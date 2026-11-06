//===- ThreadSafetyRanges.h -------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Sets of integer ranges and expression helpers that the thread safety
// analysis uses to model the return values of try_acquire functions. This
// header is private to the analysis. It is only included by the unit tests
// outside clang/lib/Analysis.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYRANGES_H
#define LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYRANGES_H

#include "clang/AST/OperationKinds.h"
#include "clang/AST/Type.h"
#include "clang/Basic/LLVM.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

namespace clang {

class ASTContext;
class CastExpr;
class Expr;
class Stmt;
class StmtExpr;
class ValueDecl;

namespace threadSafety {

struct IntDomain {
  unsigned BitWidth = 0;
  llvm::APSInt Lo;
  llvm::APSInt Hi;

  IntDomain() = default;
  IntDomain(unsigned BitWidth, llvm::APSInt Lo, llvm::APSInt Hi)
      : BitWidth(BitWidth), Lo(std::move(Lo)), Hi(std::move(Hi)) {}

  static IntDomain forType(QualType Ty, const ASTContext &Ctx);
  llvm::APSInt toDomainInt(const llvm::APSInt &V) const;

  bool operator==(const IntDomain &Other) const {
    return BitWidth == Other.BitWidth &&
           llvm::APSInt::compareValues(Lo, Other.Lo) == 0 &&
           llvm::APSInt::compareValues(Hi, Other.Hi) == 0;
  }
};

class IntRangeSet {
public:
  /// A closed signed interval [Lo, Hi] with Lo <= Hi.
  struct Range {
    llvm::APSInt Lo;
    llvm::APSInt Hi;

    Range(llvm::APSInt Lo, llvm::APSInt Hi)
        : Lo(std::move(Lo)), Hi(std::move(Hi)) {}

    unsigned getBitWidth() const { return Lo.getBitWidth(); }

    bool operator==(const Range &Other) const {
      return llvm::APSInt::compareValues(Lo, Other.Lo) == 0 &&
             llvm::APSInt::compareValues(Hi, Other.Hi) == 0;
    }
    bool operator!=(const Range &Other) const { return !(*this == Other); }
  };

private:
  SmallVector<Range, 2> Ranges;

public:
  IntRangeSet() = default;

  bool empty() const { return Ranges.empty(); }

  static IntRangeSet full(const IntDomain &Dom);
  static IntRangeSet closedRange(const IntDomain &Dom,
                                 const llvm::APSInt &First,
                                 const llvm::APSInt &Last);
  static IntRangeSet single(const IntDomain &Dom, const llvm::APSInt &Val);
  static IntRangeSet forComparison(const IntDomain &Dom, BinaryOperatorKind Opc,
                                   const llvm::APSInt &K);
  /// The values in \p Dom that are true (non-zero) if \p Truth is set or
  /// false (zero) otherwise.
  static IntRangeSet truthSet(const IntDomain &Dom, bool Truth) {
    return forComparison(Dom, Truth ? BO_NE : BO_EQ, llvm::APSInt::get(0));
  }
  /// The subset of {0, 1} in \p Dom with 0 if \p CanBeFalse and 1 if
  /// \p CanBeTrue.
  static IntRangeSet boolSet(const IntDomain &Dom, bool CanBeFalse,
                             bool CanBeTrue);

  /// Union of all \p Sets in O(N log N) time, where N is the total number
  /// of intervals. All sets must belong to the same domain.
  static IntRangeSet unionAll(ArrayRef<IntRangeSet> Sets);

  IntRangeSet complement(const IntDomain &Dom) const;
  /// The values of this set that are in \p Dom, represented in \p Dom.
  IntRangeSet reproject(const IntDomain &Dom) const;
  IntRangeSet intersect(const IntRangeSet &Other) const;
  IntRangeSet unionWith(const IntRangeSet &Other) const;

  bool subsetOf(const llvm::APSInt &First, const llvm::APSInt &Last) const;
  bool intersects(const llvm::APSInt &First, const llvm::APSInt &Last) const;
  bool subsetOfSet(const IntRangeSet &Other) const;
  bool intersectsSet(const IntRangeSet &Other) const;
  bool isSingleValue(llvm::APSInt &Val) const;
  bool mayBeZero() const {
    llvm::APSInt Zero = llvm::APSInt::get(0);
    return intersects(Zero, Zero);
  }
  bool mayBeNonZero() const {
    llvm::APSInt Zero = llvm::APSInt::get(0);
    return !empty() && !subsetOf(Zero, Zero);
  }
  /// Over-approximate this set by at most \p MaxIntervals intervals by
  /// filling the smallest gaps between intervals.
  void widen(unsigned MaxIntervals);
  ArrayRef<Range> ranges() const { return Ranges; }
};

// Defined in ThreadSafetyRanges.cpp.
bool isBijectiveReinterpretCast(const CastExpr *CE, const ASTContext &Ctx);
IntRangeSet mapRangeBackwardThroughBijectiveCasts(
    IntRangeSet S, ArrayRef<const CastExpr *> Casts, const IntDomain &TargetDom,
    const ASTContext &Ctx);
std::optional<IntDomain> getScalarDomainForType(QualType Ty,
                                                const ASTContext &Ctx);
IntRangeSet reprojectRangeSet(const IntRangeSet &Src, const IntDomain &Dom);
llvm::APSInt truncToType(const llvm::APSInt &V, QualType Ty,
                         const ASTContext &Ctx);
IntRangeSet castIntegralRangeSet(const IntRangeSet &Src, QualType DstTy,
                                 const ASTContext &Ctx);

// Defined in ThreadSafetyValueEval.cpp.
const Expr *stripNoOpExprWrappers(const Expr *E);
void scanTrylockVars(const Stmt *Root, const ASTContext &Ctx,
                     llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
                     llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars);
inline void
scanModifiedVars(const Stmt *Root, const ASTContext &Ctx,
                 llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars) {
  llvm::SmallPtrSet<const ValueDecl *, 4> UnusedEscaped;
  scanTrylockVars(Root, Ctx, UnusedEscaped, ModifiedVars);
}

} // namespace threadSafety
} // namespace clang

#endif // LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYRANGES_H
