//===- ThreadSafetyRanges.cpp - Integer range sets ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Integer range sets and the transfer functions on them that the
// thread safety analysis uses to track the possible return values
// of try-acquire functions.
//
//===----------------------------------------------------------------------===//

#include "ThreadSafetyInternal.h"

using namespace clang;
using namespace threadSafety;

IntDomain IntDomain::forType(QualType Ty, const ASTContext &Ctx) {
  assert(Ty->isIntegralOrEnumerationType());
  unsigned Bits = Ctx.getIntWidth(Ty);
  bool IsUnsigned = Ty->isUnsignedIntegerOrEnumerationType();
  // Keep types up to 62 bits within a single 64-bit APInt word so that
  // interval endpoints do not heap-allocate.
  unsigned W = Bits <= 62 ? 64u : std::max(Bits + 2, 66u);
  llvm::APSInt Min = llvm::APSInt::getMinValue(Bits, IsUnsigned).extend(W);
  llvm::APSInt Max = llvm::APSInt::getMaxValue(Bits, IsUnsigned).extend(W);
  Min.setIsSigned(true);
  Max.setIsSigned(true);
  return {W, std::move(Min), std::move(Max)};
}

llvm::APSInt IntDomain::toDomainInt(const llvm::APSInt &V) const {
  unsigned TempW = std::max(V.getBitWidth() + 2, BitWidth);
  llvm::APSInt Ext = V.extend(TempW);
  Ext.setIsSigned(true);
  llvm::APSInt Res = Ext.extOrTrunc(BitWidth);
  Res.setIsSigned(true);
  return Res;
}

static llvm::APSInt incAPSInt(llvm::APSInt V) {
  ++V;
  return V;
}

static llvm::APSInt decAPSInt(llvm::APSInt V) {
  --V;
  return V;
}

/// \p V as a signed integer that is wide enough to add or subtract one.
static llvm::APSInt widenAPSInt(const llvm::APSInt &V) {
  llvm::APSInt Res = V.extend(V.getBitWidth() + 2);
  Res.setIsSigned(true);
  return Res;
}

using ClosedRange = ThreadSafetyAnalyzer::IntRangeSet::Range;

static SmallVector<ClosedRange, 2> sextRanges(ArrayRef<ClosedRange> Ranges,
                                              unsigned W) {
  SmallVector<ClosedRange, 2> Ext;
  Ext.reserve(Ranges.size());
  for (const ClosedRange &R : Ranges) {
    if (R.getBitWidth() == W)
      Ext.push_back(R);
    else
      Ext.emplace_back(R.Lo.extend(W), R.Hi.extend(W));
  }
  return Ext;
}

static std::pair<SmallVector<ClosedRange, 2>, SmallVector<ClosedRange, 2>>
matchRangeWidths(ArrayRef<ClosedRange> A, ArrayRef<ClosedRange> B) {
  if (A.empty() || B.empty() ||
      A.front().getBitWidth() == B.front().getBitWidth())
    return {SmallVector<ClosedRange, 2>(A), SmallVector<ClosedRange, 2>(B)};
  unsigned W = std::max(A.front().getBitWidth(), B.front().getBitWidth());
  return {sextRanges(A, W), sextRanges(B, W)};
}

/// Append \p R to \p Out, where \p Out is sorted and its last interval starts
/// no later than \p R, merging overlapping or adjacent intervals.
static void appendOrMergeRange(SmallVectorImpl<ClosedRange> &Out,
                               const ClosedRange &R) {
  if (Out.empty() || incAPSInt(Out.back().Hi).slt(R.Lo)) {
    Out.push_back(R);
  } else if (Out.back().Hi.slt(R.Hi)) {
    Out.back().Hi = R.Hi;
  }
}

IntRangeSet IntRangeSet::full(const IntDomain &Dom) {
  return closedRange(Dom, Dom.Lo, Dom.Hi);
}

IntRangeSet IntRangeSet::closedRange(const IntDomain &Dom,
                                     const llvm::APSInt &First,
                                     const llvm::APSInt &Last) {
  if (llvm::APSInt::compareValues(First, Last) > 0 ||
      llvm::APSInt::compareValues(Last, Dom.Lo) < 0 ||
      llvm::APSInt::compareValues(First, Dom.Hi) > 0)
    return {};
  llvm::APSInt Lo = llvm::APSInt::compareValues(First, Dom.Lo) <= 0
                        ? Dom.Lo
                        : Dom.toDomainInt(First);
  llvm::APSInt Hi = llvm::APSInt::compareValues(Last, Dom.Hi) >= 0
                        ? Dom.Hi
                        : Dom.toDomainInt(Last);
  IntRangeSet S;
  S.Ranges.emplace_back(std::move(Lo), std::move(Hi));
  return S;
}

IntRangeSet IntRangeSet::single(const IntDomain &Dom, const llvm::APSInt &Val) {
  return closedRange(Dom, Val, Val);
}

IntRangeSet IntRangeSet::reproject(const IntDomain &Dom) const {
  IntRangeSet Res;
  for (const auto &[Lo, Hi] : Ranges)
    Res = Res.unionWith(closedRange(Dom, Lo, Hi));
  return Res;
}

IntRangeSet IntRangeSet::forComparison(const IntDomain &Dom,
                                       BinaryOperator::Opcode Opc,
                                       const llvm::APSInt &K) {
  switch (Opc) {
  case BO_EQ:
    return single(Dom, K);
  case BO_NE:
    return single(Dom, K).complement(Dom);
  case BO_LT:
    return closedRange(Dom, Dom.Lo, decAPSInt(widenAPSInt(K)));
  case BO_LE:
    return closedRange(Dom, Dom.Lo, K);
  case BO_GT:
    return closedRange(Dom, incAPSInt(widenAPSInt(K)), Dom.Hi);
  case BO_GE:
    return closedRange(Dom, K, Dom.Hi);
  default:
    llvm_unreachable("Unexpected comparison opcode");
  }
}

IntRangeSet IntRangeSet::boolSet(const IntDomain &Dom, bool CanBeFalse,
                                 bool CanBeTrue) {
  IntRangeSet Res;
  if (CanBeFalse)
    Res = single(Dom, llvm::APSInt::get(0));
  if (CanBeTrue)
    Res = Res.unionWith(single(Dom, llvm::APSInt::get(1)));
  return Res;
}

IntRangeSet IntRangeSet::complement(const IntDomain &Dom) const {
  IntRangeSet Mapped = reproject(Dom);
  if (Mapped.empty())
    return full(Dom);
  IntRangeSet Res;
  llvm::APSInt NextLo = Dom.Lo;
  for (const auto &[Lo, Hi] : Mapped.Ranges) {
    if (NextLo.slt(Lo))
      Res.Ranges.emplace_back(NextLo, decAPSInt(Lo));
    NextLo = incAPSInt(Hi);
  }
  if (NextLo.sle(Dom.Hi))
    Res.Ranges.emplace_back(std::move(NextLo), Dom.Hi);
  return Res;
}

IntRangeSet IntRangeSet::intersect(const IntRangeSet &Other) const {
  if (empty() || Other.empty())
    return {};
  auto [A, B] = matchRangeWidths(Ranges, Other.Ranges);
  IntRangeSet Res;
  size_t I = 0, J = 0;
  while (I < A.size() && J < B.size()) {
    const llvm::APSInt &MaxLo = A[I].Lo.sgt(B[J].Lo) ? A[I].Lo : B[J].Lo;
    const llvm::APSInt &MinHi = A[I].Hi.slt(B[J].Hi) ? A[I].Hi : B[J].Hi;
    if (MaxLo.sle(MinHi))
      Res.Ranges.emplace_back(MaxLo, MinHi);
    if (A[I].Hi.slt(B[J].Hi))
      ++I;
    else
      ++J;
  }
  return Res;
}

IntRangeSet IntRangeSet::unionWith(const IntRangeSet &Other) const {
  if (empty())
    return Other;
  if (Other.empty())
    return *this;
  auto [A, B] = matchRangeWidths(Ranges, Other.Ranges);
  IntRangeSet Res;
  Res.Ranges.reserve(A.size() + B.size());
  size_t I = 0, J = 0;
  while (I < A.size() || J < B.size()) {
    if (J == B.size() || (I < A.size() && A[I].Lo.slt(B[J].Lo)))
      appendOrMergeRange(Res.Ranges, A[I++]);
    else
      appendOrMergeRange(Res.Ranges, B[J++]);
  }
  return Res;
}

void IntRangeSet::widen(unsigned MaxIntervals) {
  assert(MaxIntervals > 0);
  if (Ranges.size() <= MaxIntervals)
    return;
  // Fill the Ranges.size() - MaxIntervals smallest gaps. The gaps are
  // computed with one extra bit such that the subtraction cannot overflow.
  unsigned NumGaps = Ranges.size() - 1;
  unsigned W = Ranges.front().getBitWidth() + 1;
  SmallVector<std::pair<llvm::APInt, unsigned>, 16> Gaps;
  Gaps.reserve(NumGaps);
  for (unsigned I = 0; I < NumGaps; ++I) {
    llvm::APInt Lo = Ranges[I + 1].Lo.sext(W);
    llvm::APInt Hi = incAPSInt(Ranges[I].Hi).sext(W);
    Gaps.emplace_back(Lo - Hi, I);
  }
  unsigned NumToFill = Ranges.size() - MaxIntervals;
  std::nth_element(
      Gaps.begin(), Gaps.begin() + (NumToFill - 1), Gaps.end(),
      [](const auto &A, const auto &B) { return A.first.slt(B.first); });
  SmallVector<bool, 16> Fill(NumGaps, false);
  for (unsigned I = 0; I < NumToFill; ++I)
    Fill[Gaps[I].second] = true;
  SmallVector<Range, 2> Res;
  for (unsigned I = 0; I < Ranges.size(); ++I) {
    if (I > 0 && Fill[I - 1])
      Res.back().Hi = Ranges[I].Hi;
    else
      Res.push_back(Ranges[I]);
  }
  Ranges = std::move(Res);
}

IntRangeSet IntRangeSet::unionAll(ArrayRef<IntRangeSet> Sets) {
  unsigned W = 0;
  size_t Total = 0;
  for (const IntRangeSet &S : Sets) {
    if (!S.empty()) {
      W = std::max(W, S.Ranges.front().getBitWidth());
      Total += S.Ranges.size();
    }
  }
  if (Total == 0)
    return {};
  SmallVector<Range, 8> All;
  All.reserve(Total);
  for (const IntRangeSet &S : Sets) {
    for (const Range &R : S.Ranges) {
      if (R.getBitWidth() == W)
        All.push_back(R);
      else
        All.emplace_back(R.Lo.extend(W), R.Hi.extend(W));
    }
  }
  llvm::sort(All,
             [](const Range &A, const Range &B) { return A.Lo.slt(B.Lo); });
  IntRangeSet Res;
  for (const Range &R : All)
    appendOrMergeRange(Res.Ranges, R);
  return Res;
}

bool IntRangeSet::subsetOf(const llvm::APSInt &First,
                           const llvm::APSInt &Last) const {
  return !Ranges.empty() &&
         llvm::APSInt::compareValues(Ranges.front().Lo, First) >= 0 &&
         llvm::APSInt::compareValues(Ranges.back().Hi, Last) <= 0;
}

bool IntRangeSet::intersects(const llvm::APSInt &First,
                             const llvm::APSInt &Last) const {
  return llvm::any_of(Ranges, [&](const Range &R) {
    return llvm::APSInt::compareValues(R.Hi, First) >= 0 &&
           llvm::APSInt::compareValues(R.Lo, Last) <= 0;
  });
}

bool IntRangeSet::subsetOfSet(const IntRangeSet &Other) const {
  if (empty())
    return true;
  if (Other.empty())
    return false;
  return intersect(Other).Ranges == Ranges;
}

bool IntRangeSet::intersectsSet(const IntRangeSet &Other) const {
  return !intersect(Other).empty();
}

bool IntRangeSet::isSingleValue(llvm::APSInt &Val) const {
  if (Ranges.size() != 1 || Ranges[0].Lo != Ranges[0].Hi)
    return false;
  Val = Ranges[0].Lo;
  return true;
}

/// Whether \p CE is a same-width non-boolean integral or pointer-integer cast
/// that induces a bijection between the bit patterns of its source and
/// destination types, e.g. (intptr_t)ptr or C++ promotion of an unsigned
/// unscoped enum to int.
bool threadSafety::isBijectiveReinterpretCast(const CastExpr *CE,
                                              const ASTContext &Ctx) {
  QualType SubTy = CE->getSubExpr()->getType();
  QualType DstTy = CE->getType();
  if (SubTy.isNull() || DstTy.isNull() || SubTy->isDependentType() ||
      DstTy->isDependentType() || SubTy->isBooleanType() ||
      DstTy->isBooleanType())
    return false;
  if (const auto *ED = SubTy->getAsEnumDecl(); ED && !ED->isComplete())
    return false;
  if (const auto *ED = DstTy->getAsEnumDecl(); ED && !ED->isComplete())
    return false;
  switch (CE->getCastKind()) {
  case CK_IntegralCast:
    return SubTy->isIntegralOrEnumerationType() &&
           DstTy->isIntegralOrEnumerationType() &&
           Ctx.getIntWidth(SubTy) == Ctx.getIntWidth(DstTy);
  case CK_PointerToIntegral:
    return SubTy->isAnyPointerType() && DstTy->isIntegralOrEnumerationType() &&
           Ctx.getIntWidth(DstTy) == Ctx.getIntWidth(Ctx.getUIntPtrType());
  case CK_IntegralToPointer:
    return DstTy->isAnyPointerType() && SubTy->isIntegralOrEnumerationType() &&
           Ctx.getIntWidth(SubTy) == Ctx.getIntWidth(Ctx.getUIntPtrType());
  default:
    return false;
  }
}

ThreadSafetyAnalyzer::IntRangeSet
threadSafety::mapRangeBackwardThroughBijectiveCasts(
    ThreadSafetyAnalyzer::IntRangeSet S, ArrayRef<const CastExpr *> Casts,
    const ThreadSafetyAnalyzer::IntDomain &TargetDom, const ASTContext &Ctx) {
  for (const CastExpr *CE : Casts) {
    QualType DstScalarTy = CE->getType()->isAnyPointerType()
                               ? Ctx.getUIntPtrType()
                               : CE->getType();
    QualType SrcScalarTy = CE->getSubExpr()->getType()->isAnyPointerType()
                               ? Ctx.getUIntPtrType()
                               : CE->getSubExpr()->getType();
    auto DstDom = ThreadSafetyAnalyzer::IntDomain::forType(DstScalarTy, Ctx);
    S = castIntegralRangeSet(reprojectRangeSet(S, DstDom), SrcScalarTy, Ctx);
  }
  return reprojectRangeSet(S, TargetDom);
}

std::optional<ThreadSafetyAnalyzer::IntDomain>
threadSafety::getScalarDomainForType(QualType Ty, const ASTContext &Ctx) {
  using IntDomain = ThreadSafetyAnalyzer::IntDomain;
  if (Ty.isNull() || Ty->isDependentType())
    return std::nullopt;
  if (const auto *ED = Ty->getAsEnumDecl(); ED && !ED->isComplete())
    return std::nullopt;
  if (Ty->isIntegralOrEnumerationType())
    return IntDomain::forType(Ty, Ctx);
  if (Ty->isAnyPointerType() || Ty->isNullPtrType())
    return IntDomain::forType(Ctx.getUIntPtrType(), Ctx);
  if (Ty->isMemberPointerType())
    return IntDomain::forType(Ctx.BoolTy, Ctx);
  return std::nullopt;
}

std::optional<ThreadSafetyAnalyzer::IntDomain>
ThreadSafetyAnalyzer::getScalarDomain(QualType Ty) const {
  return getScalarDomainForType(Ty, *ASTCtx);
}

ThreadSafetyAnalyzer::IntRangeSet
threadSafety::reprojectRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                const ThreadSafetyAnalyzer::IntDomain &Dom) {
  return Src.reproject(Dom);
}

static ThreadSafetyAnalyzer::IntRangeSet
booleanizeRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                   const ThreadSafetyAnalyzer::IntDomain &DstDom) {
  return ThreadSafetyAnalyzer::IntRangeSet::boolSet(DstDom, Src.mayBeZero(),
                                                    Src.mayBeNonZero());
}

/// \p V converted to \p Ty, i.e. truncated or extended to the width and
/// signedness of \p Ty, or compared with zero if \p Ty is bool.
llvm::APSInt threadSafety::truncToType(const llvm::APSInt &V, QualType Ty,
                                       const ASTContext &Ctx) {
  // Converting a value to bool yields whether it is non-zero.
  if (Ty->isBooleanType())
    return llvm::APSInt(llvm::APInt(Ctx.getIntWidth(Ty), !V.isZero()),
                        /*isUnsigned=*/true);
  llvm::APSInt Res = V.extOrTrunc(Ctx.getIntWidth(Ty));
  Res.setIsUnsigned(Ty->isUnsignedIntegerOrEnumerationType());
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
threadSafety::castIntegralRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                   QualType DstTy, const ASTContext &Ctx) {
  if (Src.empty())
    return {};
  auto DstDom = ThreadSafetyAnalyzer::IntDomain::forType(DstTy, Ctx);
  // Boolean conversion is != 0.
  if (DstTy->isBooleanType())
    return booleanizeRangeSet(Src, DstDom);

  unsigned DstBits = Ctx.getIntWidth(DstTy);

  // The intervals of Src may be wider than the destination domain, e.g. for
  // __int128 sources. Use a width that can represent all values involved.
  unsigned WideW = std::max(DstDom.BitWidth + 2, DstBits + 3);
  for (const ClosedRange &CR : Src.ranges())
    WideW = std::max(WideW, CR.getBitWidth() + 2);
  llvm::APSInt TwoPowW(llvm::APInt::getOneBitSet(WideW, DstBits),
                       /*isUnsigned=*/false);

  ThreadSafetyAnalyzer::IntRangeSet Res;
  for (const auto &[Lo, Hi] : Src.ranges()) {
    if (llvm::APSInt::compareValues(Lo, DstDom.Lo) >= 0 &&
        llvm::APSInt::compareValues(Hi, DstDom.Hi) <= 0) {
      Res = Res.unionWith(
          ThreadSafetyAnalyzer::IntRangeSet::closedRange(DstDom, Lo, Hi));
      continue;
    }
    llvm::APSInt LoW = Lo.extend(WideW);
    llvm::APSInt HiW = Hi.extend(WideW);
    LoW.setIsUnsigned(false);
    HiW.setIsUnsigned(false);
    if (HiW - LoW >= TwoPowW)
      return ThreadSafetyAnalyzer::IntRangeSet::full(DstDom);
    llvm::APSInt MappedLo = truncToType(Lo, DstTy, Ctx);
    llvm::APSInt MappedHi = truncToType(Hi, DstTy, Ctx);
    if (llvm::APSInt::compareValues(MappedLo, MappedHi) <= 0) {
      Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::closedRange(
          DstDom, MappedLo, MappedHi));
    } else {
      Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::closedRange(
          DstDom, DstDom.Lo, MappedHi));
      Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::closedRange(
          DstDom, MappedLo, DstDom.Hi));
    }
  }
  return Res;
}
