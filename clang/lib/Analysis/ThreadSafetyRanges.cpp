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
castDerivedToBaseRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                          const ThreadSafetyAnalyzer::IntDomain &Dom) {
  using IntRangeSet = ThreadSafetyAnalyzer::IntRangeSet;
  // Adjusting a non-null pointer by a base-class offset yields a non-null
  // pointer. A null pointer stays null.
  IntRangeSet Mapped = reprojectRangeSet(Src, Dom);
  IntRangeSet Res;
  if (Mapped.mayBeZero())
    Res = IntRangeSet::truthSet(Dom, false);
  if (Mapped.mayBeNonZero())
    Res = Res.unionWith(IntRangeSet::truthSet(Dom, true));
  return Res;
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

/// The value of \p LV \p Opc \p RV converted to \p ResTy if \p Opc is an
/// arithmetic, shift or bitwise operator.
std::optional<llvm::APSInt>
threadSafety::foldIntBinOp(BinaryOperator::Opcode Opc, llvm::APSInt LV,
                           llvm::APSInt RV, QualType ResTy,
                           const ASTContext &Ctx) {
  if (Opc == BO_Shl || Opc == BO_Shr) {
    LV = truncToType(LV, ResTy, Ctx);
    if (RV.isNegative() || RV.ugt(LV.getBitWidth() - 1))
      return std::nullopt;
    unsigned Shift = static_cast<unsigned>(RV.getZExtValue());
    return truncToType(Opc == BO_Shl ? (LV << Shift) : (LV >> Shift), ResTy,
                       Ctx);
  }
  if (Opc == BO_Div || Opc == BO_Rem) {
    LV = truncToType(LV, ResTy, Ctx);
    RV = truncToType(RV, ResTy, Ctx);
    if (RV.isZero() ||
        (LV.isSigned() && LV.isMinSignedValue() && RV.isAllOnes()))
      return std::nullopt;
    return truncToType(Opc == BO_Div ? (LV / RV) : (LV % RV), ResTy, Ctx);
  }
  // The operands of compound assignments may have different widths and
  // signedness.
  unsigned W =
      std::max({LV.getBitWidth(), RV.getBitWidth(), Ctx.getIntWidth(ResTy)}) +
      2;
  LV = LV.extend(W);
  RV = RV.extend(W);
  LV.setIsSigned(true);
  RV.setIsSigned(true);
  switch (Opc) {
  case BO_Add:
    return truncToType(LV + RV, ResTy, Ctx);
  case BO_Sub:
    return truncToType(LV - RV, ResTy, Ctx);
  case BO_Mul:
    return truncToType(LV * RV, ResTy, Ctx);
  case BO_And:
    return truncToType(LV & RV, ResTy, Ctx);
  case BO_Or:
    return truncToType(LV | RV, ResTy, Ctx);
  case BO_Xor:
    return truncToType(LV ^ RV, ResTy, Ctx);
  default:
    return std::nullopt;
  }
}

/// Truncate the range \p Src to a bit-field of width \p BitWidth and type
/// \p FieldTy, projected into \p DstDom.
ThreadSafetyAnalyzer::IntRangeSet
threadSafety::truncateToBitField(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                 unsigned BitWidth, QualType FieldTy,
                                 const ThreadSafetyAnalyzer::IntDomain &DstDom,
                                 const ASTContext &Ctx) {
  using IntRangeSet = ThreadSafetyAnalyzer::IntRangeSet;
  if (Src.empty() || BitWidth == 0)
    return {};
  if (FieldTy->isBooleanType())
    return booleanizeRangeSet(Src, DstDom);
  BitWidth = std::min(BitWidth, Ctx.getIntWidth(FieldTy));
  bool IsUnsigned = FieldTy->isUnsignedIntegerOrEnumerationType();
  unsigned W = std::max({DstDom.BitWidth + 2, BitWidth + 3, 64u});
  for (const ClosedRange &CR : Src.ranges())
    W = std::max(W, CR.getBitWidth() + 2);
  llvm::APSInt BFMin(
      IsUnsigned ? llvm::APInt::getZero(DstDom.BitWidth)
                 : llvm::APInt::getSignMask(BitWidth).sext(DstDom.BitWidth),
      /*isUnsigned=*/false);
  llvm::APSInt BFMax(
      IsUnsigned
          ? llvm::APInt::getLowBitsSet(DstDom.BitWidth, BitWidth)
          : llvm::APInt::getSignedMaxValue(BitWidth).sext(DstDom.BitWidth),
      /*isUnsigned=*/false);
  llvm::APSInt TwoPowW(llvm::APInt::getOneBitSet(W, BitWidth),
                       /*isUnsigned=*/false);
  auto TruncPoint = [&](const llvm::APSInt &V) {
    llvm::APInt Trunc = V.extOrTrunc(BitWidth);
    return llvm::APSInt(IsUnsigned ? Trunc.zext(DstDom.BitWidth)
                                   : Trunc.sext(DstDom.BitWidth),
                        /*isUnsigned=*/false);
  };
  IntRangeSet Res;
  for (const auto &[Lo, Hi] : Src.ranges()) {
    if (llvm::APSInt::compareValues(Lo, BFMin) >= 0 &&
        llvm::APSInt::compareValues(Hi, BFMax) <= 0) {
      Res = Res.unionWith(IntRangeSet::closedRange(DstDom, Lo, Hi));
      continue;
    }
    llvm::APSInt LoW = Lo.extend(W), HiW = Hi.extend(W);
    LoW.setIsUnsigned(false);
    HiW.setIsUnsigned(false);
    if (HiW - LoW >= TwoPowW)
      return IntRangeSet::closedRange(DstDom, BFMin, BFMax);
    llvm::APSInt MappedLo = TruncPoint(Lo), MappedHi = TruncPoint(Hi);
    if (llvm::APSInt::compareValues(MappedLo, MappedHi) <= 0) {
      Res = Res.unionWith(IntRangeSet::closedRange(DstDom, MappedLo, MappedHi));
    } else {
      Res = Res.unionWith(IntRangeSet::closedRange(DstDom, BFMin, MappedHi));
      Res = Res.unionWith(IntRangeSet::closedRange(DstDom, MappedLo, BFMax));
    }
  }
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
threadSafety::castIntegralRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                   QualType DstTy, const ASTContext &Ctx) {
  return truncateToBitField(Src, Ctx.getIntWidth(DstTy), DstTy,
                            IntDomain::forType(DstTy, Ctx), Ctx);
}

static IntRangeSet affineTransformRangeSet(const IntRangeSet &Src,
                                           bool NegateSrc, llvm::APSInt K,
                                           bool SubtractK, QualType ResTy,
                                           const ASTContext &Ctx) {
  if (Src.empty())
    return {};
  K = truncToType(K, ResTy, Ctx);
  unsigned W = std::max({Ctx.getIntWidth(ResTy),
                         Src.ranges().front().getBitWidth(), 62u}) +
               3;
  llvm::APSInt KW = K.extend(W);
  KW.setIsUnsigned(false);
  if (SubtractK)
    KW = -KW;
  IntDomain WideDom{W,
                    llvm::APSInt(llvm::APInt::getSignedMinValue(W - 1).sext(W),
                                 /*isUnsigned=*/false),
                    llvm::APSInt(llvm::APInt::getSignedMaxValue(W - 1).sext(W),
                                 /*isUnsigned=*/false)};
  IntRangeSet Shifted;
  for (const auto &[Lo, Hi] : Src.ranges()) {
    llvm::APSInt LoW = Lo.extend(W), HiW = Hi.extend(W);
    LoW.setIsUnsigned(false);
    HiW.setIsUnsigned(false);
    llvm::APSInt NewLo = (NegateSrc ? -HiW : LoW) + KW;
    llvm::APSInt NewHi = (NegateSrc ? -LoW : HiW) + KW;
    Shifted =
        Shifted.unionWith(IntRangeSet::closedRange(WideDom, NewLo, NewHi));
  }
  return castIntegralRangeSet(Shifted, ResTy, Ctx);
}

ThreadSafetyAnalyzer::IntRangeSet
threadSafety::negateRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                             QualType ResTy, const ASTContext &Ctx) {
  return affineTransformRangeSet(Src, /*NegateSrc=*/true, llvm::APSInt::get(0),
                                 /*SubtractK=*/false, ResTy, Ctx);
}

/// The values of \p Src + \p K (or \p Src - \p K if \p Subtract is true) in
/// the integral type \p ResTy.
ThreadSafetyAnalyzer::IntRangeSet
threadSafety::addConstToRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                 llvm::APSInt K, bool Subtract, QualType ResTy,
                                 const ASTContext &Ctx) {
  return affineTransformRangeSet(Src, /*NegateSrc=*/false, std::move(K),
                                 Subtract, ResTy, Ctx);
}

/// The values of \p K - \p Src in the integral type \p ResTy.
ThreadSafetyAnalyzer::IntRangeSet
threadSafety::subRangeSetFromConst(llvm::APSInt K,
                                   const ThreadSafetyAnalyzer::IntRangeSet &Src,
                                   QualType ResTy, const ASTContext &Ctx) {
  return affineTransformRangeSet(Src, /*NegateSrc=*/true, std::move(K),
                                 /*SubtractK=*/false, ResTy, Ctx);
}

/// Whether applyCast() can compute the values of the cast \p CE from the
/// values of its operand.
bool threadSafety::isRangeMappableCast(const CastExpr *CE) {
  QualType SubTy = CE->getSubExpr()->getType();
  QualType DstTy = CE->getType();
  switch (CE->getCastKind()) {
  case CK_LValueToRValue:
  case CK_NoOp:
  case CK_IntegralToBoolean:
  case CK_PointerToBoolean:
  case CK_MemberPointerToBoolean:
  case CK_BooleanToSignedIntegral:
    return true;
  case CK_UserDefinedConversion:
    return isConversionFunctionCast(CE);
  case CK_BitCast:
  case CK_DerivedToBase:
  case CK_UncheckedDerivedToBase:
    return DstTy->isAnyPointerType() && SubTy->isAnyPointerType();
  case CK_PointerToIntegral:
    return SubTy->isAnyPointerType() && DstTy->isIntegralOrEnumerationType();
  case CK_IntegralToPointer:
    return DstTy->isAnyPointerType() && SubTy->isIntegralOrEnumerationType();
  case CK_IntegralCast:
    return SubTy->isIntegralOrEnumerationType() &&
           DstTy->isIntegralOrEnumerationType();
  default:
    return false;
  }
}

/// The values in \p Dom, the domain of the type of the cast \p CE, that \p CE
/// may have if its operand has the values \p Sub. \p CE must satisfy
/// isRangeMappableCast().
ThreadSafetyAnalyzer::IntRangeSet threadSafety::applyCast(
    const CastExpr *CE, const ThreadSafetyAnalyzer::IntRangeSet &Sub,
    const ThreadSafetyAnalyzer::IntDomain &Dom, const ASTContext &Ctx) {
  switch (CE->getCastKind()) {
  case CK_DerivedToBase:
  case CK_UncheckedDerivedToBase:
    return castDerivedToBaseRangeSet(Sub, Dom);
  case CK_PointerToIntegral:
  case CK_IntegralCast:
    return castIntegralRangeSet(Sub, CE->getType(), Ctx);
  case CK_IntegralToPointer:
    return castIntegralRangeSet(Sub, Ctx.getUIntPtrType(), Ctx);
  case CK_IntegralToBoolean:
  case CK_PointerToBoolean:
  case CK_MemberPointerToBoolean:
    return booleanizeRangeSet(Sub, Dom);
  case CK_BooleanToSignedIntegral: {
    ThreadSafetyAnalyzer::IntRangeSet Res;
    if (Sub.mayBeZero())
      Res =
          ThreadSafetyAnalyzer::IntRangeSet::single(Dom, llvm::APSInt::get(0));
    if (Sub.mayBeNonZero())
      Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
          Dom, llvm::APSInt::get(-1)));
    return Res;
  }
  default:
    return reprojectRangeSet(Sub, Dom);
  }
}

/// Whether \p L \p Opc \p R holds for some values of the non-empty sets \p L
/// and \p R.
static bool mayHold(BinaryOperator::Opcode Opc,
                    const ThreadSafetyAnalyzer::IntRangeSet &L,
                    const ThreadSafetyAnalyzer::IntRangeSet &R) {
  switch (Opc) {
  case BO_EQ:
    return L.intersectsSet(R);
  case BO_NE: {
    llvm::APSInt LV, RV;
    return !(L.isSingleValue(LV) && R.isSingleValue(RV) &&
             llvm::APSInt::compareValues(LV, RV) == 0);
  }
  case BO_LT:
    return llvm::APSInt::compareValues(L.ranges().front().Lo,
                                       R.ranges().back().Hi) < 0;
  case BO_LE:
    return llvm::APSInt::compareValues(L.ranges().front().Lo,
                                       R.ranges().back().Hi) <= 0;
  case BO_GT:
  case BO_GE:
    return mayHold(BinaryOperator::reverseComparisonOp(Opc), R, L);
  default:
    llvm_unreachable("Unexpected comparison opcode");
  }
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet> threadSafety::compareRangeSets(
    BinaryOperator::Opcode Opc, const ThreadSafetyAnalyzer::IntRangeSet &L,
    const ThreadSafetyAnalyzer::IntRangeSet &R,
    const ThreadSafetyAnalyzer::IntDomain &ResDom, bool IsMemberPtrComparison) {
  using IntRangeSet = ThreadSafetyAnalyzer::IntRangeSet;
  if (L.empty() || R.empty())
    return IntRangeSet{};

  if (IsMemberPtrComparison) {
    if (!BinaryOperator::isEqualityOp(Opc))
      return std::nullopt;
    // Only null-ness is tracked for member pointers. Two non-null member
    // pointers may or may not be equal.
    bool LNull = L.mayBeZero(), LNonNull = L.mayBeNonZero();
    bool RNull = R.mayBeZero(), RNonNull = R.mayBeNonZero();
    bool CanEq = (LNull && RNull) || (LNonNull && RNonNull);
    bool CanNe =
        (LNull && RNonNull) || (LNonNull && RNull) || (LNonNull && RNonNull);
    return Opc == BO_EQ ? IntRangeSet::boolSet(ResDom, CanNe, CanEq)
                        : IntRangeSet::boolSet(ResDom, CanEq, CanNe);
  }
  if (!BinaryOperator::isRelationalOp(Opc) &&
      !BinaryOperator::isEqualityOp(Opc))
    return std::nullopt;
  return IntRangeSet::boolSet(
      ResDom, mayHold(BinaryOperator::negateComparisonOp(Opc), L, R),
      mayHold(Opc, L, R));
}
