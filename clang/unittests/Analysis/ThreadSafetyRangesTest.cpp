//===- unittests/Analysis/ThreadSafetyRangesTest.cpp ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Unit tests for the integer range sets and the transfer functions that the
// thread safety analysis uses to track the return values of try-acquire
// functions.
//
//===----------------------------------------------------------------------===//

#include "../../lib/Analysis/ThreadSafetyRanges.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

using namespace clang;
using namespace threadSafety;

namespace {

using Intervals = std::vector<std::pair<int64_t, int64_t>>;
using ::testing::ElementsAre;
using ::testing::IsEmpty;
using ::testing::Pair;

class ThreadSafetyRangesTest : public ::testing::Test {
protected:
  void SetUp() override {
    AST = tooling::buildASTFromCode("");
    ASSERT_TRUE(AST);
  }

  ASTContext &ctx() { return AST->getASTContext(); }
  IntDomain dom(QualType Ty) { return IntDomain::forType(Ty, ctx()); }

  static llvm::APSInt val(int64_t V) { return llvm::APSInt::get(V); }

  /// The closed intervals of \p S.
  static Intervals intervals(const IntRangeSet &S) {
    Intervals Res;
    for (const auto &[Lo, Hi] : S.ranges())
      Res.emplace_back(Lo.getSExtValue(), Hi.getSExtValue());
    return Res;
  }

  IntRangeSet range(QualType Ty, int64_t Lo, int64_t Hi) {
    return IntRangeSet::closedRange(dom(Ty), val(Lo), val(Hi));
  }

  std::unique_ptr<ASTUnit> AST;
};

TEST_F(ThreadSafetyRangesTest, DomainForType) {
  IntDomain Int = dom(ctx().IntTy);
  EXPECT_EQ(Int.Lo.getSExtValue(), INT32_MIN);
  EXPECT_EQ(Int.Hi.getSExtValue(), INT32_MAX);
  IntDomain UChar = dom(ctx().UnsignedCharTy);
  EXPECT_EQ(UChar.Lo.getSExtValue(), 0);
  EXPECT_EQ(UChar.Hi.getSExtValue(), 255);
  // Values of a 64-bit unsigned type need more than 64 bits.
  EXPECT_GT(dom(ctx().UnsignedLongLongTy).BitWidth, 64u);
}

TEST_F(ThreadSafetyRangesTest, Construction) {
  QualType Int = ctx().IntTy;
  EXPECT_THAT(intervals(range(Int, 3, 7)), ElementsAre(Pair(3, 7)));
  EXPECT_THAT(intervals(IntRangeSet::single(dom(Int), val(-4))),
              ElementsAre(Pair(-4, -4)));
  EXPECT_THAT(intervals(IntRangeSet::full(dom(Int))),
              ElementsAre(Pair(INT32_MIN, INT32_MAX)));
  // Empty ranges and ranges outside the domain are empty.
  EXPECT_TRUE(range(Int, 7, 3).empty());
  EXPECT_TRUE(range(ctx().UnsignedCharTy, 256, 300).empty());
  // Ranges are clamped to the domain.
  EXPECT_THAT(intervals(range(ctx().UnsignedCharTy, -5, 300)),
              ElementsAre(Pair(0, 255)));
}

TEST_F(ThreadSafetyRangesTest, ForComparison) {
  IntDomain D = dom(ctx().SignedCharTy);
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_EQ, val(5))),
              ElementsAre(Pair(5, 5)));
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_NE, val(5))),
              ElementsAre(Pair(-128, 4), Pair(6, 127)));
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_LT, val(0))),
              ElementsAre(Pair(-128, -1)));
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_LE, val(0))),
              ElementsAre(Pair(-128, 0)));
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_GT, val(0))),
              ElementsAre(Pair(1, 127)));
  EXPECT_THAT(intervals(IntRangeSet::forComparison(D, BO_GE, val(0))),
              ElementsAre(Pair(0, 127)));
  // A comparison that no value satisfies.
  EXPECT_TRUE(IntRangeSet::forComparison(D, BO_LT, val(-128)).empty());
  EXPECT_THAT(intervals(IntRangeSet::truthSet(D, true)),
              ElementsAre(Pair(-128, -1), Pair(1, 127)));
  EXPECT_THAT(intervals(IntRangeSet::boolSet(D, true, true)),
              ElementsAre(Pair(0, 1)));
  EXPECT_THAT(intervals(IntRangeSet::boolSet(D, false, true)),
              ElementsAre(Pair(1, 1)));
}

TEST_F(ThreadSafetyRangesTest, SetOperations) {
  QualType Int = ctx().IntTy;
  IntRangeSet A = range(Int, 0, 10);
  IntRangeSet B = range(Int, 5, 20);
  IntRangeSet C = range(Int, 30, 40);
  EXPECT_THAT(intervals(A.intersect(B)), ElementsAre(Pair(5, 10)));
  EXPECT_TRUE(A.intersect(C).empty());
  EXPECT_THAT(intervals(A.unionWith(B)), ElementsAre(Pair(0, 20)));
  EXPECT_THAT(intervals(A.unionWith(C)),
              ElementsAre(Pair(0, 10), Pair(30, 40)));
  // Adjacent intervals are merged.
  EXPECT_THAT(intervals(A.unionWith(range(Int, 11, 12))),
              ElementsAre(Pair(0, 12)));
  EXPECT_THAT(intervals(IntRangeSet::unionAll({C, A, B})),
              ElementsAre(Pair(0, 20), Pair(30, 40)));
  EXPECT_THAT(intervals(range(ctx().UnsignedCharTy, 1, 254)
                            .complement(dom(ctx().UnsignedCharTy))),
              ElementsAre(Pair(0, 0), Pair(255, 255)));
  EXPECT_THAT(intervals(IntRangeSet().complement(dom(ctx().BoolTy))),
              ElementsAre(Pair(0, 1)));
}

TEST_F(ThreadSafetyRangesTest, Predicates) {
  QualType Int = ctx().IntTy;
  IntRangeSet A = range(Int, 0, 10).unionWith(range(Int, 20, 30));
  EXPECT_TRUE(A.subsetOf(val(0), val(30)));
  EXPECT_FALSE(A.subsetOf(val(1), val(30)));
  EXPECT_TRUE(A.intersects(val(25), val(100)));
  EXPECT_FALSE(A.intersects(val(11), val(19)));
  EXPECT_TRUE(range(Int, 2, 3).subsetOfSet(A));
  EXPECT_FALSE(range(Int, 9, 21).subsetOfSet(A));
  EXPECT_TRUE(IntRangeSet().subsetOfSet(A));
  EXPECT_FALSE(A.subsetOfSet(IntRangeSet()));
  EXPECT_TRUE(range(Int, 9, 21).intersectsSet(A));
  EXPECT_FALSE(range(Int, 11, 19).intersectsSet(A));
  EXPECT_TRUE(A.mayBeZero());
  EXPECT_TRUE(A.mayBeNonZero());
  EXPECT_FALSE(range(Int, 1, 5).mayBeZero());
  EXPECT_FALSE(range(Int, 0, 0).mayBeNonZero());

  llvm::APSInt V;
  EXPECT_TRUE(range(Int, 7, 7).isSingleValue(V));
  EXPECT_EQ(V.getSExtValue(), 7);
  EXPECT_FALSE(range(Int, 7, 8).isSingleValue(V));
  EXPECT_FALSE(A.isSingleValue(V));
}

TEST_F(ThreadSafetyRangesTest, Reproject) {
  // Values that are not in the new domain are dropped.
  IntRangeSet S = range(ctx().IntTy, -10, 300);
  EXPECT_THAT(intervals(reprojectRangeSet(S, dom(ctx().UnsignedCharTy))),
              ElementsAre(Pair(0, 255)));
  EXPECT_THAT(intervals(reprojectRangeSet(S, dom(ctx().SignedCharTy))),
              ElementsAre(Pair(-10, 127)));
}

TEST_F(ThreadSafetyRangesTest, Widen) {
  QualType Int = ctx().IntTy;
  IntRangeSet S = range(Int, 0, 0)
                      .unionWith(range(Int, 2, 2))
                      .unionWith(range(Int, 10, 10))
                      .unionWith(range(Int, 100, 100));
  S.widen(4);
  EXPECT_THAT(intervals(S), ElementsAre(Pair(0, 0), Pair(2, 2), Pair(10, 10),
                                        Pair(100, 100)));
  // The smallest gaps are filled first.
  S.widen(2);
  EXPECT_THAT(intervals(S), ElementsAre(Pair(0, 10), Pair(100, 100)));
  S.widen(1);
  EXPECT_THAT(intervals(S), ElementsAre(Pair(0, 100)));
}

TEST_F(ThreadSafetyRangesTest, CastIntegral) {
  QualType Int = ctx().IntTy;
  QualType UChar = ctx().UnsignedCharTy;
  QualType SChar = ctx().SignedCharTy;
  // Values that fit are preserved.
  EXPECT_THAT(intervals(castIntegralRangeSet(range(Int, 1, 9), UChar, ctx())),
              ElementsAre(Pair(1, 9)));
  // Negative values wrap around in an unsigned type.
  EXPECT_THAT(intervals(castIntegralRangeSet(range(Int, -2, 1), UChar, ctx())),
              ElementsAre(Pair(0, 1), Pair(254, 255)));
  // Large unsigned values wrap around in a signed type.
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(UChar, 120, 130), SChar, ctx())),
      ElementsAre(Pair(-128, -126), Pair(120, 127)));
  // Spans smaller than 2^W that cross a modulo-2^W boundary map to at most two
  // intervals regardless of whether the span exceeds 16.
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, 255, 257), UChar, ctx())),
      ElementsAre(Pair(0, 1), Pair(255, 255)));
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, 240, 270), UChar, ctx())),
      ElementsAre(Pair(0, 14), Pair(240, 255)));
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, 300, 330), UChar, ctx())),
      ElementsAre(Pair(44, 74)));
  // Large spans that do not fit cover the whole destination domain.
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, 0, 1000), UChar, ctx())),
      ElementsAre(Pair(0, 255)));
  // Conversion to bool compares with zero.
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, 1, 5), ctx().BoolTy, ctx())),
      ElementsAre(Pair(1, 1)));
  EXPECT_THAT(
      intervals(castIntegralRangeSet(range(Int, -1, 1), ctx().BoolTy, ctx())),
      ElementsAre(Pair(0, 1)));
  EXPECT_TRUE(castIntegralRangeSet(IntRangeSet(), UChar, ctx()).empty());
}

TEST_F(ThreadSafetyRangesTest, Negate) {
  QualType Int = ctx().IntTy;
  EXPECT_THAT(intervals(negateRangeSet(range(Int, 1, 3), Int, ctx())),
              ElementsAre(Pair(-3, -1)));
  // The negation of INT_MIN is INT_MIN.
  EXPECT_THAT(
      intervals(
          negateRangeSet(range(Int, INT32_MIN, INT32_MIN + 1), Int, ctx())),
      ElementsAre(Pair(INT32_MIN, INT32_MIN), Pair(INT32_MAX, INT32_MAX)));
  // Unsigned negation wraps around.
  QualType UChar = ctx().UnsignedCharTy;
  EXPECT_THAT(intervals(negateRangeSet(range(UChar, 0, 2), UChar, ctx())),
              ElementsAre(Pair(0, 0), Pair(254, 255)));
}

TEST_F(ThreadSafetyRangesTest, AddConst) {
  QualType Int = ctx().IntTy;
  QualType UChar = ctx().UnsignedCharTy;
  EXPECT_THAT(intervals(addConstToRangeSet(range(Int, 0, 2), val(5),
                                           /*Subtract=*/false, Int, ctx())),
              ElementsAre(Pair(5, 7)));
  EXPECT_THAT(intervals(addConstToRangeSet(range(Int, 0, 2), val(5),
                                           /*Subtract=*/true, Int, ctx())),
              ElementsAre(Pair(-5, -3)));
  // Unsigned addition wraps around.
  EXPECT_THAT(intervals(addConstToRangeSet(range(UChar, 250, 255), val(10),
                                           /*Subtract=*/false, UChar, ctx())),
              ElementsAre(Pair(4, 9)));
  // K - [1, 3] = [K - 3, K - 1].
  EXPECT_THAT(
      intervals(subRangeSetFromConst(val(10), range(Int, 1, 3), Int, ctx())),
      ElementsAre(Pair(7, 9)));
}

TEST_F(ThreadSafetyRangesTest, TruncateToBitField) {
  QualType UInt = ctx().UnsignedIntTy;
  QualType Int = ctx().IntTy;
  IntDomain IntDom = dom(Int);
  // A 2-bit unsigned bit-field holds the values 0..3.
  EXPECT_THAT(
      intervals(truncateToBitField(range(Int, 1, 2), 2, UInt, IntDom, ctx())),
      ElementsAre(Pair(1, 2)));
  EXPECT_THAT(
      intervals(truncateToBitField(range(Int, 5, 5), 2, UInt, IntDom, ctx())),
      ElementsAre(Pair(1, 1)));
  // A 2-bit signed bit-field holds the values -2..1.
  EXPECT_THAT(
      intervals(truncateToBitField(range(Int, 2, 3), 2, Int, IntDom, ctx())),
      ElementsAre(Pair(-2, -1)));
  // Spans smaller than 2^BitWidth that cross a wrap boundary map exactly.
  EXPECT_THAT(intervals(truncateToBitField(range(Int, 240, 270), 8, UInt,
                                           IntDom, ctx())),
              ElementsAre(Pair(0, 14), Pair(240, 255)));
  EXPECT_THAT(intervals(truncateToBitField(range(Int, 300, 330), 8, UInt,
                                           IntDom, ctx())),
              ElementsAre(Pair(44, 74)));
  // Large spans cover all values of the bit-field.
  EXPECT_THAT(intervals(truncateToBitField(range(Int, 0, 1000), 2, UInt, IntDom,
                                           ctx())),
              ElementsAre(Pair(0, 3)));
  // A bit-field as wide as its type does not truncate.
  EXPECT_THAT(
      intervals(truncateToBitField(range(Int, -7, 7), 32, Int, IntDom, ctx())),
      ElementsAre(Pair(-7, 7)));
}

TEST_F(ThreadSafetyRangesTest, FoldIntBinOp) {
  QualType Int = ctx().IntTy;
  QualType UChar = ctx().UnsignedCharTy;
  auto Fold = [&](BinaryOperator::Opcode Opc, int64_t L, int64_t R,
                  QualType Ty) -> std::optional<int64_t> {
    if (auto V = foldIntBinOp(Opc, val(L), val(R), Ty, ctx()))
      return V->getExtValue();
    return std::nullopt;
  };
  EXPECT_EQ(Fold(BO_Add, 2, 3, Int), 5);
  EXPECT_EQ(Fold(BO_Sub, 2, 3, Int), -1);
  EXPECT_EQ(Fold(BO_Mul, 6, 7, Int), 42);
  EXPECT_EQ(Fold(BO_Div, 7, 2, Int), 3);
  EXPECT_EQ(Fold(BO_Rem, 7, 2, Int), 1);
  EXPECT_EQ(Fold(BO_And, 6, 3, Int), 2);
  EXPECT_EQ(Fold(BO_Or, 6, 3, Int), 7);
  EXPECT_EQ(Fold(BO_Xor, 6, 3, Int), 5);
  EXPECT_EQ(Fold(BO_Shl, 1, 4, Int), 16);
  EXPECT_EQ(Fold(BO_Shr, 16, 4, Int), 1);
  // The result is converted to the result type.
  EXPECT_EQ(Fold(BO_Add, 250, 10, UChar), 4);
  // Undefined operations are not folded.
  EXPECT_EQ(Fold(BO_Div, 1, 0, Int), std::nullopt);
  EXPECT_EQ(Fold(BO_Div, INT32_MIN, -1, Int), std::nullopt);
  EXPECT_EQ(Fold(BO_Shl, 1, 32, Int), std::nullopt);
  EXPECT_EQ(Fold(BO_Shl, 1, -1, Int), std::nullopt);
  // Comparisons are not folded.
  EXPECT_EQ(Fold(BO_LT, 1, 2, Int), std::nullopt);
  // Operands with different signedness are normalized before folding.
  auto MixedV = foldIntBinOp(BO_Add, llvm::APSInt::get(2),
                             llvm::APSInt::getUnsigned(3), Int, ctx());
  ASSERT_TRUE(MixedV);
  EXPECT_EQ(MixedV->getExtValue(), 5);
}

TEST_F(ThreadSafetyRangesTest, CompareRangeSets) {
  QualType Int = ctx().IntTy;
  IntDomain Res = dom(Int);
  auto Cmp = [&](BinaryOperator::Opcode Opc, const IntRangeSet &L,
                 const IntRangeSet &R) {
    auto V = compareRangeSets(Opc, L, R, Res, /*IsMemberPtrComparison=*/false);
    EXPECT_TRUE(V.has_value());
    return V ? intervals(*V) : Intervals{};
  };
  // Always true, always false, and either.
  EXPECT_THAT(Cmp(BO_LT, range(Int, 0, 2), range(Int, 5, 5)),
              ElementsAre(Pair(1, 1)));
  EXPECT_THAT(Cmp(BO_GT, range(Int, 0, 2), range(Int, 5, 5)),
              ElementsAre(Pair(0, 0)));
  EXPECT_THAT(Cmp(BO_LE, range(Int, 0, 5), range(Int, 3, 3)),
              ElementsAre(Pair(0, 1)));
  EXPECT_THAT(Cmp(BO_EQ, range(Int, 3, 3), range(Int, 3, 3)),
              ElementsAre(Pair(1, 1)));
  EXPECT_THAT(Cmp(BO_NE, range(Int, 3, 3), range(Int, 3, 3)),
              ElementsAre(Pair(0, 0)));
  EXPECT_THAT(Cmp(BO_EQ, range(Int, 0, 2), range(Int, 4, 6)),
              ElementsAre(Pair(0, 0)));
  // Comparisons of empty sets have no values.
  EXPECT_THAT(Cmp(BO_EQ, IntRangeSet(), range(Int, 4, 6)), IsEmpty());
  // Other operators are not comparisons.
  EXPECT_FALSE(compareRangeSets(BO_Add, range(Int, 0, 1), range(Int, 0, 1), Res,
                                /*IsMemberPtrComparison=*/false));
  // Only the null-ness of member pointers is known.
  IntDomain Bool = dom(ctx().BoolTy);
  IntRangeSet NonNull = IntRangeSet::single(Bool, val(1));
  auto MP = compareRangeSets(BO_EQ, NonNull, NonNull, Res,
                             /*IsMemberPtrComparison=*/true);
  ASSERT_TRUE(MP);
  EXPECT_THAT(intervals(*MP), ElementsAre(Pair(0, 1)));
  EXPECT_FALSE(compareRangeSets(BO_LT, NonNull, NonNull, Res,
                                /*IsMemberPtrComparison=*/true));
}

TEST_F(ThreadSafetyRangesTest, ScalarDomainForType) {
  auto Built = tooling::buildASTFromCodeWithArgs(
      R"cpp(
        struct S { int x; };
        enum CompleteEnum : short { E_A = -1, E_B = 2 };
        S s_var;
        int S::*mp_var;
        CompleteEnum ce_var;
      )cpp",
      {"-std=c++17"});
  ASSERT_TRUE(Built);
  ASTContext &C = Built->getASTContext();

  auto IntDom = getScalarDomainForType(C.IntTy, C);
  ASSERT_TRUE(IntDom);
  EXPECT_EQ(IntDom->Lo.getSExtValue(), INT32_MIN);
  EXPECT_EQ(IntDom->Hi.getSExtValue(), INT32_MAX);

  IntDomain UIntPtrDom = IntDomain::forType(C.getUIntPtrType(), C);
  auto PtrDom = getScalarDomainForType(C.getPointerType(C.IntTy), C);
  ASSERT_TRUE(PtrDom);
  EXPECT_EQ(*PtrDom, UIntPtrDom);

  auto NullPtrDom = getScalarDomainForType(C.NullPtrTy, C);
  ASSERT_TRUE(NullPtrDom);
  EXPECT_EQ(*NullPtrDom, UIntPtrDom);

  llvm::StringMap<QualType> VarTypes;
  for (const Decl *D : C.getTranslationUnitDecl()->decls())
    if (const auto *VD = dyn_cast<VarDecl>(D))
      VarTypes[VD->getName()] = VD->getType();

  auto MemPtrDom = getScalarDomainForType(VarTypes["mp_var"], C);
  ASSERT_TRUE(MemPtrDom);
  EXPECT_EQ(MemPtrDom->Lo.getSExtValue(), 0);
  EXPECT_EQ(MemPtrDom->Hi.getSExtValue(), 1);

  auto CompleteEnumDom = getScalarDomainForType(VarTypes["ce_var"], C);
  ASSERT_TRUE(CompleteEnumDom);
  EXPECT_EQ(CompleteEnumDom->Lo.getSExtValue(), INT16_MIN);
  EXPECT_EQ(CompleteEnumDom->Hi.getSExtValue(), INT16_MAX);

  EXPECT_FALSE(getScalarDomainForType(C.DoubleTy, C));
  EXPECT_FALSE(getScalarDomainForType(C.VoidTy, C));
  EXPECT_FALSE(getScalarDomainForType(VarTypes["s_var"], C));

  auto BuiltC = tooling::buildASTFromCodeWithArgs(
      "enum IncompleteEnum; extern enum IncompleteEnum *ie_ptr;", {"-x", "c"});
  ASSERT_TRUE(BuiltC);
  ASTContext &CC = BuiltC->getASTContext();
  for (const Decl *D : CC.getTranslationUnitDecl()->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D);
        VD && VD->getName() == "ie_ptr") {
      EXPECT_FALSE(getScalarDomainForType(VD->getType()->getPointeeType(), CC));
    }
  }
}

TEST_F(ThreadSafetyRangesTest, TruncToType) {
  EXPECT_EQ(truncToType(val(0x1ff), ctx().SignedCharTy, ctx()).getSExtValue(),
            -1);
  EXPECT_EQ(truncToType(val(-1), ctx().UnsignedCharTy, ctx()).getZExtValue(),
            255u);
  llvm::APSInt NarrowNeg(llvm::APInt(8, -2, /*isSigned=*/true),
                         /*isUnsigned=*/false);
  EXPECT_EQ(truncToType(NarrowNeg, ctx().IntTy, ctx()).getSExtValue(), -2);
  EXPECT_EQ(truncToType(val(42), ctx().BoolTy, ctx()).getZExtValue(), 1u);
  EXPECT_EQ(truncToType(val(0), ctx().BoolTy, ctx()).getZExtValue(), 0u);
}

TEST_F(ThreadSafetyRangesTest, BijectiveReinterpretCast) {
  auto Built = tooling::buildASTFromCodeWithArgs(
      R"cpp(
        void f(int x, void *p) {
          unsigned u = static_cast<unsigned>(x);
          short s = static_cast<short>(x);
          auto ip = reinterpret_cast<__UINTPTR_TYPE__>(p);
          void *q = reinterpret_cast<void *>(ip);
          (void)u; (void)s; (void)q;
        }
      )cpp",
      {"-std=c++17"});
  ASSERT_TRUE(Built);
  ASTContext &C = Built->getASTContext();
  SmallVector<const CastExpr *, 4> Casts;
  for (const Decl *D : C.getTranslationUnitDecl()->decls()) {
    const auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD || FD->getName() != "f")
      continue;
    for (const Stmt *S : FD->getBody()->children()) {
      const auto *DS = dyn_cast<DeclStmt>(S);
      if (!DS)
        continue;
      const auto *VD = cast<VarDecl>(DS->getSingleDecl());
      Casts.push_back(cast<CastExpr>(stripNoOpExprWrappers(VD->getInit())));
    }
  }
  ASSERT_EQ(Casts.size(), 4u);
  // int -> unsigned (same width): bijective.
  EXPECT_TRUE(isBijectiveReinterpretCast(Casts[0], C));
  // int -> short (narrowing): not bijective.
  EXPECT_FALSE(isBijectiveReinterpretCast(Casts[1], C));
  // void * -> uintptr_t and uintptr_t -> void *: bijective.
  EXPECT_TRUE(isBijectiveReinterpretCast(Casts[2], C));
  EXPECT_TRUE(isBijectiveReinterpretCast(Casts[3], C));

  // Mapping [UINT32_MAX - 1, UINT32_MAX] backward from unsigned to int yields
  // [-2, -1].
  IntDomain UIntDom = IntDomain::forType(C.UnsignedIntTy, C);
  IntDomain IntDom = IntDomain::forType(C.IntTy, C);
  IntRangeSet HighUnsigned = IntRangeSet::closedRange(
      UIntDom, val(static_cast<int64_t>(UINT32_MAX) - 1),
      val(static_cast<int64_t>(UINT32_MAX)));
  SmallVector<const CastExpr *, 1> Chain{Casts[0]};
  IntRangeSet Mapped =
      mapRangeBackwardThroughBijectiveCasts(HighUnsigned, Chain, IntDom, C);
  EXPECT_THAT(intervals(Mapped), ElementsAre(Pair(-2, -1)));
}

TEST_F(ThreadSafetyRangesTest, RangeMappableAndApplyCast) {
  auto Built = tooling::buildASTFromCodeWithArgs(
      R"cpp(
        struct B1 { int a; };
        struct B2 { int b; };
        struct D : B1, B2 { int c; };
        struct ConvBool { operator bool() const; };
        struct ConvCtor { ConvCtor(int); };
        void f(int x, D *d, int D::*mp, ConvBool cb) {
          bool b1 = x;
          bool b2 = d;
          bool b3 = mp;
          B1 *p1 = d;
          B2 *p2 = d;
          bool b4 = static_cast<bool>(cb);
          ConvCtor cc = x;
          (void)b1; (void)b2; (void)b3; (void)p1; (void)p2; (void)b4; (void)cc;
        }
      )cpp",
      {"-std=c++17"});
  ASSERT_TRUE(Built);
  ASTContext &C = Built->getASTContext();
  SmallVector<const CastExpr *, 8> Casts;
  for (const Decl *D : C.getTranslationUnitDecl()->decls()) {
    const auto *FD = dyn_cast<FunctionDecl>(D);
    if (!FD || FD->getName() != "f")
      continue;
    for (const Stmt *S : FD->getBody()->children()) {
      const auto *DS = dyn_cast<DeclStmt>(S);
      if (!DS)
        continue;
      const auto *VD = cast<VarDecl>(DS->getSingleDecl());
      const Expr *Init = VD->getInit()->IgnoreParens();
      if (const auto *CE = dyn_cast<CXXConstructExpr>(Init);
          CE && CE->getNumArgs() == 1)
        Init = CE->getArg(0)->IgnoreParens();
      Casts.push_back(cast<CastExpr>(Init));
    }
  }
  ASSERT_EQ(Casts.size(), 7u);
  for (unsigned I = 0; I < 6; ++I)
    EXPECT_TRUE(isRangeMappableCast(Casts[I])) << "I=" << I;
  // User-defined conversion via constructor is not a conversion-function cast.
  EXPECT_FALSE(isRangeMappableCast(Casts[6]));

  IntDomain IntDom = IntDomain::forType(C.IntTy, C);
  IntDomain BoolDom = IntDomain::forType(C.BoolTy, C);
  // CK_IntegralToBoolean: [0, 0] -> [0, 0], [2, 5] -> [1, 1], [-1, 1] -> [0, 1]
  EXPECT_THAT(intervals(applyCast(Casts[0], IntRangeSet::single(IntDom, val(0)),
                                  BoolDom, C)),
              ElementsAre(Pair(0, 0)));
  EXPECT_THAT(intervals(applyCast(
                  Casts[0], IntRangeSet::closedRange(IntDom, val(2), val(5)),
                  BoolDom, C)),
              ElementsAre(Pair(1, 1)));
  EXPECT_THAT(intervals(applyCast(
                  Casts[0], IntRangeSet::closedRange(IntDom, val(-1), val(1)),
                  BoolDom, C)),
              ElementsAre(Pair(0, 1)));

  // CK_DerivedToBase preserves nullness for both zero and non-zero offsets.
  IntDomain PtrDom = *getScalarDomainForType(Casts[4]->getType(), C);
  for (const CastExpr *DBC : {Casts[3], Casts[4]}) {
    EXPECT_THAT(intervals(applyCast(DBC, IntRangeSet::single(PtrDom, val(0)),
                                    PtrDom, C)),
                ElementsAre(Pair(0, 0)));
    IntRangeSet NonNull = applyCast(
        DBC, IntRangeSet::truthSet(PtrDom, /*WantNonZero=*/true), PtrDom, C);
    EXPECT_FALSE(NonNull.mayBeZero());
    EXPECT_TRUE(NonNull.mayBeNonZero());
  }
}

TEST_F(ThreadSafetyRangesTest, Int128Ranges) {
  if (!ctx().getTargetInfo().hasInt128Type())
    GTEST_SKIP();
  QualType I128 = ctx().Int128Ty;
  QualType U128 = ctx().UnsignedInt128Ty;
  IntDomain S128Dom = dom(I128);
  IntDomain U128Dom = dom(U128);
  EXPECT_EQ(S128Dom.BitWidth, 130u);
  EXPECT_EQ(U128Dom.BitWidth, 130u);
  EXPECT_TRUE(S128Dom.Lo.isNegative());
  EXPECT_FALSE(U128Dom.Lo.isNegative());

  IntRangeSet R = range(ctx().IntTy, -5, 10);
  IntRangeSet CastS128 = castIntegralRangeSet(R, I128, ctx());
  EXPECT_THAT(intervals(CastS128), ElementsAre(Pair(-5, 10)));
}

TEST_F(ThreadSafetyRangesTest, ExtractPureStmtExprAndScanVars) {
  auto Built = tooling::buildASTFromCodeWithArgs(
      R"cpp(
        void f() {
          int a = 0, b = 0, c = 0, d = 0;
          int r1 = ({ a + 1; });
          int r2 = ({ b = 2; b; });
          int r3 = ({ int tmp = a; tmp; });
          int r4 = ({ if (a) {} a; });
          int r5 = ({ c = 2; (void)&c; int tmp = a; tmp; });
          int r6 = ({ *&c = 2; a; });
          int r7 = ({ (void)&c; a; });
          int r8 = ({ int x = 1; int t = (x = 2, x); t; });
          int *p = &c;
          auto l1 = [&d]() { return d; };
          int s = sizeof(a = 5);
          (void)r1; (void)r2; (void)r3; (void)r4; (void)r5; (void)r6;
          (void)r7; (void)r8;
          (void)p; (void)l1; (void)s;
        }
      )cpp",
      {"-std=c++17", "-Wno-unevaluated-expression"});
  ASSERT_TRUE(Built);
  ASTContext &C = Built->getASTContext();
  const FunctionDecl *FD = nullptr;
  for (const Decl *D : C.getTranslationUnitDecl()->decls()) {
    if (const auto *F = dyn_cast<FunctionDecl>(D); F && F->getName() == "f") {
      FD = F;
      break;
    }
  }
  ASSERT_NE(FD, nullptr);

  llvm::StringMap<const ValueDecl *> Vars;
  llvm::StringMap<const StmtExpr *> StmtExprs;
  for (const Stmt *S : FD->getBody()->children()) {
    const auto *DS = dyn_cast<DeclStmt>(S);
    if (!DS)
      continue;
    for (const Decl *D : DS->decls()) {
      const auto *VD = dyn_cast<VarDecl>(D);
      if (!VD)
        continue;
      Vars[VD->getName()] = cast<ValueDecl>(VD->getCanonicalDecl());
      if (const Expr *Init = VD->getInit())
        if (const auto *SE = dyn_cast<StmtExpr>(Init->IgnoreParenImpCasts()))
          StmtExprs[VD->getName()] = SE;
    }
  }
  ASSERT_EQ(StmtExprs.size(), 8u);
  EXPECT_NE(extractPureStmtExpr(StmtExprs["r1"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r2"], C), nullptr);
  EXPECT_NE(extractPureStmtExpr(StmtExprs["r3"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r4"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r5"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r6"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r7"], C), nullptr);
  EXPECT_EQ(extractPureStmtExpr(StmtExprs["r8"], C), nullptr);

  llvm::SmallPtrSet<const ValueDecl *, 8> Escaped, Modified;
  scanTrylockVars(FD->getBody(), C, Escaped, Modified);
  // 'a' is only read (sizeof(a = 5) is unevaluated).
  EXPECT_FALSE(Escaped.contains(Vars["a"]));
  EXPECT_FALSE(Modified.contains(Vars["a"]));
  // 'b' is modified by direct assignment, not escaped.
  EXPECT_FALSE(Escaped.contains(Vars["b"]));
  EXPECT_TRUE(Modified.contains(Vars["b"]));
  // 'c' has its address taken.
  EXPECT_TRUE(Escaped.contains(Vars["c"]));
  EXPECT_TRUE(Modified.contains(Vars["c"]));
  // 'd' is captured by reference in a lambda.
  EXPECT_TRUE(Escaped.contains(Vars["d"]));
  EXPECT_TRUE(Modified.contains(Vars["d"]));
}

} // namespace
