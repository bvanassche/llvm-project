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

} // namespace
