//===- ThreadSafetyTrylockCond.cpp - Try-acquire conditions ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Evaluation of branch conditions that test the result of a
// try-acquire function at its call sites.
//
//===----------------------------------------------------------------------===//

#include "ThreadSafetyInternal.h"
#include "clang/AST/StmtObjC.h"

using namespace clang;
using namespace threadSafety;

const ThreadSafetyAnalyzer::SwitchCaseTable &
ThreadSafetyAnalyzer::getSwitchCaseTable(const SwitchStmt *SS,
                                         const IntDomain &Dom) {
  auto &Entries = SwitchTables[SS];
  for (auto &[EDom, Table] : Entries)
    if (EDom == Dom)
      return *Table;

  auto Table = std::make_unique<SwitchCaseTable>();
  Table->Valid = true;
  SmallVector<IntRangeSet, 8> AllCases;
  for (const SwitchCase *SC = SS->getSwitchCaseList(); SC;
       SC = SC->getNextSwitchCase()) {
    const auto *CS = dyn_cast<CaseStmt>(SC);
    if (!CS)
      continue;
    auto Lo = getIntegralOrEnumConstantExpr(CS->getLHS(), *ASTCtx);
    auto Hi = CS->getRHS()
                  ? getIntegralOrEnumConstantExpr(CS->getRHS(), *ASTCtx)
                  : Lo;
    if (!Lo || !Hi) {
      Table->Valid = false;
      break;
    }
    IntRangeSet CaseSet = IntRangeSet::closedRange(Dom, *Lo, *Hi);
    AllCases.push_back(CaseSet);
    Table->CaseSets.try_emplace(CS, std::move(CaseSet));
  }
  if (Table->Valid)
    Table->DefaultSet = IntRangeSet::unionAll(AllCases).complement(Dom);
  else
    Table->CaseSets.clear();
  Entries.emplace_back(Dom, std::move(Table));
  return *Entries.back().second;
}

LocalVarContext
ThreadSafetyAnalyzer::getLogicalOpLHSContext(const BinaryOperator *BOP,
                                             LocalVarContext C) {
  if (!BOP || C.isEmpty())
    return C;
  if (CurrentSortedGraph) {
    if (!BuiltLogicalOpTermBlock) {
      BuiltLogicalOpTermBlock = true;
      for (const CFGBlock *B : *CurrentSortedGraph) {
        if (const auto *TermBO =
                dyn_cast_or_null<BinaryOperator>(B->getTerminatorStmt());
            TermBO && TermBO->isLogicalOp()) {
          auto [It, Inserted] =
              LogicalOpTermBlock.try_emplace(TermBO, B->getBlockID());
          if (!Inserted && It->second != B->getBlockID())
            It->second = ~0u;
        }
      }
    }
    if (auto It = LogicalOpTermBlock.find(BOP);
        It != LogicalOpTermBlock.end() && It->second < BlockInfo.size())
      return BlockInfo[It->second].ExitContext;
  }
  llvm::SmallPtrSet<const ValueDecl *, 4> Mod;
  scanModifiedVars(BOP->getRHS(), *ASTCtx, Mod);
  for (const ValueDecl *VD : Mod)
    if (const auto *ND = dyn_cast<NamedDecl>(VD))
      C = LocalVarMap.clearDefinitionIfSet(ND, C);
  return C;
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockRangeCond(const Stmt *Cond,
                                               LocalVarContext C,
                                               unsigned Depth) {
  if (!Cond || Depth > MaxRangeCondDepth)
    return {};
  std::pair<const Stmt *, const void *> Key(Cond, C.getRootWithoutRetain());
  if (auto It = RangeCondCache.find(Key); It != RangeCondCache.end())
    return It->second.second;
  TrylockRangeCondResult Res = evaluateTrylockRangeCondImpl(Cond, C, Depth);
  if (Res.Call) {
    Res.TrueSet.widen(MaxStateRangeIntervals);
    Res.FalseSet.widen(MaxStateRangeIntervals);
  }
  RangeCondCache.try_emplace(Key, C, Res);
  return Res;
}

std::optional<llvm::APSInt>
ThreadSafetyAnalyzer::evaluateTrylockCmpConstSide(const Expr *ConstSide,
                                                  const BinaryOperator *BOP) {
  QualType Ty = ConstSide->getType();
  if (Ty->isIntegralOrEnumerationType())
    return evaluateRuntimeIntConstant(ConstSide, *ASTCtx);
  if (Ty->isMemberPointerType()) {
    if (!BOP->isEqualityOp())
      return std::nullopt;
    const Expr *E = skipValuePreservingWrappers(ConstSide, nullptr);
    if (isa_and_nonnull<CXXNullPtrLiteralExpr, GNUNullExpr>(E))
      return llvm::APSInt::get(0);
    if (const auto *CE = dyn_cast_or_null<CastExpr>(E);
        CE && CE->getCastKind() == CK_NullToMemberPointer)
      return llvm::APSInt::get(0);
    return std::nullopt;
  }
  if (Ty->isAnyPointerType() || Ty->isNullPtrType()) {
    const Expr *E = skipValuePreservingWrappers(ConstSide, nullptr);
    if (isa_and_nonnull<CXXNullPtrLiteralExpr, GNUNullExpr>(E))
      return llvm::APSInt::get(0);
    if (const auto *CE = dyn_cast_or_null<CastExpr>(E)) {
      if (CE->getCastKind() == CK_NullToPointer)
        return llvm::APSInt::get(0);
      if (CE->getCastKind() == CK_IntegralToPointer)
        E = CE->getSubExpr();
    }
    if (E && E->getType()->isIntegralOrEnumerationType())
      if (auto ICE = evaluateRuntimeIntConstant(E, *ASTCtx))
        return truncToType(*ICE, ASTCtx->getUIntPtrType(), *ASTCtx);
    return std::nullopt;
  }
  return std::nullopt;
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockBinaryCondCmp(
    const Expr *CondSide, const Expr *ConstSide, BinaryOperator::Opcode SideOp,
    LocalVarContext C, const BinaryOperator *BOP) {
  auto K = evaluateTrylockCmpConstSide(ConstSide, BOP);
  if (!K)
    return {};
  LocalVarContext SubCtx = C;
  const auto *BCOP = dyn_cast_or_null<BinaryConditionalOperator>(
      skipValuePreservingWrappers(CondSide, &SubCtx));
  if (!BCOP)
    return {};
  auto FalseVal = evaluateTrylockCmpConstSide(BCOP->getFalseExpr(), BOP);
  if (!FalseVal)
    return {};
  auto ResDom = getScalarDomain(BCOP->getType());
  if (!ResDom)
    return {};
  const CallExpr *SubCall = unwrapTrylockValueExpr(BCOP->getTrueExpr(), SubCtx);
  const NamedDecl *Callee = getTrylockCallee(SubCall);
  if (!Callee)
    return {};
  IntDomain Dom = getTrylockCallDomain(SubCall);
  IntRangeSet CmpTrue = IntRangeSet::forComparison(Dom, SideOp, *K);
  IntRangeSet NonZero = IntRangeSet::truthSet(Dom, true);
  IntRangeSet Zero = IntRangeSet::truthSet(Dom, false);
  IntRangeSet TrueSet = NonZero.intersect(CmpTrue);
  if (!IntRangeSet::single(*ResDom, *FalseVal)
           .intersect(IntRangeSet::forComparison(*ResDom, SideOp, *K))
           .empty())
    TrueSet = TrueSet.unionWith(Zero);
  IntRangeSet FalseSet = TrueSet.complement(Dom);
  return {SubCall,
          Callee,
          SubCtx,
          std::move(Dom),
          std::move(TrueSet),
          std::move(FalseSet)};
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockBoolEq(const Expr *BoolSide,
                                            const Expr *ConstSide,
                                            LocalVarContext C,
                                            const BinaryOperator *BOP,
                                            unsigned Depth) {
  auto K = evaluateTrylockCmpConstSide(ConstSide, BOP);
  if (!K)
    return {};
  auto Res = evaluateTrylockRangeCond(BoolSide, C, Depth + 1);
  if (!Res.Call || (*K != 0 && !isGuaranteedZeroOrOneExpr(BoolSide, C)))
    return {};
  if (*K == 1) {
    if (BOP->getOpcode() == BO_NE)
      std::swap(Res.TrueSet, Res.FalseSet);
  } else if (*K == 0) {
    if (BOP->getOpcode() == BO_EQ)
      std::swap(Res.TrueSet, Res.FalseSet);
  } else {
    IntRangeSet All = Res.TrueSet.unionWith(Res.FalseSet);
    if (BOP->getOpcode() == BO_EQ) {
      Res.TrueSet = {};
      Res.FalseSet = std::move(All);
    } else {
      Res.TrueSet = std::move(All);
      Res.FalseSet = {};
    }
  }
  return Res;
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockRangeCondImpl(const Stmt *Cond,
                                                   LocalVarContext C,
                                                   unsigned Depth) {
  if (!Cond)
    return {};

  if (const auto *PE = dyn_cast<ParenExpr>(Cond))
    return evaluateTrylockRangeCond(PE->getSubExpr(), C, Depth + 1);
  if (const auto *FE = dyn_cast<FullExpr>(Cond))
    return evaluateTrylockRangeCond(FE->getSubExpr(), C, Depth + 1);

  if (const auto *CE = dyn_cast<CastExpr>(Cond)) {
    switch (CE->getCastKind()) {
    case CK_IntegralToBoolean:
    case CK_PointerToBoolean:
    case CK_MemberPointerToBoolean:
    case CK_FloatingToBoolean:
    case CK_FloatingComplexToBoolean:
    case CK_BooleanToSignedIntegral:
      return evaluateTrylockRangeCond(CE->getSubExpr(), C, Depth + 1);
    case CK_DerivedToBase:
    case CK_UncheckedDerivedToBase:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType())
        return evaluateTrylockRangeCond(CE->getSubExpr(), C, Depth + 1);
      return {};
    default:
      if (isValuePreservingCast(CE, *ASTCtx) ||
          isBijectiveReinterpretCast(CE, *ASTCtx))
        return evaluateTrylockRangeCond(CE->getSubExpr(), C, Depth + 1);
      return {};
    }
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(Cond)) {
    const Expr *E = LocalVarMap.lookupValueExpr(DRE->getDecl(), C);
    return evaluateTrylockRangeCond(E, C, Depth + 1);
  }

  if (const auto *SE = dyn_cast<StmtExpr>(Cond)) {
    if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty())
      if (const auto *E = dyn_cast<Expr>(CS->body_back()))
        return evaluateTrylockRangeCond(E, C, Depth + 1);
    return {};
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(Cond)) {
    if (isBuiltinExpectCall(CallExp))
      return evaluateTrylockRangeCond(CallExp->getArg(0), C, Depth + 1);

    if (const NamedDecl *Callee = getTrylockCallee(CallExp)) {
      IntDomain Dom = getTrylockCallDomain(CallExp);
      IntRangeSet FalseSet = IntRangeSet::truthSet(Dom, false);
      IntRangeSet TrueSet = IntRangeSet::truthSet(Dom, true);
      return {CallExp,
              Callee,
              C,
              std::move(Dom),
              std::move(TrueSet),
              std::move(FalseSet)};
    }
    return {};
  }

  if (const auto *UOP = dyn_cast<UnaryOperator>(Cond)) {
    if (UOP->getOpcode() == UO_LNot) {
      auto Res = evaluateTrylockRangeCond(UOP->getSubExpr(), C, Depth + 1);
      if (Res.Call)
        std::swap(Res.TrueSet, Res.FalseSet);
      return Res;
    }
    return {};
  }

  if (const auto *BOP = dyn_cast<BinaryOperator>(Cond)) {
    if (BOP->getOpcode() == BO_Assign) {
      // A bit-field assignment truncates the stored value.
      if (BOP->getLHS()->refersToBitField())
        return {};
      return evaluateTrylockRangeCond(BOP->getRHS(), C, Depth + 1);
    }

    if (BOP->isRelationalOp() || BOP->isEqualityOp()) {
      return evaluateTrylockCmpCond(BOP, C, Depth);
    }

    if (BOP->getOpcode() == BO_LAnd || BOP->getOpcode() == BO_LOr) {
      return evaluateTrylockLogicalOpCond(BOP, C, Depth);
    }
    return {};
  }

  if (const auto *BCOP = dyn_cast<BinaryConditionalOperator>(Cond)) {
    bool FCond;
    if (getStaticBooleanValue(BCOP->getFalseExpr(), *ASTCtx, FCond) && !FCond)
      return evaluateTrylockRangeCond(BCOP->getCommon(), C, Depth + 1);
    return {};
  }

  if (const auto *COP = dyn_cast<ConditionalOperator>(Cond)) {
    bool TCond, FCond;
    if (getStaticBooleanValue(COP->getTrueExpr(), *ASTCtx, TCond) &&
        getStaticBooleanValue(COP->getFalseExpr(), *ASTCtx, FCond)) {
      if (TCond && !FCond)
        return evaluateTrylockRangeCond(COP->getCond(), C, Depth + 1);
      if (!TCond && FCond) {
        auto Res = evaluateTrylockRangeCond(COP->getCond(), C, Depth + 1);
        if (Res.Call)
          std::swap(Res.TrueSet, Res.FalseSet);
        return Res;
      }
    }
    return {};
  }

  return {};
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockCmpCond(const BinaryOperator *BOP,
                                             LocalVarContext C,
                                             unsigned Depth) {
  auto UnwrapCastChain =
      [&](const Expr *Side, LocalVarContext &SubCtx,
          SmallVectorImpl<const CastExpr *> &Casts) -> const CallExpr * {
    while ((Side = skipValuePreservingWrappers(Side, &SubCtx))) {
      if (const auto *CE = dyn_cast<CallExpr>(Side))
        return CE;
      const auto *Cast = dyn_cast<CastExpr>(Side);
      if (!Cast || !isBijectiveReinterpretCast(Cast, *ASTCtx))
        break;
      Casts.push_back(Cast);
      Side = Cast->getSubExpr();
    }
    return nullptr;
  };
  auto TryCallOrCastSide =
      [&](const Expr *CallSide, const Expr *ConstSide,
          BinaryOperator::Opcode CmpOp,
          bool AllowBijectiveCasts) -> TrylockRangeCondResult {
    LocalVarContext CallCtx = C;
    SmallVector<const CastExpr *, 2> Casts;
    const CallExpr *CallExp =
        AllowBijectiveCasts
            ? UnwrapCastChain(CallSide, CallCtx, Casts)
            : unwrapValuePreservingToCallExpr(CallSide, CallCtx);
    if (!CallExp || (AllowBijectiveCasts && Casts.empty()))
      return {};
    auto ConstVal = evaluateTrylockCmpConstSide(ConstSide, BOP);
    if (!ConstVal)
      return {};
    if (const NamedDecl *Callee = getTrylockCallee(CallExp)) {
      IntDomain Dom = getTrylockCallDomain(CallExp);
      auto CastDom = Casts.empty() ? std::optional(Dom)
                                   : getScalarDomain(CallSide->getType());
      if (!CastDom)
        return {};
      IntRangeSet TrueSet = mapRangeBackwardThroughBijectiveCasts(
          IntRangeSet::forComparison(*CastDom, CmpOp, *ConstVal), Casts, Dom,
          *ASTCtx);
      IntRangeSet FalseSet = TrueSet.complement(Dom);
      return {CallExp,
              Callee,
              CallCtx,
              std::move(Dom),
              std::move(TrueSet),
              std::move(FalseSet)};
    }
    return {};
  };

  BinaryOperator::Opcode Opc = BOP->getOpcode();
  BinaryOperator::Opcode RevOpc = BinaryOperator::reverseComparisonOp(Opc);
  for (bool AllowCasts : {false, true}) {
    if (auto Res =
            TryCallOrCastSide(BOP->getLHS(), BOP->getRHS(), Opc, AllowCasts);
        Res.Call)
      return Res;
    if (auto Res =
            TryCallOrCastSide(BOP->getRHS(), BOP->getLHS(), RevOpc, AllowCasts);
        Res.Call)
      return Res;
  }

  // Recognize GNU binary conditional expressions (x ?: false_const) Op K.
  if (auto Res = evaluateTrylockBinaryCondCmp(BOP->getLHS(), BOP->getRHS(), Opc,
                                              C, BOP);
      Res.Call)
    return Res;
  if (auto Res = evaluateTrylockBinaryCondCmp(BOP->getRHS(), BOP->getLHS(),
                                              RevOpc, C, BOP);
      Res.Call)
    return Res;

  if (BOP->isEqualityOp()) {
    if (auto Res =
            evaluateTrylockBoolEq(BOP->getLHS(), BOP->getRHS(), C, BOP, Depth);
        Res.Call)
      return Res;
    if (auto Res =
            evaluateTrylockBoolEq(BOP->getRHS(), BOP->getLHS(), C, BOP, Depth);
        Res.Call)
      return Res;
  }
  return {};
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockLogicalOpCond(const BinaryOperator *BOP,
                                                   LocalVarContext C,
                                                   unsigned Depth) {
  LocalVarContext LHSCtx = getLogicalOpLHSContext(BOP, C);
  auto RHSRes = evaluateTrylockRangeCond(BOP->getRHS(), C, Depth + 1);
  auto LHSRes = evaluateTrylockRangeCond(BOP->getLHS(), LHSCtx, Depth + 1);
  if (!RHSRes.Call) {
    if (!LHSRes.Call || stmtContainsExpr(BOP->getRHS(), LHSRes.Call))
      return {};
    IntRangeSet FullDom = IntRangeSet::full(LHSRes.Dom);
    if (BOP->getOpcode() == BO_LAnd)
      LHSRes.FalseSet = std::move(FullDom);
    else
      LHSRes.TrueSet = std::move(FullDom);
    return LHSRes;
  }
  IntRangeSet FullDom = IntRangeSet::full(RHSRes.Dom);
  const IntRangeSet &LHSTrue =
      (LHSRes.Call == RHSRes.Call) ? LHSRes.TrueSet : FullDom;
  const IntRangeSet &LHSFalse =
      (LHSRes.Call == RHSRes.Call) ? LHSRes.FalseSet : FullDom;
  if (BOP->getOpcode() == BO_LAnd) {
    RHSRes.TrueSet = LHSTrue.intersect(RHSRes.TrueSet);
    RHSRes.FalseSet = LHSFalse.unionWith(RHSRes.FalseSet);
  } else {
    RHSRes.TrueSet = LHSTrue.unionWith(RHSRes.TrueSet);
    RHSRes.FalseSet = LHSFalse.intersect(RHSRes.FalseSet);
  }
  return RHSRes;
}

/// Evaluate the condition \p Cond of a terminator. If \p Cond is a logical
/// operator, the block with the terminator evaluates the right-hand side of
/// \p Cond and the left-hand side is known to be true (&&) or false (||).
ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTerminatorTrylockCond(const Stmt *Cond,
                                                    LocalVarContext C,
                                                    unsigned Depth) {
  if (Depth > MaxRangeCondDepth)
    return {};
  const auto *BOP = dyn_cast_or_null<BinaryOperator>(
      stripNoOpExprWrappers(dyn_cast_or_null<Expr>(Cond)));
  if (!BOP || !BOP->isLogicalOp())
    return evaluateTrylockRangeCond(Cond, C, Depth);
  auto Res = evaluateTerminatorTrylockCond(BOP->getRHS(), C, Depth + 1);
  if (!Res.Call)
    return {};
  LocalVarContext LHSCtx = getLogicalOpLHSContext(BOP, C);
  auto LHSRes = evaluateTrylockRangeCond(BOP->getLHS(), LHSCtx, Depth + 1);
  if (LHSRes.Call == Res.Call) {
    const IntRangeSet &Known =
        BOP->getOpcode() == BO_LAnd ? LHSRes.TrueSet : LHSRes.FalseSet;
    // On the non-short-circuit edge (TrueSet for &&, FalseSet for ||), both
    // operands must hold (or both be false), so an empty intersection means
    // the edge is infeasible. On the short-circuit confluence edge (FalseSet
    // for &&, TrueSet for ||), keep the RHS set when the intersection is empty
    // so redundant conditions like (b || b) do not lose the RHS range.
    if (BOP->getOpcode() == BO_LAnd) {
      Res.TrueSet = Known.intersect(Res.TrueSet);
      if (IntRangeSet F = Known.intersect(Res.FalseSet); !F.empty())
        Res.FalseSet = std::move(F);
    } else {
      if (IntRangeSet T = Known.intersect(Res.TrueSet); !T.empty())
        Res.TrueSet = std::move(T);
      Res.FalseSet = Known.intersect(Res.FalseSet);
    }
    Res.TrueSet.widen(MaxStateRangeIntervals);
    Res.FalseSet.widen(MaxStateRangeIntervals);
    Res.ShortCircuitSet = Res.ShortCircuitSet.unionWith(
        BOP->getOpcode() == BO_LAnd ? LHSRes.FalseSet : LHSRes.TrueSet);
  } else if (!stmtContainsExpr(BOP->getRHS(), Res.Call)) {
    if (BOP->getOpcode() == BO_LAnd)
      Res.FalseSet = IntRangeSet::full(Res.Dom);
    else
      Res.TrueSet = IntRangeSet::full(Res.Dom);
  }
  return Res;
}

/// Whether \p Succ is the first (true) and whether it is the second (false)
/// successor of \p Pred.
std::pair<bool, bool> threadSafety::getBranchEdgeKinds(const CFGBlock *Pred,
                                                       const CFGBlock *Succ) {
  unsigned N = Pred->succ_size();
  return {N > 0 && *Pred->succ_begin() == Succ,
          N > 1 && *(Pred->succ_begin() + 1) == Succ};
}

/// The values of the condition of the switch statement that terminates a
/// block for which the edge to \p Succ is taken according to \p Table. For a
/// switch statement whose enumeration cases are all covered, CFGBuilder does
/// not add a reachable edge for the implicit default label.
ThreadSafetyAnalyzer::IntRangeSet threadSafety::getSwitchEdgeSet(
    const ThreadSafetyAnalyzer::SwitchCaseTable &Table, const CFGBlock *Succ) {
  const auto *TargetCS = dyn_cast_if_present<CaseStmt>(Succ->getLabel());
  if (auto It = Table.CaseSets.find(TargetCS); It != Table.CaseSets.end())
    return It->second;
  return Table.DefaultSet;
}

/// If the terminator of \p Block branches on the result of a trylock call,
/// store the call, its callee and the domain of its result in \p Res and
/// return true. For a switch statement, \p Table is set to the case table of
/// the switch statement. Otherwise \p Table is set to null and Res.TrueSet and
/// Res.FalseSet hold the results for which the first and the second successor
/// are taken.
bool ThreadSafetyAnalyzer::getTerminatorTrylockCond(
    const CFGBlock *Block, TrylockRangeCondResult &Res,
    const SwitchCaseTable *&Table,
    SmallVectorImpl<const CastExpr *> &SwitchCasts) {
  Table = nullptr;
  SwitchCasts.clear();
  if (!HasTrylockCall)
    return false;
  const Stmt *Term = Block->getTerminatorStmt();
  if (!Term || isa<IndirectGotoStmt>(Term) || UnevaluatedStmts.contains(Term))
    return false;

  // We don't acquire try-locks on ?: branches, except when its result is used.
  if (const auto *ACO = dyn_cast<AbstractConditionalOperator>(Term);
      ACO && !ACO->getType()->isVoidType())
    return false;

  const LocalVarContext &LVarCtx = BlockInfo[Block->getBlockID()].ExitContext;
  if (const auto *SS = dyn_cast<SwitchStmt>(Term)) {
    const Expr *Cond = SS->getCond();
    auto CondDom = Cond ? getScalarDomain(Cond->getType()) : std::nullopt;
    if (!CondDom)
      return false;
    LocalVarContext SubCtx = LVarCtx;
    const Expr *E = Cond;
    while ((E = skipValuePreservingWrappers(E, &SubCtx))) {
      if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
        Res.Call = CallExp;
        Res.CallCtx = SubCtx;
        break;
      }
      const auto *CE = dyn_cast<CastExpr>(E);
      if (!CE || !isBijectiveReinterpretCast(CE, *ASTCtx))
        break;
      SwitchCasts.push_back(CE);
      E = CE->getSubExpr();
    }
    Res.Callee = getTrylockCallee(Res.Call);
    if (!Res.Callee)
      return false;
    Res.Dom = getTrylockCallDomain(Res.Call);
    Table = &getSwitchCaseTable(SS, *CondDom);
    return Table->Valid;
  }
  const Stmt *Cond = Block->getTerminatorCondition();
  if (!Cond)
    return false;
  std::pair<const CFGBlock *, const void *> CacheKey(
      Block, LVarCtx.getRootWithoutRetain());
  if (auto It = TerminatorCondCache.find(CacheKey);
      It != TerminatorCondCache.end()) {
    Res = It->second.second;
    return Res.Call;
  }
  Res = evaluateTerminatorTrylockCond(Cond, LVarCtx);
  TerminatorCondCache.try_emplace(CacheKey, LVarCtx, Res);
  return Res.Call;
}
