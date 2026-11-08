//===- ThreadSafetyTrylockVerify.cpp - Try-acquire verification -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Verification that the implementation of a try-acquire function
// holds the capabilities it acquires exactly on the paths that
// return its success value.
//
//===----------------------------------------------------------------------===//

#include "ThreadSafetyInternal.h"
#include "clang/AST/ParentMap.h"
#include "llvm/ADT/ScopeExit.h"

using namespace clang;
using namespace threadSafety;

/// Return whether the analysis may lose track of the value of the trylock
/// call \p E, such that the capabilities that the call may have acquired have
/// to be taken into account separately at every function exit. That is the
/// case if the value of \p E is discarded, e.g. because \p E is an expression
/// statement, the left operand of a comma operator or the operand of a cast to
/// void, and if \p E is used in a way that is not modeled, e.g. if it is
/// stored in memory or in a variable whose value is not tracked or if it is
/// an operand of an operation that a branch condition cannot be evaluated
/// through. A value that reaches a return statement or a tracked variable is
/// not lost since return values and the definitions of tracked variables are
/// evaluated with all their operands. \p IsTrackedVar returns whether the
/// value of a local variable is tracked.
static bool isBooleanOrPointerDerivedToBaseCast(const CastExpr *CE) {
  switch (CE->getCastKind()) {
  case CK_IntegralToBoolean:
  case CK_PointerToBoolean:
  case CK_MemberPointerToBoolean:
    return true;
  case CK_DerivedToBase:
  case CK_UncheckedDerivedToBase:
    return CE->getType()->isPointerType() &&
           CE->getSubExpr()->getType()->isPointerType();
  default:
    return false;
  }
}

bool threadSafety::isDiscardedValue(
    const Expr *E, const ParentMap &PM, const ASTContext &Ctx,
    llvm::function_ref<bool(const ValueDecl *)> IsTrackedVar,
    bool *ReachedBranchCond) {
  if (ReachedBranchCond)
    *ReachedBranchCond = false;
  // Whether branch conditions, switch conditions, or relational/equality
  // comparisons can be evaluated through the operations between E and Child.
  bool BranchModeled = true;
  bool SwitchModeled = true;
  bool CmpOperandModeled = true;
  auto SetAllModeled = [&](bool Val) {
    BranchModeled = Val;
    SwitchModeled = Val;
    CmpOperandModeled = Val;
  };
  auto IsCond = [&](const Stmt *Child, const Expr *Cond, bool Modeled) {
    if (Child != Cond)
      return true;
    if (ReachedBranchCond && Modeled)
      *ReachedBranchCond = true;
    return !Modeled;
  };
  const Stmt *Child = E;
  while (const Stmt *P = PM.getParent(Child)) {
    if (isa<ParenExpr, FullExpr>(P)) {
      // Transparent.
    } else if (isa<MaterializeTemporaryExpr, CXXBindTemporaryExpr>(P)) {
      SetAllModeled(false);
    } else if (const auto *CE = dyn_cast<CastExpr>(P)) {
      if (CE->getCastKind() == CK_ToVoid)
        return true;
      if (isValuePreservingCast(CE, Ctx)) {
        // Preserves BranchModeled, SwitchModeled, and CmpOperandModeled.
      } else if (isBijectiveReinterpretCast(CE, Ctx)) {
        CmpOperandModeled = false;
      } else if (isBooleanOrPointerDerivedToBaseCast(CE)) {
        SwitchModeled = false;
        CmpOperandModeled = false;
      } else {
        SetAllModeled(false);
      }
    } else if (const auto *BO = dyn_cast<BinaryOperator>(P)) {
      if (BO->getOpcode() == BO_Comma) {
        if (Child == BO->getLHS())
          return true;
        SetAllModeled(false);
      } else if (BO->getOpcode() == BO_Assign) {
        if (Child != BO->getRHS())
          return true;
        if (const DeclRefExpr *DRE = unwrapDirectLValueDRE(BO->getLHS());
            DRE && IsTrackedVar(DRE->getDecl()))
          return false;
        if (BO->getLHS()->refersToBitField())
          SetAllModeled(false);
        else
          SwitchModeled = false;
      } else if (BO->isAssignmentOp()) {
        return true;
      } else if (BO->isRelationalOp() || BO->isEqualityOp()) {
        const Expr *Other = Child == BO->getLHS() ? BO->getRHS() : BO->getLHS();
        if (!Other->isValueDependent() && !Other->isEvaluatable(Ctx)) {
          SetAllModeled(false);
        } else if (BO->isRelationalOp() && !CmpOperandModeled) {
          SetAllModeled(false);
        } else {
          SwitchModeled = false;
          CmpOperandModeled = false;
        }
      } else if (BO->isLogicalOp()) {
        SwitchModeled = false;
        CmpOperandModeled = false;
      } else {
        SetAllModeled(false);
      }
    } else if (const auto *UO = dyn_cast<UnaryOperator>(P)) {
      if (UO->getOpcode() == UO_LNot) {
        SwitchModeled = false;
        CmpOperandModeled = false;
      } else {
        SetAllModeled(false);
      }
    } else if (const auto *CO = dyn_cast<AbstractConditionalOperator>(P)) {
      // A conditional operator whose value is used is not a branch whose
      // condition acquires capabilities.
      if (Child == CO->getCond() && CO->getType()->isVoidType())
        return IsCond(Child, CO->getCond(), BranchModeled);
      bool CondModeled = false;
      if (const auto *COP = dyn_cast<ConditionalOperator>(CO)) {
        bool TCond = false, FCond = false;
        CondModeled = Child == COP->getCond() &&
                      getStaticBooleanValue(COP->getTrueExpr(), Ctx, TCond) &&
                      getStaticBooleanValue(COP->getFalseExpr(), Ctx, FCond) &&
                      TCond != FCond;
      } else if (const auto *BCOP = dyn_cast<BinaryConditionalOperator>(CO)) {
        bool FCond = false;
        CondModeled = Child == BCOP->getCommon() &&
                      getStaticBooleanValue(BCOP->getFalseExpr(), Ctx, FCond) &&
                      !FCond;
      }
      if (!CondModeled) {
        SetAllModeled(false);
      } else {
        SwitchModeled = false;
        CmpOperandModeled = false;
      }
    } else if (const auto *CS = dyn_cast<CompoundStmt>(P)) {
      // Only the value of the last statement of a statement expression is
      // used.
      const Stmt *GP = PM.getParent(CS);
      if (!GP || !isa<StmtExpr>(GP) || CS->body_back() != Child)
        return true;
      if (CS->size() > 1 && !extractPureStmtExpr(cast<StmtExpr>(GP), Ctx)) {
        SwitchModeled = false;
        CmpOperandModeled = false;
      }
      P = GP;
    } else if (const auto *Call = dyn_cast<CallExpr>(P)) {
      if (!isBuiltinExpectCall(Call) || Child != Call->getArg(0))
        SetAllModeled(false);
    } else if (isa<Expr>(P)) {
      SetAllModeled(false);
    } else if (isa<ReturnStmt>(P)) {
      return false;
    } else if (const auto *DS = dyn_cast<DeclStmt>(P)) {
      for (const Decl *D : DS->decls())
        if (const auto *VD = dyn_cast<VarDecl>(D); VD && VD->getInit() == Child)
          return !IsTrackedVar(VD);
      return true;
    } else if (const auto *IS = dyn_cast<IfStmt>(P)) {
      return IsCond(Child, IS->getCond(), BranchModeled);
    } else if (const auto *WS = dyn_cast<WhileStmt>(P)) {
      return IsCond(Child, WS->getCond(), BranchModeled);
    } else if (const auto *DoS = dyn_cast<DoStmt>(P)) {
      return IsCond(Child, DoS->getCond(), BranchModeled);
    } else if (const auto *FS = dyn_cast<ForStmt>(P)) {
      return IsCond(Child, FS->getCond(), BranchModeled);
    } else if (const auto *SS = dyn_cast<SwitchStmt>(P)) {
      return IsCond(Child, SS->getCond(), SwitchModeled);
    } else {
      return true;
    }
    Child = P;
  }
  return true;
}

static bool hasModifiedLocalPointerRef(const Stmt *S,
                                       const LocalVariableMap &VMap,
                                       LocalVarContext Ctx) {
  if (!S)
    return false;
  if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
        VD && VD->hasLocalStorage() && !isa<ParmVarDecl>(VD) &&
        VD->getType()->isPointerType()) {
      LocalVarContext TmpCtx = Ctx;
      if (!VD->getInit() || VMap.lookupValueExpr(VD, TmpCtx) != VD->getInit())
        return true;
    }
  }
  for (const Stmt *Child : S->children())
    if (hasModifiedLocalPointerRef(Child, VMap, Ctx))
      return true;
  return false;
}

/// Add the capabilities acquired by the trylock call and attribute \p Key to
/// \p Caps.
void TrylockBodyVerifier::getAcquiredTrylockCaps(const AcquiredTrylockKey &Key,
                                                 CapExprSet &Caps) {
  const auto *Callee = dyn_cast_or_null<NamedDecl>(Key.first->getCalleeDecl());
  if (!Callee)
    return;
  std::optional<LocalVarLookupScope> Lookup;
  if (auto It = DiscardedCallCtx.find(Key.first); It != DiscardedCallCtx.end())
    Lookup.emplace(Analyzer, It->second);
  Analyzer.getTrylockMutexIDs(Caps, Key.second, Key.first, Callee);
}

bool TrylockBodyVerifier::isPureExitBlock(const CFGBlock *B,
                                          const CapExprSet &TargetCaps) {
  unsigned CtxIdx = Analyzer.BlockInfo[B->getBlockID()].EntryIndex;
  LocalVarContext StmtCtx = Analyzer.BlockInfo[B->getBlockID()].EntryContext;

  auto CheckCalleeDisjoint = [&](const NamedDecl *Callee, const Expr *Exp,
                                 til::SExpr *Self, LocalVarContext LookupCtx,
                                 bool AllowAcquire = false,
                                 bool AllowRelease = true) -> bool {
    if (!Callee)
      return false;
    if (const auto *FD = dyn_cast<FunctionDecl>(Callee))
      for (const ParmVarDecl *P : FD->parameters())
        if (P->hasAttrs())
          return false;

    LocalVarLookupScope Lookup(Analyzer, LookupCtx);

    auto CheckCapDisjoint = [&](Expr *Arg) -> bool {
      CapabilityExpr Cp =
          Analyzer.SxBuilder.translateAttrExpr(Arg, Callee, Exp, Self);
      if (Cp.isInvalid())
        return false;
      if (Cp.shouldIgnore())
        return true;
      return llvm::none_of(
          TargetCaps, [&](const CapabilityExpr &TC) { return TC.equals(Cp); });
    };
    // Whether the capabilities that attribute A names are disjoint from
    // TargetCaps.
    auto CheckArgsDisjoint = [&](const auto *A) {
      if (A->args_size() == 0)
        return (Self || isa<CXXMethodDecl>(Callee)) &&
               CheckCapDisjoint(nullptr);
      return llvm::all_of(A->args(), CheckCapDisjoint);
    };

    for (const Attr *At : Callee->attrs()) {
      switch (At->getKind()) {
      case attr::AcquireCapability:
        if (!AllowAcquire ||
            !CheckArgsDisjoint(cast<AcquireCapabilityAttr>(At)))
          return false;
        break;
      case attr::TryAcquireCapability:
      case attr::TryAcquireCapabilityRange:
      case attr::AssertCapability:
      case attr::LocksExcluded:
        return false;
      case attr::ReleaseCapability:
        if (!AllowRelease ||
            !CheckArgsDisjoint(cast<ReleaseCapabilityAttr>(At)))
          return false;
        break;
      case attr::RequiresCapability:
        if (!CheckArgsDisjoint(cast<RequiresCapabilityAttr>(At)))
          return false;
        break;
      default:
        break;
      }
    }
    return true;
  };

  for (const CFGElement &BI : *B) {
    switch (BI.getKind()) {
    case CFGElement::Statement: {
      const Stmt *S = BI.castAs<CFGStmt>().getStmt();
      if (Analyzer.UnevaluatedStmts.contains(S))
        break;
      llvm::scope_exit AdvanceCtx([&] {
        StmtCtx = Analyzer.LocalVarMap.getNextContext(CtxIdx, S, StmtCtx);
      });

      if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
        if (hasThreadSafetyCallEffects(CCE->getConstructor(), CCE))
          return false;
        break;
      }

      const auto *CE = dyn_cast<CallExpr>(S);
      if (!CE)
        break;

      if (isBuiltinExpectCall(CE))
        break;

      const auto *Callee = dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
      if (!hasThreadSafetyCallEffects(Callee, CE))
        break;

      if (!Callee)
        return false;
      if (const auto *TagT = CE->getType()->getAs<TagType>())
        if (isScopedLockable(TagT->getDecl()))
          return false;
      if (const auto *MD = dyn_cast<CXXMethodDecl>(Callee))
        if (isScopedLockable(MD->getParent()))
          return false;

      if (!CheckCalleeDisjoint(Callee, CE, /*Self=*/nullptr, StmtCtx))
        return false;
      break;
    }
    case CFGElement::AutomaticObjectDtor:
    case CFGElement::CleanupFunction: {
      std::optional<ScopeExitCall> Call = Analyzer.getScopeExitCall(BI);
      if (!Call ||
          !hasThreadSafetyCallEffects(Call->Callee, /*CallOrCtor=*/nullptr))
        break;
      if (!CheckCalleeDisjoint(Call->Callee, /*Exp=*/nullptr, Call->Self,
                               StmtCtx))
        return false;
      if (const auto *DD = dyn_cast<CXXDestructorDecl>(Call->Callee);
          DD && isScopedLockable(DD->getParent())) {
        const VarDecl *VD = BI.castAs<CFGAutomaticObjDtor>().getVarDecl();
        const Expr *InitE = VD ? VD->getInit() : nullptr;
        if (!InitE)
          return false;
        InitE = InitE->IgnoreParens();
        if (const auto *EWC = dyn_cast<ExprWithCleanups>(InitE))
          InitE = EWC->getSubExpr()->IgnoreParens();
        InitE = unpackConstruction(InitE);
        if (hasModifiedLocalPointerRef(InitE, Analyzer.LocalVarMap, StmtCtx))
          return false;
        const NamedDecl *InitCallee = nullptr;
        if (const auto *CCE = dyn_cast<CXXConstructExpr>(InitE))
          InitCallee = CCE->getConstructor();
        else if (const auto *CE = dyn_cast<CallExpr>(InitE))
          InitCallee = dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
        if (!CheckCalleeDisjoint(InitCallee, InitE, /*Self=*/nullptr, StmtCtx,
                                 /*AllowAcquire=*/true,
                                 /*AllowRelease=*/false))
          return false;
      }
      break;
    }
    case CFGElement::TemporaryDtor: {
      // Destroying a temporary does not affect the lockset unless its
      // destructor has thread safety attributes.
      const CXXDestructorDecl *DD =
          BI.castAs<CFGTemporaryDtor>().getDestructorDecl(*Analyzer.ASTCtx);
      if (!DD || isScopedLockable(DD->getParent()) ||
          hasThreadSafetyCallEffects(DD, /*CallOrCtor=*/nullptr))
        return false;
      break;
    }
    default:
      return false;
    }
  }
  return true;
}

void TrylockBodyVerifier::addLockToExpectedSet(FactSet &Set,
                                               const CapabilityExpr &Lock,
                                               LockKind LK,
                                               SourceLocation Loc) {
  if (Lock.shouldIgnore())
    return;
  if (auto It = Set.findLockIter(Analyzer.FactMan, Lock); It != Set.end()) {
    const auto &Existing = Analyzer.FactMan[*It];
    if (const auto *LFE = dyn_cast<LockableFactEntry>(&Existing)) {
      if (const FactEntry *RFact = LFE->tryReenter(Analyzer.FactMan, LK)) {
        Set.replaceLock(Analyzer.FactMan, It, RFact);
        return;
      }
    }
    if (Existing.kind() == LK_Shared && LK == LK_Exclusive)
      Set.replaceLock(Analyzer.FactMan, It,
                      Analyzer.FactMan.createFact<LockableFactEntry>(
                          Lock, LK_Exclusive, Loc));
    return;
  }
  Set.removeLock(Analyzer.FactMan, !Lock);
  Set.addLock(Analyzer.FactMan,
              Analyzer.FactMan.createFact<LockableFactEntry>(Lock, LK, Loc));
}

bool TrylockBodyVerifier::factSetsEquivalent(const FactSet &A,
                                             const FactSet &B) const {
  ptrdiff_t SizeA = A.end() - A.begin();
  ptrdiff_t SizeB = B.end() - B.begin();
  if (SizeA != SizeB)
    return false;
  if (SizeA == 0)
    return true;
  auto SameAttrs = [](const FactEntry &FA, const FactEntry &FB) {
    if (FA.getFactEntryKind() != FB.getFactEntryKind() ||
        FA.kind() != FB.kind() || FA.negative() != FB.negative() ||
        FA.asserted() != FB.asserted())
      return false;
    return getFactReentrancyDepth(FA) == getFactReentrancyDepth(FB);
  };
  if (SizeA <= 16) {
    auto FactMatchesIn = [&](const FactEntry &FA,
                             const FactSet &Other) -> bool {
      const FactEntry *FB = Other.findLock(Analyzer.FactMan, FA);
      return FB && SameAttrs(FA, *FB);
    };
    for (FactID ID : A)
      if (!FactMatchesIn(Analyzer.FactMan[ID], B))
        return false;
    for (FactID ID : B)
      if (!FactMatchesIn(Analyzer.FactMan[ID], A))
        return false;
    return true;
  }
  llvm::DenseMap<const ValueDecl *, SmallVector<const FactEntry *, 2>> BByDecl;
  SmallVector<const FactEntry *, 4> BNoDecl;
  for (FactID ID : B) {
    const FactEntry &FB = Analyzer.FactMan[ID];
    if (const ValueDecl *VD = FB.valueDecl())
      BByDecl[VD].push_back(&FB);
    else
      BNoDecl.push_back(&FB);
  }
  for (FactID ID : A) {
    const FactEntry &FA = Analyzer.FactMan[ID];
    const auto &Bucket =
        FA.valueDecl() ? BByDecl.lookup(FA.valueDecl()) : BNoDecl;
    if (!llvm::any_of(Bucket, [&](const FactEntry *FB) {
          return FB->matches(FA) && SameAttrs(FA, *FB);
        }))
      return false;
  }
  return true;
}

void TrylockBodyVerifier::constrainValueStateOnEdge(TrylockValueState &State,
                                                    const CFGBlock *PredBlock,
                                                    const CFGBlock *CurrBlock) {
  constrainValueStateOnEdgeImpl(State, PredBlock, CurrBlock);
  // The condition of a statement terminator is consumed by the edge. Drop its
  // range to keep the value state small.
  const Stmt *Term = PredBlock->getTerminatorStmt();
  if (!State.Infeasible && Term) {
    if (isa<IfStmt, WhileStmt, DoStmt, ForStmt, SwitchStmt>(Term)) {
      if (const auto *Cond = dyn_cast_or_null<Expr>(
              PredBlock->getTerminatorCondition(/*Strip=*/false)))
        State.ExprRanges.erase(stripNoOpExprWrappers(Cond));
    } else if (const auto *TermBO = dyn_cast<BinaryOperator>(Term);
               TermBO && TermBO->isLogicalOp() &&
               State.ExprRanges.size() > 16) {
      if (const auto *RawCond =
              dyn_cast_or_null<Expr>(PredBlock->getTerminatorCondition())) {
        const Expr *LeafCond = stripNoOpExprWrappers(RawCond);
        while (const auto *BO = dyn_cast<BinaryOperator>(LeafCond)) {
          if (!BO->isLogicalOp())
            break;
          LeafCond = stripNoOpExprWrappers(BO->getRHS());
        }
        State.ExprRanges.erase(LeafCond);
      }
    }
  }
}

void TrylockBodyVerifier::constrainValueStateOnEdgeImpl(
    TrylockValueState &State, const CFGBlock *PredBlock,
    const CFGBlock *CurrBlock) {
  if (State.Infeasible)
    return;

  const Stmt *Term = PredBlock->getTerminatorStmt();
  if (!Term || isa<IndirectGotoStmt>(Term) ||
      Analyzer.UnevaluatedStmts.contains(Term))
    return;

  if (const auto *SS = dyn_cast<SwitchStmt>(Term)) {
    const Expr *Cond = SS->getCond();
    auto CondDom =
        Cond ? Analyzer.getScalarDomain(Cond->getType()) : std::nullopt;
    if (!CondDom)
      return;
    const SwitchCaseTable &Table = Analyzer.getSwitchCaseTable(SS, *CondDom);
    if (!Table.Valid)
      return;
    const IntRangeSet CondEdgeSet = getSwitchEdgeSet(Table, CurrBlock);

    SmallVector<const CastExpr *, 2> SwitchCasts;
    const Expr *SubE = Cond;
    const ValueDecl *VD = nullptr;
    while (SubE) {
      if ((VD = Analyzer.extractTrackableVarExpr(SubE, EscapedVars)))
        break;
      SubE = Analyzer.skipValuePreservingWrappers(SubE, /*C=*/nullptr,
                                                  /*IgnoreSideEffects=*/false);
      const auto *CE = dyn_cast_or_null<CastExpr>(SubE);
      if (!CE || !isBijectiveReinterpretCast(CE, *Analyzer.ASTCtx))
        break;
      SwitchCasts.push_back(CE);
      SubE = CE->getSubExpr();
    }
    if (VD) {
      if (auto VarDom = Analyzer.getScalarDomain(VD->getType())) {
        IntRangeSet MappedEdge = mapRangeBackwardThroughBijectiveCasts(
            CondEdgeSet, SwitchCasts, *VarDom, *Analyzer.ASTCtx);
        restrictVarRange(State, VD, *VarDom, MappedEdge);
        if (State.Infeasible)
          return;
      }
    }
    const Expr *StrippedCond = stripNoOpExprWrappers(Cond);
    IntRangeSet CondEdge = CondEdgeSet;
    if (auto Cur = Analyzer.evaluatePureExprRange(StrippedCond, State,
                                                  RangeEvalCtx{&EscapedVars}))
      CondEdge = CondEdge.intersect(*Cur);
    if (CondEdge.empty()) {
      State.Infeasible = true;
      return;
    }
    State.ExprRanges[StrippedCond] = std::move(CondEdge);
    return;
  }

  const auto *RawCond =
      dyn_cast_or_null<Expr>(PredBlock->getTerminatorCondition());
  if (!RawCond)
    return;

  auto [MatchesTrue, MatchesFalse] = getBranchEdgeKinds(PredBlock, CurrBlock);
  if (MatchesTrue == MatchesFalse)
    return;

  bool TakeTrue = MatchesTrue;
  if (const auto *TermBO = dyn_cast<BinaryOperator>(Term)) {
    const BinaryOperator *TargetBO = nullptr;
    if (CurrBlock) {
      for (const CFGElement &BI : *CurrBlock) {
        if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
          if (const auto *ConfBO = dyn_cast<BinaryOperator>(CS->getStmt());
              ConfBO && ConfBO->getOpcode() == TermBO->getOpcode())
            TargetBO = ConfBO;
          break;
        }
      }
    }
    if (!TargetBO && ValueLogicalOps.contains(TermBO))
      TargetBO = TermBO;
    if (TargetBO) {
      if (TermBO->getOpcode() == BO_LAnd && !TakeTrue)
        State.ShortCircuitedOps[TargetBO] = false;
      else if (TermBO->getOpcode() == BO_LOr && TakeTrue)
        State.ShortCircuitedOps[TargetBO] = true;
    }
  }

  const Expr *StrippedRaw = stripNoOpExprWrappers(RawCond);
  if (const auto *StrippedBO = dyn_cast<BinaryOperator>(StrippedRaw);
      StrippedBO && StrippedBO->isLogicalOp()) {
    if (auto It = State.ShortCircuitedOps.find(StrippedBO);
        It != State.ShortCircuitedOps.end()) {
      if (It->second != TakeTrue)
        State.Infeasible = true;
      return;
    }
  }
  // Unlike IfStmt/WhileStmt/ForStmt (whose condition is lowered with
  // VisitLogicalOperator so PredBlock only evaluates the rightmost leaf),
  // CFGBuilder::VisitDoStmt calls addStmt(D->getCond()), so PredBlock is the
  // confluence block of the full DoStmt condition.
  if (isa<DoStmt>(Term)) {
    Analyzer.constrainLeafCondition(State, StrippedRaw, TakeTrue,
                                    RangeEvalCtx{&EscapedVars});
    return;
  }

  // In Clang's linearized CFG, PredBlock evaluated the rightmost leaf of any
  // top-level && / || chain in RawCond.
  const Expr *LeafCond = StrippedRaw;
  while (const auto *BO = dyn_cast<BinaryOperator>(LeafCond)) {
    if (!BO->isLogicalOp())
      break;
    LeafCond = stripNoOpExprWrappers(BO->getRHS());
  }

  Analyzer.constrainLeafCondition(State, LeafCond, TakeTrue,
                                  RangeEvalCtx{&EscapedVars});
}

void TrylockBodyVerifier::materializeNarrowedTrylocks(
    FactSet &Lockset, TrylockValueState &State) {
  if (State.Infeasible || State.UnmaterializedVarDefs.empty())
    return;

  auto UnwrapDirectTrylockCall =
      [&](const Expr *E, LocalVarContext &Ctx, QualType VarTy,
          IntRangeSet &CallRange, bool &PreservesExactInt) -> const CallExpr * {
    PreservesExactInt = true;
    while ((E = Analyzer.skipValuePreservingWrappers(E, &Ctx))) {
      if (const auto *CallExp = dyn_cast<CallExpr>(E))
        return CallExp;
      const auto *CE = dyn_cast<CastExpr>(E);
      if (!CE)
        return nullptr;
      if (isBijectiveReinterpretCast(CE, *Analyzer.ASTCtx)) {
        if (PreservesExactInt) {
          QualType DstScalarTy = CE->getType()->isAnyPointerType()
                                     ? Analyzer.ASTCtx->getUIntPtrType()
                                     : CE->getType();
          QualType SrcScalarTy = CE->getSubExpr()->getType()->isAnyPointerType()
                                     ? Analyzer.ASTCtx->getUIntPtrType()
                                     : CE->getSubExpr()->getType();
          IntDomain DstDom = IntDomain::forType(DstScalarTy, *Analyzer.ASTCtx);
          CallRange = castIntegralRangeSet(reprojectRangeSet(CallRange, DstDom),
                                           SrcScalarTy, *Analyzer.ASTCtx);
        }
        E = CE->getSubExpr();
        continue;
      }
      // Casts that preserve whether the value is zero, but not the value.
      switch (CE->getCastKind()) {
      case CK_DerivedToBase:
      case CK_UncheckedDerivedToBase:
        if (!CE->getType()->isAnyPointerType() ||
            !CE->getSubExpr()->getType()->isAnyPointerType())
          return nullptr;
        break;
      case CK_IntegralToBoolean:
      case CK_PointerToBoolean:
      case CK_MemberPointerToBoolean:
        if (!VarTy->isBooleanType())
          return nullptr;
        break;
      default:
        return nullptr;
      }
      PreservesExactInt = false;
      E = CE->getSubExpr();
    }
    return nullptr;
  };

  for (const auto &[VD, DefPair] : State.UnmaterializedVarDefs) {
    auto VR = State.VarRanges.find(VD);
    if (VR == State.VarRanges.end() || VR->second.empty())
      continue;
    auto VarDom = Analyzer.getScalarDomain(VD->getType());
    if (!VarDom)
      continue;
    IntRangeSet CallRange = VR->second;
    bool PreservesExactInt = false;
    LocalVarContext CallCtx = DefPair.second;
    const CallExpr *CallExp = UnwrapDirectTrylockCall(
        DefPair.first, CallCtx, VD->getType(), CallRange, PreservesExactInt);
    if (!CallExp)
      continue;
    const auto *Callee = dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl());
    if (!Callee)
      continue;

    LocalVarLookupScope Lookup(Analyzer, CallCtx);

    CapExprSet ExclusiveLocksToAdd;
    CapExprSet SharedLocksToAdd;

    // A range attribute only applies if the variable holds the exact result
    // of the call.
    bool ExactInt = PreservesExactInt &&
                    isRangeTrylockReturnType(CallExp->getType()) &&
                    isRangeTrylockReturnType(VD->getType());
    IntDomain EvalDom =
        PreservesExactInt ? Analyzer.getTrylockCallDomain(CallExp) : *VarDom;
    if (PreservesExactInt)
      CallRange = reprojectRangeSet(CallRange, EvalDom);
    for (const Attr *A : trylockAttrs(Callee)) {
      if (!trylockAttrAppliesTo(A, CallExp->getType()))
        continue;
      if (isa<TryAcquireCapabilityRangeAttr>(A) && !ExactInt)
        continue;
      if (State.AcquiredTrylockAttrs.contains({CallExp, A}))
        continue;
      auto SuccSet = Analyzer.getCombinedTrylockSuccessSet(A, CallExp, Callee,
                                                           EvalDom, ExactInt);
      if (SuccSet && !CallRange.empty() && CallRange.subsetOfSet(*SuccSet) &&
          Analyzer.collectTrylockCaps(A, CallExp, Callee, ExclusiveLocksToAdd,
                                      SharedLocksToAdd)) {
        State.AcquiredTrylockAttrs.insert({CallExp, A});
        DiscardedCallCtx.try_emplace(CallExp, CallCtx);
      }
    }

    Analyzer.addTrylockFacts(Lockset, ExclusiveLocksToAdd, SharedLocksToAdd,
                             CallExp->getExprLoc());
  }
}

const ValueDecl *
TrylockBodyVerifier::getDereferencedPtrExprVar(const Expr *PtrE) const {
  while (PtrE) {
    PtrE = stripNoOpExprWrappers(PtrE);
    if (const auto *CE = dyn_cast<CastExpr>(PtrE)) {
      QualType SubTy = CE->getSubExpr()->getType();
      QualType DstTy = CE->getType();
      if (CE->getCastKind() == CK_LValueToRValue) {
        PtrE = CE->getSubExpr();
        continue;
      }
      if ((CE->getCastKind() == CK_BitCast ||
           CE->getCastKind() == CK_DerivedToBase ||
           CE->getCastKind() == CK_UncheckedDerivedToBase) &&
          DstTy->isAnyPointerType() && SubTy->isAnyPointerType()) {
        PtrE = CE->getSubExpr();
        continue;
      }
      return nullptr;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(PtrE)) {
      if (isBuiltinExpectCall(CallExp)) {
        PtrE = CallExp->getArg(0);
        continue;
      }
      return nullptr;
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(PtrE)) {
      const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      if (!VD || !VD->getType()->isAnyPointerType() ||
          !Analyzer.isTrackableLocalVar(VD, EscapedVars))
        return nullptr;
      return VD;
    }
    return nullptr;
  }
  return nullptr;
}

const ValueDecl *
TrylockBodyVerifier::getAccessedLValuePtrVar(const Expr *LV) const {
  while (LV) {
    LV = LV->IgnoreParens();
    if (const auto *CE = dyn_cast<CastExpr>(LV)) {
      if (CE->getCastKind() == CK_NoOp ||
          CE->getCastKind() == CK_DerivedToBase ||
          CE->getCastKind() == CK_UncheckedDerivedToBase) {
        LV = CE->getSubExpr();
        continue;
      }
    }
    if (const auto *ME = dyn_cast<MemberExpr>(LV)) {
      if (!isa<FieldDecl, IndirectFieldDecl>(ME->getMemberDecl()))
        return nullptr;
      if (ME->isArrow())
        return getDereferencedPtrExprVar(ME->getBase());
      LV = ME->getBase();
      continue;
    }
    if (const auto *UO = dyn_cast<UnaryOperator>(LV)) {
      if (UO->getOpcode() == UO_Deref && !UO->getType()->isFunctionType())
        return getDereferencedPtrExprVar(UO->getSubExpr());
      return nullptr;
    }
    if (const auto *ASE = dyn_cast<ArraySubscriptExpr>(LV)) {
      const Expr *Base = ASE->getBase()->IgnoreParens();
      if (const auto *CE = dyn_cast<CastExpr>(Base);
          CE && CE->getCastKind() == CK_ArrayToPointerDecay) {
        LV = CE->getSubExpr();
        continue;
      }
      return getDereferencedPtrExprVar(Base);
    }
    return nullptr;
  }
  return nullptr;
}

const ValueDecl *
TrylockBodyVerifier::getDereferencedPtrInStmt(const Stmt *S) const {
  if (!S)
    return nullptr;

  // The thread safety analysis builds its CFG with all statements added as
  // separate CFG elements (setAllAlwaysAdd()), and this function is called
  // for each element in execution order. Hence, only examine S itself and not
  // its subexpressions. This evaluates each dereference against the pointer
  // value at the time of the dereference and visits each AST node only once.
  // Most statements in unevaluated contexts are not CFG elements. The
  // arguments of builtins like __builtin_constant_p() are CFG elements but
  // updateValueStateForStmt() skips these.
  const ValueDecl *VD = nullptr;
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (CE->isUnevaluatedBuiltinCall(*Analyzer.ASTCtx))
      return nullptr;
    if (const auto *MCE = dyn_cast<CXXMemberCallExpr>(CE)) {
      if (const CXXMethodDecl *MD = MCE->getMethodDecl();
          MD && !MD->isStatic() && !hasThreadSafetyCallEffects(MD, MCE)) {
        if (const auto *ME =
                dyn_cast<MemberExpr>(MCE->getCallee()->IgnoreParens())) {
          if (ME->isArrow())
            VD = getDereferencedPtrExprVar(ME->getBase());
          else
            VD = getAccessedLValuePtrVar(ME->getBase());
        }
      }
    } else if (const auto *OCE = dyn_cast<CXXOperatorCallExpr>(CE)) {
      OverloadedOperatorKind OOK = OCE->getOperator();
      if ((OCE->isAssignmentOp() || OOK == OO_PlusPlus ||
           OOK == OO_MinusMinus) &&
          OCE->getNumArgs() >= 1 && OCE->getArg(0)->isGLValue() &&
          !hasThreadSafetyCallEffects(
              dyn_cast_or_null<NamedDecl>(OCE->getCalleeDecl()), OCE))
        VD = getAccessedLValuePtrVar(OCE->getArg(0));
    }
  } else if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->isAssignmentOp())
      VD = getAccessedLValuePtrVar(BO->getLHS());
  } else if (const auto *UO = dyn_cast<UnaryOperator>(S)) {
    if (UO->isIncrementDecrementOp())
      VD = getAccessedLValuePtrVar(UO->getSubExpr());
  } else if (const auto *CastE = dyn_cast<CastExpr>(S)) {
    if (CastE->getCastKind() == CK_LValueToRValue)
      VD = getAccessedLValuePtrVar(CastE->getSubExpr());
  }
  return (VD && !llvm::is_contained(Analyzer.getSubtreeModifiedVars(S), VD))
             ? VD
             : nullptr;
}

/// Drop the ranges of local variables that are out of scope in \p B. Their
/// values cannot be used anymore, and dropping them keeps the size of the
/// value state proportional to the number of variables in scope. A trylock
/// result stored in such a variable is kept if the variable may still be
/// referenced by the value of a statement expression. Otherwise, it is
/// dropped if it cannot have acquired a capability, e.g. on the failure path
/// of 'if (r) return 1;', or remembered as a result that is no longer stored
/// in any variable. Without this, the results of a sequence of trylock calls
/// whose success paths return early would be forked on at every subsequent
/// return statement.
void TrylockBodyVerifier::pruneOutOfScopeVars(TrylockValueState &State,
                                              const CFGBlock *B) {
  if (State.Infeasible || !CurrentParentMap ||
      (State.VarRanges.empty() && State.UnmaterializedVarDefs.empty()))
    return;
  const Stmt *Rep = nullptr;
  for (const CFGElement &E : *B)
    if (std::optional<CFGStmt> CS = E.getAs<CFGStmt>()) {
      Rep = CS->getStmt();
      break;
    }
  if (!Rep)
    Rep = B->getTerminatorStmt();
  if (!Rep)
    return;
  auto IsAncestorOfRep = [&](const Stmt *S) {
    for (const Stmt *P = Rep; P; P = CurrentParentMap->getParent(P))
      if (P == S)
        return true;
    return false;
  };
  auto InScope = [&](const ValueDecl *VD) {
    auto It = VarScopes.find(VD);
    return It == VarScopes.end() || IsAncestorOfRep(It->second);
  };
  // Whether the value of the statement expression that is the scope of a
  // variable may still be evaluated in B, e.g. for the right-hand side of
  // 'return c && ({ bool r = trylock(&mu); r; });'. Its value may refer to
  // the variable.
  auto MayStillBeReferenced = [&](const ValueDecl *VD) {
    const Stmt *Top = VarScopes.lookup(VD);
    if (!isa_and_nonnull<StmtExpr>(Top))
      return false;
    while (const Stmt *P = CurrentParentMap->getParent(Top)) {
      if (isa<Expr, ReturnStmt>(P)) {
        Top = P;
        continue;
      }
      // A statement of an enclosing statement expression.
      if (isa<CompoundStmt>(P) &&
          isa_and_nonnull<StmtExpr>(CurrentParentMap->getParent(P))) {
        Top = CurrentParentMap->getParent(P);
        continue;
      }
      break;
    }
    return IsAncestorOfRep(Top);
  };
  SmallVector<const ValueDecl *, 4> Dead;
  for (const auto &[VD, R] : State.VarRanges)
    if (!InScope(VD) && !MayStillBeReferenced(VD))
      Dead.push_back(VD);
  SmallVector<const ValueDecl *, 4> DeadDefs;
  for (const auto &[VD, DefPair] : State.UnmaterializedVarDefs)
    if (!InScope(VD) && !MayStillBeReferenced(VD))
      DeadDefs.push_back(VD);
  // Sort for a deterministic order of the remembered results.
  llvm::sort(DeadDefs, [](const ValueDecl *A, const ValueDecl *B) {
    return A->getLocation().getRawEncoding() <
           B->getLocation().getRawEncoding();
  });
  for (const ValueDecl *VD : DeadDefs)
    retireVarDef(State, VD, /*NewRHS=*/nullptr);
  for (const ValueDecl *VD : Dead) {
    State.VarRanges.erase(VD);
    State.DerefNonNullVars.erase(VD);
  }
}

void TrylockBodyVerifier::recordStmtMetadata(const Stmt *S,
                                             LocalVarContext StmtCtx) {
  if (!S || Analyzer.UnevaluatedStmts.contains(S))
    return;
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const auto *Callee = dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
        Callee && hasTrylockAttr(Callee))
      DiscardedCallCtx.insert_or_assign(CE, StmtCtx);
    return;
  }
  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    if (CurrentParentMap) {
      if (const Stmt *Scope = CurrentParentMap->getParent(DS)) {
        // The value of a statement expression may be evaluated in a CFG block
        // after the blocks of its body.
        if (const Stmt *P = CurrentParentMap->getParent(Scope);
            isa_and_nonnull<StmtExpr>(P))
          Scope = P;
        for (const Decl *D : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(D);
              VD && VD->hasLocalStorage())
            VarScopes.try_emplace(cast<ValueDecl>(VD->getCanonicalDecl()),
                                  Scope);
      }
    }
    forEachEvaluatedDeclVLAStmt(
        DS, *Analyzer.ASTCtx, /*IncludeTopLevelVLA=*/false,
        [&](const Stmt *SubS) {
          if (const auto *CE = dyn_cast<CallExpr>(SubS))
            if (const auto *Callee =
                    dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
                Callee && hasTrylockAttr(Callee))
              DiscardedCallCtx.insert_or_assign(CE, StmtCtx);
        });
  }
}

void TrylockBodyVerifier::updateValueStateForStmt(TrylockValueState &State,
                                                  const Stmt *S,
                                                  LocalVarContext StmtCtx) {
  updateValueStateForStmtImpl(State, S, StmtCtx);
  // Once a full expression has been processed, its range is no longer needed.
  // Dropping it keeps the size of the value state independent of the size of
  // the function. Ranges of subexpressions are kept since an enclosing
  // expression may be evaluated in another CFG block, e.g. for || and ?:.
  if (State.Infeasible || !CurrentParentMap)
    return;
  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    for (const Decl *D : DS->decls())
      if (const auto *VD = dyn_cast<VarDecl>(D); VD && VD->getInit())
        State.ExprRanges.erase(stripNoOpExprWrappers(VD->getInit()));
    State.ShortCircuitedOps.clear();
    return;
  }
  if (const auto *E = dyn_cast<Expr>(S)) {
    if (const auto *SE = dyn_cast<StmtExpr>(E)) {
      if (const CompoundStmt *CS = SE->getSubStmt(); CS && !CS->body_empty())
        if (const auto *LastExpr = dyn_cast<Expr>(CS->body_back()))
          State.ExprRanges.erase(stripNoOpExprWrappers(LastExpr));
    }
    const Stmt *Parent = CurrentParentMap->getParent(S);
    if (const auto *CS = dyn_cast_if_present<CompoundStmt>(Parent)) {
      if (CS->body_back() != S ||
          !isa_and_nonnull<StmtExpr>(CurrentParentMap->getParent(CS))) {
        State.ExprRanges.erase(stripNoOpExprWrappers(E));
        State.ShortCircuitedOps.clear();
      }
    } else if (isa_and_nonnull<LabelStmt, CaseStmt, DefaultStmt,
                               AttributedStmt>(Parent)) {
      State.ExprRanges.erase(stripNoOpExprWrappers(E));
      State.ShortCircuitedOps.clear();
    }
  }
}

// Called before VD is modified. If VD holds a trylock result that is not
// stored anywhere else and that the new value \p NewRHS does not depend on,
// remember that result together with the values VD may have had.
void TrylockBodyVerifier::retireVarDef(TrylockValueState &State,
                                       const ValueDecl *VD,
                                       const Expr *NewRHS) {
  auto It = State.UnmaterializedVarDefs.find(VD);
  if (It == State.UnmaterializedVarDefs.end())
    return;
  const std::pair<const Expr *, LocalVarContext> Def = It->second;
  if (NewRHS) {
    bool Referenced = false;
    auto Visit = [&](auto &Self, const Stmt *Node) -> void {
      if (!Node || Referenced || isa<LambdaExpr, BlockExpr>(Node))
        return;
      if (const auto *DRE = dyn_cast<DeclRefExpr>(Node)) {
        const auto *RefVD = cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
        if (auto RefIt = State.UnmaterializedVarDefs.find(RefVD);
            RefIt != State.UnmaterializedVarDefs.end() &&
            RefIt->second.first == Def.first)
          Referenced = true;
      }
      for (const Stmt *Child : Node->children())
        Self(Self, Child);
    };
    Visit(Visit, NewRHS);
    if (Referenced)
      return;
  }
  std::optional<IntRangeSet> Allowed;
  if (auto VR = State.VarRanges.find(VD); VR != State.VarRanges.end())
    Allowed = VR->second;
  State.UnmaterializedVarDefs.erase(It);
  if (trylockDefMayAcquire(State, Def.first, Def.second, VD->getType(),
                           Allowed ? &*Allowed : nullptr))
    addOverwrittenTrylockDef(State,
                             makeOverwrittenTrylockDef(VD, Def, Allowed));
}

void TrylockBodyVerifier::updateVarFromExpr(TrylockValueState &State,
                                            const ValueDecl *VD,
                                            const Expr *RHS,
                                            LocalVarContext StmtCtx) {
  VD = cast<ValueDecl>(VD->getCanonicalDecl());
  retireVarDef(State, VD, RHS);
  State.DerefNonNullVars.erase(VD);
  if (!Analyzer.isTrackableLocalVar(VD, EscapedVars) || !RHS) {
    State.VarRanges.erase(VD);
    State.UnmaterializedVarDefs.erase(VD);
    return;
  }
  const ValueDecl *SrcVD = Analyzer.extractTrackableVarExpr(RHS, EscapedVars);
  if (SrcVD && State.DerefNonNullVars.contains(SrcVD))
    State.DerefNonNullVars.insert(VD);
  auto DefIt = SrcVD ? State.UnmaterializedVarDefs.find(SrcVD)
                     : State.UnmaterializedVarDefs.end();
  if (DefIt != State.UnmaterializedVarDefs.end()) {
    // Copy the definition first: inserting VD may grow the map and
    // invalidate DefIt.
    auto Def = DefIt->second;
    State.UnmaterializedVarDefs.insert_or_assign(VD, Def);
  } else if (exprHasUnmaterializedTrylock(RHS, StmtCtx, State,
                                          /*UseStateDefs=*/true)) {
    State.UnmaterializedVarDefs.insert_or_assign(VD,
                                                 std::make_pair(RHS, StmtCtx));
  } else {
    State.UnmaterializedVarDefs.erase(VD);
  }

  auto VarDom = Analyzer.getScalarDomain(VD->getType());
  auto R =
      Analyzer.evaluatePureExprRange(RHS, State, RangeEvalCtx{&EscapedVars});
  if (VarDom && R)
    State.VarRanges[VD] = reprojectRangeSet(*R, *VarDom);
  else
    State.VarRanges.erase(VD);
}

void TrylockBodyVerifier::updateValueStateForStmtImpl(TrylockValueState &State,
                                                      const Stmt *S,
                                                      LocalVarContext StmtCtx) {
  if (State.Infeasible || !S || Analyzer.UnevaluatedStmts.contains(S))
    return;

  if (const auto *E = dyn_cast<Expr>(S)) {
    // Keep ShortCircuitedOps such that the enclosing statement can read the
    // short-circuited value of a logical operator.
    State.ExprRanges.erase(stripNoOpExprWrappers(E));
    if (const auto *CE = dyn_cast<CallExpr>(E)) {
      if (DiscardedCalls.contains(CE))
        State.DiscardedTrylockCalls.insert(CE);
      SmallVector<AcquiredTrylockKey, 2> ToErase;
      for (const auto &Key : State.AcquiredTrylockAttrs)
        if (Key.first == CE)
          ToErase.push_back(Key);
      for (const auto &Key : ToErase) {
        State.AcquiredTrylockAttrs.erase(Key);
        State.ConsumedTrylockAttrs.erase(Key);
      }
    }
  }

  // Record the dereference separately instead of narrowing the range of VD
  // such that a later null check is not treated as infeasible. Code built
  // with -fno-delete-null-pointer-checks may dereference a pointer before
  // checking it.
  if (const ValueDecl *DerefVD = getDereferencedPtrInStmt(S))
    State.DerefNonNullVars.insert(DerefVD);

  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/false, [&](const Expr *Sz) {
      llvm::SmallPtrSet<const ValueDecl *, 4> ModVars;
      scanModifiedVars(Sz, *Analyzer.ASTCtx, ModVars);
      for (const ValueDecl *ModVD : ModVars) {
        retireVarDef(State, ModVD, /*NewRHS=*/nullptr);
        State.VarRanges.erase(ModVD);
        State.DerefNonNullVars.erase(ModVD);
      }
    });
    forEachEvaluatedDeclVLAStmt(DS, *Analyzer.ASTCtx,
                                /*IncludeTopLevelVLA=*/false,
                                [&](const Stmt *SubS) {
                                  if (const auto *CE = dyn_cast<CallExpr>(SubS);
                                      CE && DiscardedCalls.contains(CE))
                                    State.DiscardedTrylockCalls.insert(CE);
                                });
    for (const Decl *D : DS->decls())
      if (const auto *VD = dyn_cast<VarDecl>(D))
        updateVarFromExpr(State, VD, VD->getInit(), StmtCtx);
    return;
  }

  auto InvalidateCompoundLValue = [&](const Expr *LV) {
    SmallVector<const DeclRefExpr *, 2> DREs;
    collectModifiedLValueDREs(LV, DREs);
    for (const DeclRefExpr *ModDRE : DREs) {
      if (const auto *VD =
              dyn_cast<ValueDecl>(ModDRE->getDecl()->getCanonicalDecl())) {
        retireVarDef(State, VD, /*NewRHS=*/nullptr);
        State.DerefNonNullVars.erase(VD);
        State.VarRanges.erase(VD);
      }
    }
  };

  if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (!BO->isAssignmentOp())
      return;
    const auto *DRE = BO->getLHS()->refersToBitField()
                          ? nullptr
                          : unwrapDirectLValueDRE(BO->getLHS());
    if (!DRE) {
      InvalidateCompoundLValue(BO->getLHS());
      if (BO->getOpcode() == BO_Assign) {
        if (const FieldDecl *BF = BO->getLHS()->getSourceBitField();
            BF && BF->hasConstantIntegerBitWidth()) {
          auto BODom = Analyzer.getScalarDomain(BO->getType());
          auto R = Analyzer.evaluatePureExprRange(BO->getRHS(), State,
                                                  RangeEvalCtx{&EscapedVars});
          if (BODom && R)
            State.ExprRanges[stripNoOpExprWrappers(BO)] =
                truncateToBitField(*R, BF->getBitWidthValue(), BO->getType(),
                                   *BODom, *Analyzer.ASTCtx);
        }
      }
      return;
    }
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (!VD)
      return;
    if (BO->getOpcode() == BO_Assign) {
      updateVarFromExpr(State, VD, BO->getRHS(), StmtCtx);
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
        State.ExprRanges[stripNoOpExprWrappers(BO)] = It->second;
    } else {
      retireVarDef(State, VD, /*NewRHS=*/nullptr);
      State.DerefNonNullVars.erase(VD);
      if (Analyzer.isTrackableLocalVar(VD, EscapedVars) &&
          VD->getType()->isIntegralOrEnumerationType()) {
        auto L = Analyzer.evaluatePureExprRange(BO->getLHS(), State,
                                                RangeEvalCtx{&EscapedVars});
        auto R = Analyzer.evaluatePureExprRange(BO->getRHS(), State,
                                                RangeEvalCtx{&EscapedVars});
        llvm::APSInt LV, RV;
        if (L && R && L->isSingleValue(LV) && R->isSingleValue(RV) &&
            (BO->getOpcode() == BO_AddAssign ||
             BO->getOpcode() == BO_SubAssign)) {
          llvm::APSInt ResV = *foldIntBinOp(
              BinaryOperator::getOpForCompoundAssignment(BO->getOpcode()), LV,
              RV, VD->getType(), *Analyzer.ASTCtx);
          State.VarRanges[VD] = IntRangeSet::single(
              *Analyzer.getScalarDomain(VD->getType()), ResV);
          return;
        }
      }
      State.VarRanges.erase(VD);
    }
    return;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(S)) {
    if (!UO->isIncrementDecrementOp())
      return;
    const auto *DRE = unwrapDirectLValueDRE(UO->getSubExpr());
    if (!DRE) {
      InvalidateCompoundLValue(UO->getSubExpr());
      return;
    }
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (!VD)
      return;
    retireVarDef(State, VD, /*NewRHS=*/nullptr);
    State.DerefNonNullVars.erase(VD);
    if (Analyzer.isTrackableLocalVar(VD, EscapedVars) &&
        VD->getType()->isIntegralOrEnumerationType()) {
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end()) {
        llvm::APSInt V;
        if (It->second.isSingleValue(V)) {
          llvm::APSInt Trunc = *foldIntBinOp(
              UO->isIncrementOp() ? BO_Add : BO_Sub, V, llvm::APSInt::get(1),
              VD->getType(), *Analyzer.ASTCtx);
          auto VarDom = *Analyzer.getScalarDomain(VD->getType());
          if (UO->isPrefix())
            State.ExprRanges[stripNoOpExprWrappers(UO)] =
                IntRangeSet::single(VarDom, Trunc);
          else
            State.ExprRanges[stripNoOpExprWrappers(UO)] = It->second;
          State.VarRanges[VD] = IntRangeSet::single(VarDom, Trunc);
          return;
        }
      }
    }
    State.VarRanges.erase(VD);
    return;
  }

  if (const auto *AS = dyn_cast<AsmStmt>(S)) {
    for (unsigned I = 0, N = AS->getNumOutputs(); I < N; ++I)
      InvalidateCompoundLValue(AS->getOutputExpr(I)->IgnoreParenCasts());
    return;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(S)) {
    if (const CompoundStmt *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
      if (const auto *LastExpr = dyn_cast<Expr>(CS->body_back())) {
        if (auto Dom = Analyzer.getScalarDomain(SE->getType())) {
          auto R = Analyzer.evaluatePureExprRange(LastExpr, State,
                                                  RangeEvalCtx{&EscapedVars});
          auto RDeref = Analyzer.evaluatePureExprRange(
              LastExpr, State,
              RangeEvalCtx{&EscapedVars, /*AssumeDerefValid=*/true});
          const bool Same =
              (!R && !RDeref) || (R && RDeref && R->subsetOfSet(*RDeref) &&
                                  RDeref->subsetOfSet(*R));
          if (Same) {
            State.ExprRanges[stripNoOpExprWrappers(SE)] =
                R ? reprojectRangeSet(*R, *Dom) : IntRangeSet::full(*Dom);
          }
        }
      }
    }
  }
}

/// The maximum number of expressions that exprHasUnmaterializedTrylock()
/// visits per query.
static constexpr unsigned MaxTrylockScanSteps = 1u << 16;

bool TrylockBodyVerifier::exprHasUnmaterializedTrylock(
    const Expr *E, LocalVarContext Ctx, const TrylockValueState &State,
    bool UseStateDefs, bool IncludeMaterialized,
    llvm::SmallPtrSetImpl<const CallExpr *> *Calls) {
  // Walk the expression and the definitions of the variables that it refers
  // to. Visit each (expression, context) pair once such that the time is
  // linear in the number of definitions even if the definitions form a DAG,
  // and use a worklist instead of recursion such that long definition chains
  // cannot exhaust the stack. If the walk exceeds its budget, answer that E
  // may contain a trylock call: answering "no" would make the callers forget
  // the capabilities that such a call may acquire.
  if (InReturnEval && ReturnEvalExhausted)
    return true;
  struct WorkItem {
    const Expr *E;
    LocalVarContext Ctx;
    bool UseStateDefs;
  };
  SmallVector<WorkItem, 8> Worklist;
  llvm::SmallDenseSet<std::tuple<const Expr *, const void *, unsigned>, 8>
      Visited;
  unsigned LocalSteps = MaxTrylockScanSteps;
  unsigned &Steps = InReturnEval ? ReturnScanSteps : LocalSteps;
  bool Found = false;
  Worklist.push_back({E, Ctx, UseStateDefs});
  while (!Worklist.empty()) {
    WorkItem I = Worklist.pop_back_val();
    if (!I.E || Analyzer.UnevaluatedStmts.contains(I.E))
      continue;
    const Expr *Cur = stripNoOpExprWrappers(I.E);
    if (Analyzer.UnevaluatedStmts.contains(Cur) ||
        !Visited.insert({Cur, I.Ctx.getRootWithoutRetain(), I.UseStateDefs})
             .second)
      continue;
    if (Steps-- == 0) {
      ReturnEvalExhausted = true;
      return true;
    }
    auto Push = [&](const Expr *SubE) {
      Worklist.push_back({SubE, I.Ctx, I.UseStateDefs});
    };

    if (const auto *BO = dyn_cast<BinaryOperator>(Cur)) {
      if (BO->isLogicalOp() && I.UseStateDefs &&
          State.ShortCircuitedOps.contains(BO))
        continue;
      if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign) {
        Push(BO->getRHS());
        continue;
      }
    }

    if (const auto *CallExp = dyn_cast<CallExpr>(Cur)) {
      if (CallExp->isUnevaluatedBuiltinCall(*Analyzer.ASTCtx))
        continue;
      if (isBuiltinExpectCall(CallExp)) {
        Push(CallExp->getArg(0));
        continue;
      }
      if (const auto *Callee =
              dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl())) {
        for (const Attr *A : trylockAttrs(Callee)) {
          if (trylockAttrAppliesTo(A, CallExp->getType()) &&
              (IncludeMaterialized ||
               !State.AcquiredTrylockAttrs.contains({CallExp, A}))) {
            if (!Calls)
              return true;
            Calls->insert(CallExp);
            Found = true;
            break;
          }
        }
      }
      for (const Expr *Arg : CallExp->arguments())
        Push(Arg);
      continue;
    }

    if (const auto *DRE = dyn_cast<DeclRefExpr>(Cur)) {
      const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      if (I.UseStateDefs && VD) {
        if (auto It = State.UnmaterializedVarDefs.find(VD);
            It != State.UnmaterializedVarDefs.end()) {
          Worklist.push_back(
              {It->second.first, It->second.second, /*UseStateDefs=*/false});
          continue;
        }
        if (State.VarRanges.contains(VD))
          continue;
      }
      LocalVarContext SubCtx = I.Ctx;
      if (const Expr *DefE =
              Analyzer.LocalVarMap.lookupValueExpr(DRE->getDecl(), SubCtx))
        Worklist.push_back({DefE, SubCtx, /*UseStateDefs=*/false});
      continue;
    }

    if (const auto *SE = dyn_cast<StmtExpr>(Cur)) {
      if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty())
        if (const auto *Last = dyn_cast<Expr>(CS->body_back()))
          Push(Last);
      continue;
    }

    for (const Stmt *Child : Cur->children())
      if (const auto *ChildE = dyn_cast_or_null<Expr>(Child))
        Push(ChildE);
  }
  return Found;
}

/// The maximum number of distinct outcomes that evaluateReturnOutcomes()
/// produces for a single expression.
static constexpr unsigned MaxReturnOutcomes = 64;

/// The maximum number of evaluateReturnOutcomes() calls per verified return
/// value. Bounds the time spent on return values whose evaluation would fork
/// into exponentially many outcomes, e.g. nested conditional operators whose
/// operands contain many trylock calls.
static constexpr unsigned MaxReturnEvalSteps = 4096;

/// Add the capabilities that the trylock calls in \p E acquire on success to
/// \p Out, following the definitions of the variables that \p E refers to.
/// Calls whose capabilities are already held according to \p State are
/// skipped. Expressions in \p Visited are skipped and the visited expressions
/// are added to \p Visited.
void TrylockBodyVerifier::collectTrylockAcquires(
    const Expr *E, LocalVarContext Ctx, const TrylockValueState &State,
    bool UseStateDefs, SmallVectorImpl<PendingTrylockAcquire> &Out,
    llvm::SmallPtrSetImpl<const Expr *> &Visited, unsigned Depth) {
  auto AddPending = [&](const PendingTrylockAcquire &PA) {
    auto It = llvm::find_if(Out, [&](const PendingTrylockAcquire &Existing) {
      return Existing.Cap.equals(PA.Cap);
    });
    if (It == Out.end()) {
      Out.push_back(PA);
      return;
    }
    if (PA.LK == LK_Exclusive)
      It->LK = LK_Exclusive;
    It->MayOnly = It->MayOnly && PA.MayOnly;
  };

  struct WorkItem {
    const Expr *E;
    LocalVarContext Ctx;
    bool UseStateDefs;
  };
  SmallVector<WorkItem, 8> Worklist;
  Worklist.push_back({E, Ctx, UseStateDefs});
  while (!Worklist.empty()) {
    WorkItem I = Worklist.pop_back_val();
    if (!I.E || Analyzer.UnevaluatedStmts.contains(I.E) ||
        isa<LambdaExpr, BlockExpr>(I.E) || !Visited.insert(I.E).second)
      continue;
    if (const auto *CallExp = dyn_cast<CallExpr>(I.E)) {
      if (CallExp->isUnevaluatedBuiltinCall(*Analyzer.ASTCtx))
        continue;
      if (const NamedDecl *Callee = getTrylockCallee(CallExp)) {
        ThreadSafetyAnalyzer::LocalVarLookupScope Lookup(Analyzer, I.Ctx);
        for (const Attr *A : trylockAttrs(Callee)) {
          if (!trylockAttrAppliesTo(A, CallExp->getType()) ||
              State.AcquiredTrylockAttrs.contains({CallExp, A}))
            continue;
          CapExprSet Caps;
          Analyzer.getTrylockMutexIDs(Caps, A, CallExp, Callee);
          for (const CapabilityExpr &Cap : Caps)
            if (!Cap.shouldIgnore())
              AddPending({Cap,
                          isSharedTrylockAttr(A) ? LK_Shared : LK_Exclusive,
                          CallExp->getExprLoc()});
        }
      }
    } else if (const auto *DRE = dyn_cast<DeclRefExpr>(I.E)) {
      const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      if (I.UseStateDefs && VD) {
        if (auto It = State.UnmaterializedVarDefs.find(VD);
            It != State.UnmaterializedVarDefs.end()) {
          Worklist.push_back(
              {It->second.first, It->second.second, /*UseStateDefs=*/false});
          continue;
        }
      }
      LocalVarContext SubCtx = I.Ctx;
      if (const Expr *DefE =
              Analyzer.LocalVarMap.lookupValueExpr(DRE->getDecl(), SubCtx))
        Worklist.push_back({DefE, SubCtx, /*UseStateDefs=*/false});
      continue;
    } else if (const auto *SE = dyn_cast<StmtExpr>(I.E)) {
      if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty())
        if (const auto *Last = dyn_cast<Expr>(CS->body_back()))
          Worklist.push_back({Last, I.Ctx, I.UseStateDefs});
      continue;
    }
    for (const Stmt *Child : I.E->children())
      if (const auto *ChildE = dyn_cast_or_null<Expr>(Child))
        Worklist.push_back({ChildE, I.Ctx, I.UseStateDefs});
  }
}

namespace clang {
namespace threadSafety {

/// Helper of TrylockBodyVerifier::evaluateReturnWithPendingTrylocks().
///
/// The values of an expression only depend on the trylock calls that it
/// contains through the values that these calls return. Hence, instead of
/// evaluating every kind of expression over a set of (values, lock state)
/// outcomes, fork the lock state at each trylock call that has not been
/// materialized yet: one fork per set of return values for which the call
/// acquires the same capabilities. Record the return values of the call for
/// each fork in TrylockValueState::ExprRanges and evaluate the expression
/// once per fork with ThreadSafetyAnalyzer::evaluatePureExprRange(), which
/// takes ExprRanges into account. As a result, the semantics of expressions
/// are only implemented once.
///
/// Operands that are only evaluated conditionally, i.e. the right-hand side
/// of '&&' and '||' and the arms of '?:', are only forked for the forks in
/// which they are evaluated. The forks are split on the value of the
/// condition, which is recorded in ExprRanges too.
///
/// The value of a variable whose definition contains a trylock call is
/// recorded per fork for the DeclRefExpr that refers to it rather than for
/// the variable, since the same variable may have another value where its
/// definition refers to it, e.g. in 'r = r + trylock(&mu)'.
class LLVM_LIBRARY_VISIBILITY ReturnValueForker {
public:
  using IntDomain = ThreadSafetyAnalyzer::IntDomain;
  using IntRangeSet = ThreadSafetyAnalyzer::IntRangeSet;
  using TrylockValueState = ThreadSafetyAnalyzer::TrylockValueState;
  using PendingTrylockAcquire = ThreadSafetyAnalyzer::PendingTrylockAcquire;
  using ReturnEvalOutcome = ThreadSafetyAnalyzer::ReturnEvalOutcome;
  using RangeEvalCtx = ThreadSafetyAnalyzer::RangeEvalCtx;
  using LocalVarLookupScope = ThreadSafetyAnalyzer::LocalVarLookupScope;

  /// A lock state together with the values of the trylock calls, the
  /// conditions and the variable references that it depends on.
  struct Fork {
    FactSet Lockset;
    SmallVector<PendingTrylockAcquire, 2> Pending;
    llvm::SmallDenseMap<const Expr *, IntRangeSet, 4> Bindings;
  };
  using ForkList = SmallVector<Fork, 2>;

  ReturnValueForker(TrylockBodyVerifier &Verifier,
                    const TrylockValueState &State)
      : Verifier(Verifier), Analyzer(Verifier.Analyzer), State(State),
        RetEC{&Verifier.EscapedVars, /*AssumeDerefValid=*/true} {}

  /// Fork \p Forks on the trylock calls that evaluating \p E executes. \p E
  /// is evaluated in the local variable context \p Ctx, with the values that
  /// State records for the local variables if \p UseStateDefs is set.
  void fork(const Expr *E, LocalVarContext Ctx, bool UseStateDefs,
            ForkList &Forks, unsigned Depth = 0);

  /// Fork \p Forks on the pending trylock definition \p DefE in \p DefCtx,
  /// constrained to \p Allowed if non-null. If \p ClearBindings is set, clear
  /// the bindings of each fork afterwards so that later evaluations of the
  /// same AST node (e.g. from a later loop iteration) fork fresh outcomes.
  void forkPendingDef(const Expr *DefE, LocalVarContext DefCtx, QualType Ty,
                      const IntRangeSet *Allowed, ForkList &Forks,
                      bool ClearBindings = false);

  /// The values of \p E in \p F, or std::nullopt if these are unknown.
  std::optional<IntRangeSet> eval(const Expr *E, const Fork &F,
                                  bool UseStateDefs) const;

private:
  // Bind \p E to \p Values in \p F. Return false if \p F is infeasible, i.e.
  // if \p E already has been bound to disjoint values.
  bool bind(Fork &F, const Expr *E, IntRangeSet Values) const;
  // Replace each fork in \p Forks by the forks in which the condition \p Cond
  // may be true and false, with \p Cond bound to the corresponding values.
  // Store the forks in which \p Cond may be true in \p TrueForks and the
  // others in \p FalseForks.
  void splitOnCondition(const Expr *Cond, bool UseStateDefs, ForkList &Forks,
                        ForkList &TrueForks, ForkList &FalseForks) const;
  void forkCall(const CallExpr *CE, LocalVarContext Ctx, bool UseStateDefs,
                ForkList &Forks, unsigned Depth);
  void forkDeclRef(const DeclRefExpr *DRE, LocalVarContext Ctx,
                   bool UseStateDefs, ForkList &Forks, unsigned Depth);
  // Merge the forks that only differ in the values of expressions that no
  // longer matter, then give up if there still are too many forks.
  bool checkForkCount(ForkList &Forks);
  // Merge the forks in \p Forks whose bindings only differ for the
  // expressions in Dead into one fork per set of bindings.
  void mergeForks(ForkList &Forks) const;
  // Whether the values of \p CE are known not to depend on the values of its
  // arguments.
  bool isOpaqueCall(const CallExpr *CE) const;

  TrylockBodyVerifier &Verifier;
  ThreadSafetyAnalyzer &Analyzer;
  const TrylockValueState &State;
  const RangeEvalCtx RetEC;
  // The expressions that contain a forked trylock call. The values that
  // State.ExprRanges records for these do not take the forks into account.
  llvm::SmallPtrSet<const Expr *, 8> Shadowed;
  // The expressions that have been bound, in the order in which these have
  // been bound for the first time.
  mutable SmallVector<const Expr *, 8> BindLog;
  mutable llvm::SmallPtrSet<const Expr *, 8> Logged;
  // The bound expressions whose values no longer matter, e.g. the arguments
  // of a call whose return value does not depend on them.
  llvm::SmallPtrSet<const Expr *, 8> Dead;

  // Restrict \p V, the values of \p E in the domain \p Dom, to the values
  // that the branches that have been taken allow.
  IntRangeSet constrainByState(const Expr *E, IntRangeSet V,
                               const IntDomain &Dom, bool UseStateDefs) const {
    if (!UseStateDefs && !isa<CallExpr>(E))
      return V;
    if (auto It = State.ExprRanges.find(E); It != State.ExprRanges.end())
      return V.intersect(reprojectRangeSet(It->second, Dom));
    return V;
  }
};

} // namespace threadSafety
} // namespace clang

bool ReturnValueForker::checkForkCount(ForkList &Forks) {
  if (Forks.size() <= MaxReturnOutcomes)
    return true;
  mergeForks(Forks);
  if (Forks.size() <= MaxReturnOutcomes)
    return true;
  Verifier.ReturnEvalExhausted = true;
  return false;
}

void ReturnValueForker::mergeForks(ForkList &Forks) const {
  // Group the forks by their live bindings. Compare canonical keys such that
  // grouping takes linear time in the number of forks.
  auto LiveKey = [&](const Fork &F) {
    SmallVector<std::pair<const Expr *, const IntRangeSet *>, 8> Live;
    for (const auto &[E, V] : F.Bindings)
      if (!Dead.contains(E))
        Live.push_back({E, &V});
    llvm::sort(Live, [](const auto &L, const auto &R) {
      return std::less<const Expr *>()(L.first, R.first);
    });
    llvm::FoldingSetNodeID ID;
    for (const auto &[E, V] : Live) {
      ID.AddPointer(E);
      for (const IntRangeSet::Range &R : V->ranges()) {
        R.Lo.Profile(ID);
        R.Hi.Profile(ID);
      }
      ID.AddInteger(~0u);
    }
    return ID;
  };
  SmallVector<llvm::FoldingSetNodeID, 8> Keys;
  SmallVector<SmallVector<unsigned, 4>, 4> Groups;
  llvm::DenseMap<unsigned, SmallVector<unsigned, 2>> GroupsByHash;
  for (unsigned I = 0, N = Forks.size(); I < N; ++I) {
    llvm::FoldingSetNodeID Key = LiveKey(Forks[I]);
    SmallVector<unsigned, 2> &Candidates = GroupsByHash[Key.computeHash()];
    auto It =
        llvm::find_if(Candidates, [&](unsigned G) { return Keys[G] == Key; });
    if (It != Candidates.end()) {
      Groups[*It].push_back(I);
      continue;
    }
    Candidates.push_back(Groups.size());
    Keys.push_back(std::move(Key));
    Groups.push_back({I});
  }
  ForkList Merged;
  for (const SmallVector<unsigned, 4> &G : Groups) {
    Fork M = Forks[G.front()];
    if (G.size() > 1) {
      auto HeldBy = [&](const Fork &F, const CapabilityExpr &Cap, LockKind LK) {
        if (const FactEntry *FE = F.Lockset.findLock(Analyzer.FactMan, Cap);
            FE && !FE->negative() && FE->kind() == LK)
          return true;
        return llvm::any_of(F.Pending, [&](const PendingTrylockAcquire &PA) {
          return !PA.MayOnly && PA.LK == LK && PA.Cap.equals(Cap);
        });
      };
      auto HeldByAll = [&](const CapabilityExpr &Cap, LockKind LK) {
        return llvm::all_of(
            G, [&](unsigned I) { return HeldBy(Forks[I], Cap, LK); });
      };
      SmallVector<CapabilityExpr, 4> NotCommon;
      for (const auto &Fact : M.Lockset) {
        const FactEntry &FE = Analyzer.FactMan[Fact];
        if (!llvm::all_of(G, [&](unsigned I) {
              const FactEntry *OFE =
                  Forks[I].Lockset.findLock(Analyzer.FactMan, FE);
              return OFE && OFE->negative() == FE.negative() &&
                     OFE->kind() == FE.kind();
            }))
          NotCommon.push_back(FE);
      }
      for (const CapabilityExpr &Cap : NotCommon)
        M.Lockset.removeLock(Analyzer.FactMan, Cap);

      M.Pending.clear();
      auto AddPending = [&](const CapabilityExpr &Cap, LockKind LK,
                            SourceLocation Loc, bool MayOnly) {
        if (const FactEntry *FE = M.Lockset.findLock(Analyzer.FactMan, Cap);
            FE && !FE->negative() && FE->kind() == LK)
          return;
        const bool MustHold = !MayOnly && HeldByAll(Cap, LK);
        auto It = llvm::find_if(
            M.Pending, [&](const PendingTrylockAcquire &Existing) {
              return Existing.Cap.equals(Cap) && Existing.LK == LK;
            });
        if (It == M.Pending.end())
          M.Pending.push_back({Cap, LK, Loc, !MustHold});
        else if (MustHold)
          It->MayOnly = false;
      };
      for (unsigned I : G) {
        for (const auto &Fact : Forks[I].Lockset) {
          const FactEntry &FE = Analyzer.FactMan[Fact];
          if (!FE.negative())
            AddPending(FE, FE.kind(), FE.loc(), /*MayOnly=*/false);
        }
        for (const PendingTrylockAcquire &PA : Forks[I].Pending)
          AddPending(PA.Cap, PA.LK, PA.Loc, PA.MayOnly);
      }
      for (unsigned I : llvm::drop_begin(G))
        for (const auto &[E, V] : Forks[I].Bindings)
          if (Dead.contains(E))
            M.Bindings[E] = M.Bindings[E].unionWith(V);
    }
    Merged.push_back(std::move(M));
  }
  Forks = std::move(Merged);
}

bool ReturnValueForker::isOpaqueCall(const CallExpr *CE) const {
  if (getTrylockCallee(CE))
    return true;
  if (isBuiltinExpectCall(CE) || CE->getBuiltinCallee() != 0)
    return false;
  const FunctionDecl *FD = CE->getDirectCallee();
  return FD && !FD->isConstexpr() && !Analyzer.lookupTrivialInlineBody(CE);
}

bool ReturnValueForker::bind(Fork &F, const Expr *E, IntRangeSet Values) const {
  auto [It, Inserted] = F.Bindings.try_emplace(E, Values);
  if (Inserted && Logged.insert(E).second)
    BindLog.push_back(E);
  if (!Inserted)
    It->second = It->second.intersect(Values);
  return !It->second.empty();
}

std::optional<ReturnValueForker::IntRangeSet>
ReturnValueForker::eval(const Expr *E, const Fork &F, bool UseStateDefs) const {
  // Like the definitions of local variables, which do not depend on the
  // values of the variables where these are referenced, evaluate an
  // expression without State if !UseStateDefs. Trylock calls are an
  // exception: their values are recorded for the call expression.
  TrylockValueState EvalState;
  if (UseStateDefs) {
    EvalState = State;
    for (const Expr *S : Shadowed)
      EvalState.ExprRanges.erase(S);
  } else {
    for (const auto &[RE, Values] : State.ExprRanges)
      if (isa<CallExpr>(RE))
        EvalState.ExprRanges.insert({RE, Values});
  }
  // The bindings of F are the values that the bound expressions evaluated to
  // in this fork. Pin these such that evaluating an operand that modifies a
  // variable, e.g. 'check(&s)', does not discard the values of the
  // conditions and variable references in the other operands.
  llvm::SmallPtrSet<const Expr *, 8> Pinned;
  for (const auto &[BE, Values] : F.Bindings) {
    EvalState.ExprRanges.insert_or_assign(BE, Values);
    Pinned.insert(BE);
  }
  RangeEvalCtx EC = RetEC;
  EC.PinnedExprs = &Pinned;
  return Analyzer.evaluatePureExprRange(E, EvalState, EC);
}

void ReturnValueForker::splitOnCondition(const Expr *Cond, bool UseStateDefs,
                                         ForkList &Forks, ForkList &TrueForks,
                                         ForkList &FalseForks) const {
  const Expr *Key = stripNoOpExprWrappers(Cond);
  auto CondDom = Analyzer.getScalarDomain(Cond->getType());
  for (Fork &F : Forks) {
    std::optional<IntRangeSet> CV;
    if (CondDom)
      CV = eval(Cond, F, UseStateDefs);
    if (CV)
      CV = constrainByState(Key, reprojectRangeSet(*CV, *CondDom), *CondDom,
                            UseStateDefs);
    bool MayBeTrue = !CV || CV->mayBeNonZero();
    bool MayBeFalse = !CV || CV->mayBeZero();
    if (MayBeTrue && MayBeFalse && CondDom) {
      IntRangeSet All = CV ? *CV : IntRangeSet::full(*CondDom);
      Fork TF = F;
      if (bind(TF, Key, All.intersect(IntRangeSet::truthSet(*CondDom, true))))
        TrueForks.push_back(std::move(TF));
      if (bind(F, Key, All.intersect(IntRangeSet::truthSet(*CondDom, false))))
        FalseForks.push_back(std::move(F));
      continue;
    }
    // Bind the condition even if its value is known, e.g. from the branch
    // that evaluated it, such that eval() pins its value.
    if (CV && !bind(F, Key, *CV))
      continue;
    if (MayBeTrue)
      TrueForks.push_back(std::move(F));
    else if (MayBeFalse)
      FalseForks.push_back(std::move(F));
  }
  Forks.clear();
}

void ReturnValueForker::forkCall(const CallExpr *CE, LocalVarContext Ctx,
                                 bool UseStateDefs, ForkList &Forks,
                                 unsigned Depth) {
  // The arguments are evaluated before the call.
  const size_t FirstArgBinding = BindLog.size();
  for (const Expr *Arg : CE->arguments())
    fork(Arg, Ctx, UseStateDefs, Forks, Depth + 1);
  if (isOpaqueCall(CE))
    Dead.insert(BindLog.begin() + FirstArgBinding, BindLog.end());

  const NamedDecl *Callee = getTrylockCallee(CE);
  if (!Callee)
    return;
  auto CallDom = Analyzer.getScalarDomain(CE->getType());
  if (!CallDom) {
    Verifier.ReturnEvalExhausted = true;
    return;
  }

  // The return values for which the call acquires each capability
  // exclusively and shared. A capability that a call acquires both
  // exclusively and shared for a value is acquired exclusively.
  struct CallCapSpec {
    CapabilityExpr Cap;
    IntRangeSet ExclusiveSet;
    IntRangeSet SharedSet;
  };
  SmallVector<CallCapSpec, 2> CallSpecs;
  SmallVector<CapabilityExpr, 2> AlreadyAcquiredCaps;
  {
    LocalVarLookupScope Lookup(Analyzer, Ctx);
    for (const Attr *A : trylockAttrs(Callee)) {
      if (!trylockAttrAppliesTo(A, CE->getType()))
        continue;
      auto SuccSet = Analyzer.getTrylockSuccessSet(A, *CallDom);
      if (!SuccSet) {
        Verifier.ReturnEvalExhausted = true;
        return;
      }
      CapExprSet Caps;
      Analyzer.getTrylockMutexIDs(Caps, A, CE, Callee);
      const bool AlreadyMaterialized =
          State.AcquiredTrylockAttrs.contains({CE, A});
      const LockKind LK = isSharedTrylockAttr(A) ? LK_Shared : LK_Exclusive;
      for (const CapabilityExpr &Cap : Caps) {
        if (Cap.shouldIgnore())
          continue;
        if (AlreadyMaterialized) {
          AlreadyAcquiredCaps.push_back(Cap);
          continue;
        }
        auto It = llvm::find_if(CallSpecs, [&](const CallCapSpec &Existing) {
          return Existing.Cap.equals(Cap);
        });
        if (It == CallSpecs.end()) {
          CallSpecs.push_back({Cap, IntRangeSet(), IntRangeSet()});
          It = std::prev(CallSpecs.end());
        }
        IntRangeSet &Set =
            LK == LK_Exclusive ? It->ExclusiveSet : It->SharedSet;
        Set = Set.unionWith(*SuccSet);
      }
    }
  }

  // The values that the branches that have been taken allow.
  std::optional<IntRangeSet> Allowed;
  if (auto It = State.ExprRanges.find(CE); It != State.ExprRanges.end())
    Allowed = reprojectRangeSet(It->second, *CallDom);

  const SourceLocation CallLoc = CE->getExprLoc();
  ForkList DoneForks, TodoForks;
  for (Fork &F : Forks) {
    // A call that is reached more than once, e.g. through two references to
    // the same variable, has already been forked.
    if (F.Bindings.contains(CE))
      DoneForks.push_back(std::move(F));
    else if (bind(F, CE, Allowed ? *Allowed : IntRangeSet::full(*CallDom)))
      TodoForks.push_back(std::move(F));
  }
  if (!TodoForks.empty()) {
    for (const CallCapSpec &Spec : CallSpecs) {
      if (llvm::any_of(AlreadyAcquiredCaps, [&](const CapabilityExpr &C) {
            return C.equals(Spec.Cap);
          }))
        continue;
      IntRangeSet SharedOnly =
          Spec.SharedSet.intersect(Spec.ExclusiveSet.complement(*CallDom));
      IntRangeSet FailSet =
          Spec.ExclusiveSet.unionWith(Spec.SharedSet).complement(*CallDom);
      ForkList Next;
      for (Fork &F : TodoForks) {
        auto Split = [&](const IntRangeSet &Set, std::optional<LockKind> LK) {
          Fork NF = F;
          if (!bind(NF, CE, Set))
            return;
          if (LK)
            NF.Pending.push_back({Spec.Cap, *LK, CallLoc});
          Next.push_back(std::move(NF));
        };
        Split(Spec.ExclusiveSet, LK_Exclusive);
        Split(SharedOnly, LK_Shared);
        Split(FailSet, std::nullopt);
      }
      TodoForks = std::move(Next);
      if (TodoForks.empty() || !checkForkCount(TodoForks))
        break;
    }
    llvm::append_range(DoneForks, std::move(TodoForks));
  }
  Forks = std::move(DoneForks);
  checkForkCount(Forks);
}

void ReturnValueForker::forkDeclRef(const DeclRefExpr *DRE, LocalVarContext Ctx,
                                    bool UseStateDefs, ForkList &Forks,
                                    unsigned Depth) {
  if (llvm::all_of(Forks,
                   [&](const Fork &F) { return F.Bindings.contains(DRE); }))
    return;
  const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
  const Expr *DefE = nullptr;
  LocalVarContext DefCtx = Ctx;
  if (UseStateDefs && VD) {
    if (auto It = State.UnmaterializedVarDefs.find(VD);
        It != State.UnmaterializedVarDefs.end()) {
      DefE = It->second.first;
      DefCtx = It->second.second;
    } else if (State.VarRanges.contains(VD)) {
      return;
    }
  }
  if (!DefE)
    DefE = Analyzer.LocalVarMap.lookupValueExpr(DRE->getDecl(), DefCtx);
  if (!DefE)
    return;
  auto DefDom = Analyzer.getScalarDomain(DefE->getType());
  auto RefDom = Analyzer.getScalarDomain(DRE->getType());
  if (!DefDom || !RefDom) {
    Verifier.ReturnEvalExhausted = true;
    return;
  }

  const Expr *DefKey = stripNoOpExprWrappers(DefE);
  bool IsCurrentVarDef = UseStateDefs;
  if (!IsCurrentVarDef && VD)
    if (auto It = State.UnmaterializedVarDefs.find(VD);
        It != State.UnmaterializedVarDefs.end())
      IsCurrentVarDef = It->second.first == DefE;
  std::optional<IntRangeSet> VarConstraint;
  if (IsCurrentVarDef && VD)
    if (auto VR = State.VarRanges.find(VD); VR != State.VarRanges.end())
      VarConstraint = reprojectRangeSet(VR->second, *RefDom);

  ForkList DoneForks, TodoForks;
  for (Fork &F : Forks) {
    if (F.Bindings.contains(DefKey))
      DoneForks.push_back(std::move(F));
    else
      TodoForks.push_back(std::move(F));
  }
  if (!TodoForks.empty()) {
    fork(DefKey, DefCtx, /*UseStateDefs=*/false, TodoForks, Depth + 1);
    if (Verifier.ReturnEvalExhausted)
      return;
    for (Fork &F : TodoForks) {
      std::optional<IntRangeSet> DV = eval(DefKey, F, /*UseStateDefs=*/false);
      IntRangeSet Values =
          DV ? reprojectRangeSet(*DV, *RefDom) : IntRangeSet::full(*RefDom);
      if (VarConstraint)
        Values = Values.intersect(*VarConstraint);
      if (bind(F, DefKey, reprojectRangeSet(std::move(Values), *DefDom)))
        DoneForks.push_back(std::move(F));
    }
  }

  ForkList Next;
  for (Fork &F : DoneForks) {
    IntRangeSet Values =
        reprojectRangeSet(F.Bindings.find(DefKey)->second, *RefDom);
    if (VarConstraint)
      Values = Values.intersect(*VarConstraint);
    Values = constrainByState(DRE, std::move(Values), *RefDom, UseStateDefs);
    if (bind(F, DRE, std::move(Values)))
      Next.push_back(std::move(F));
  }
  Forks = std::move(Next);
  checkForkCount(Forks);
}

void ReturnValueForker::forkPendingDef(const Expr *DefE, LocalVarContext DefCtx,
                                       QualType Ty, const IntRangeSet *Allowed,
                                       ForkList &Forks, bool ClearBindings) {
  if (!DefE || Forks.empty() || Verifier.ReturnEvalExhausted)
    return;
  auto Dom = Analyzer.getScalarDomain(Ty);
  if (!Dom) {
    if (Allowed)
      Verifier.ReturnEvalExhausted = true;
    return;
  }
  const Expr *DefKey = stripNoOpExprWrappers(DefE);
  llvm::SmallPtrSet<const CallExpr *, 4> DefCalls;
  bool HaveDefCalls = false;
  ForkList DoneForks, TodoForks;
  for (Fork &F : Forks) {
    if (F.Bindings.contains(DefKey)) {
      if (!Allowed || bind(F, DefKey, reprojectRangeSet(*Allowed, *Dom)))
        DoneForks.push_back(std::move(F));
      continue;
    }
    if (!Allowed) {
      if (!HaveDefCalls) {
        Verifier.exprHasUnmaterializedTrylock(
            DefKey, DefCtx, State, /*UseStateDefs=*/false,
            /*IncludeMaterialized=*/false, &DefCalls);
        HaveDefCalls = true;
      }
      if (Verifier.ReturnEvalExhausted)
        return;
      if (llvm::all_of(DefCalls, [&](const CallExpr *CE) {
            return F.Bindings.contains(CE);
          })) {
        DoneForks.push_back(std::move(F));
        continue;
      }
    }
    TodoForks.push_back(std::move(F));
  }
  if (TodoForks.empty()) {
    Forks = std::move(DoneForks);
    return;
  }

  fork(DefKey, DefCtx, /*UseStateDefs=*/false, TodoForks);
  if (Verifier.ReturnEvalExhausted)
    return;

  ForkList Next;
  for (Fork &F : TodoForks) {
    std::optional<IntRangeSet> DV = eval(DefKey, F, /*UseStateDefs=*/false);
    IntRangeSet Values =
        DV ? reprojectRangeSet(*DV, *Dom) : IntRangeSet::full(*Dom);
    if (Allowed)
      Values = Values.intersect(reprojectRangeSet(*Allowed, *Dom));
    if (bind(F, DefKey, std::move(Values)))
      Next.push_back(std::move(F));
  }
  llvm::append_range(DoneForks, std::move(Next));
  if (ClearBindings) {
    BindLog.clear();
    Logged.clear();
    Dead.clear();
    Shadowed.clear();
    for (Fork &F : DoneForks)
      F.Bindings.clear();
  }
  Forks = std::move(DoneForks);
  checkForkCount(Forks);
}

void ReturnValueForker::fork(const Expr *E, LocalVarContext Ctx,
                             bool UseStateDefs, ForkList &Forks,
                             unsigned Depth) {
  if (!E || Forks.empty() || Verifier.ReturnEvalExhausted ||
      Analyzer.UnevaluatedStmts.contains(E))
    return;
  if (Verifier.ReturnEvalSteps == 0 || Depth > MaxConstrainExprDepth) {
    Verifier.ReturnEvalExhausted = true;
    return;
  }
  --Verifier.ReturnEvalSteps;
  const Expr *Cur = stripNoOpExprWrappers(E);
  if (Analyzer.UnevaluatedStmts.contains(Cur))
    return;
  // Whether the value of Cur depends on the value of a trylock call. If not,
  // there is nothing to fork. State provides the values of the variables if
  // UseStateDefs is set. Otherwise, the variable references have to be bound
  // to the values of their definitions.
  const bool HasTrylock = Verifier.exprHasUnmaterializedTrylock(
      Cur, Ctx, State, UseStateDefs, /*IncludeMaterialized=*/true);
  if (!HasTrylock && UseStateDefs)
    return;
  // Give up on an expression that contains a trylock call but that cannot be
  // forked. Otherwise its value is merely unknown.
  auto GiveUp = [&] {
    if (HasTrylock)
      Verifier.ReturnEvalExhausted = true;
  };

  if (const auto *CE = dyn_cast<CallExpr>(Cur)) {
    if (CE->isUnevaluatedBuiltinCall(*Analyzer.ASTCtx))
      return;
    if (HasTrylock && !getTrylockCallee(CE))
      Shadowed.insert(Cur);
    if (isBuiltinExpectCall(CE))
      return fork(CE->getArg(0), Ctx, UseStateDefs, Forks, Depth + 1);
    return forkCall(CE, Ctx, UseStateDefs, Forks, Depth);
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(Cur))
    return forkDeclRef(DRE, Ctx, UseStateDefs, Forks, Depth);

  if (HasTrylock)
    Shadowed.insert(Cur);

  // Only split the forks on a condition if a conditionally evaluated operand
  // depends on a trylock call.
  if (const auto *BO = dyn_cast<BinaryOperator>(Cur)) {
    if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign)
      return fork(BO->getRHS(), Ctx, UseStateDefs, Forks, Depth + 1);
    if (BO->isLogicalOp() && HasTrylock) {
      fork(BO->getLHS(), Ctx, UseStateDefs, Forks, Depth + 1);
      ForkList TrueForks, FalseForks;
      splitOnCondition(BO->getLHS(), UseStateDefs, Forks, TrueForks,
                       FalseForks);
      // The right-hand side is only evaluated if the left-hand side is true
      // (&&) or false (||).
      const bool IsAnd = BO->getOpcode() == BO_LAnd;
      ForkList &EvalRHS = IsAnd ? TrueForks : FalseForks;
      ForkList &SkipRHS = IsAnd ? FalseForks : TrueForks;
      fork(BO->getRHS(), Ctx, UseStateDefs, EvalRHS, Depth + 1);
      Forks = std::move(SkipRHS);
      llvm::append_range(Forks, std::move(EvalRHS));
      checkForkCount(Forks);
      return;
    }
  }

  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(Cur);
      BCO && HasTrylock) {
    // The common operand is evaluated once. The false operand is only
    // evaluated if it is false.
    fork(BCO->getCommon(), Ctx, UseStateDefs, Forks, Depth + 1);
    ForkList TrueForks, FalseForks;
    splitOnCondition(BCO->getCommon(), UseStateDefs, Forks, TrueForks,
                     FalseForks);
    fork(BCO->getFalseExpr(), Ctx, UseStateDefs, FalseForks, Depth + 1);
    Forks = std::move(TrueForks);
    llvm::append_range(Forks, std::move(FalseForks));
    checkForkCount(Forks);
    return;
  }

  if (const auto *COP = dyn_cast<ConditionalOperator>(Cur); COP && HasTrylock) {
    fork(COP->getCond(), Ctx, UseStateDefs, Forks, Depth + 1);
    ForkList TrueForks, FalseForks;
    splitOnCondition(COP->getCond(), UseStateDefs, Forks, TrueForks,
                     FalseForks);
    fork(COP->getTrueExpr(), Ctx, UseStateDefs, TrueForks, Depth + 1);
    fork(COP->getFalseExpr(), Ctx, UseStateDefs, FalseForks, Depth + 1);
    Forks = std::move(TrueForks);
    llvm::append_range(Forks, std::move(FalseForks));
    checkForkCount(Forks);
    return;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(Cur)) {
    if (!UseStateDefs)
      if (const Expr *Inner = Analyzer.getCachedPureStmtExpr(SE))
        return fork(Inner, Ctx, UseStateDefs, Forks, Depth + 1);
    // The statements before the last one have already been executed. Their
    // effects on the lockset and on the local variable context are known.
    const auto *CS = SE->getSubStmt();
    const auto *Last =
        CS && !CS->body_empty() ? dyn_cast<Expr>(CS->body_back()) : nullptr;
    auto Dom = Analyzer.getScalarDomain(SE->getType());
    if (!Last || !Dom)
      return GiveUp();
    fork(Last, Ctx, UseStateDefs, Forks, Depth + 1);
    ForkList Next;
    for (Fork &F : Forks) {
      std::optional<IntRangeSet> V = eval(Last, F, UseStateDefs);
      if (bind(F, SE,
               constrainByState(SE,
                                V ? reprojectRangeSet(*V, *Dom)
                                  : IntRangeSet::full(*Dom),
                                *Dom, UseStateDefs)))
        Next.push_back(std::move(F));
    }
    Forks = std::move(Next);
    return;
  }

  // Bind the variable references in the operands, which are evaluated
  // unconditionally unless Cur does not depend on a trylock call.
  for (const Stmt *Child : Cur->children()) {
    if (const auto *ChildE = dyn_cast_or_null<Expr>(Child))
      fork(ChildE, Ctx, UseStateDefs, Forks, Depth + 1);
    else if (Child)
      return GiveUp();
  }
}

/// Whether evaluating the trylock result \p DefE in the local variable context
/// \p DefCtx may acquire a capability on the path described by \p State if
/// its value is in \p Allowed. Answer true if that cannot be determined
/// within the evaluation budget.
bool TrylockBodyVerifier::trylockDefMayAcquire(const TrylockValueState &State,
                                               const Expr *DefE,
                                               LocalVarContext DefCtx,
                                               QualType Ty,
                                               const IntRangeSet *Allowed) {
  if (State.Infeasible)
    return false;
  auto Dom = Analyzer.getScalarDomain(Ty);
  if (!Dom || InReturnEval)
    return true;
  ReturnEvalSteps = MaxReturnEvalSteps;
  ReturnScanSteps = MaxTrylockScanSteps;
  InReturnEval = true;
  ReturnEvalExhausted = false;
  llvm::scope_exit ResetBudget([&] {
    ReturnEvalSteps = 0;
    ReturnScanSteps = 0;
    InReturnEval = false;
    ReturnEvalExhausted = false;
  });
  ReturnValueForker Forker(*this, State);
  ReturnValueForker::ForkList Forks = {{FactSet(), {}, {}}};
  Forker.forkPendingDef(DefE, DefCtx, Ty, Allowed, Forks);
  if (ReturnEvalExhausted)
    return true;
  return llvm::any_of(Forks, [&](const ReturnValueForker::Fork &F) {
    return !F.Pending.empty() || !F.Lockset.isEmpty(Analyzer.FactMan);
  });
}

/// Evaluate the return value \p RetVal together with every pending trylock
/// call that may have succeeded on the current path. If the evaluation exceeds
/// its budget, assume that every trylock call that may have been executed has
/// acquired its capabilities for every return value.
void TrylockBodyVerifier::evaluateReturnWithPendingTrylocks(
    const Expr *RetVal, const FactSet &InLockset,
    const TrylockValueState &State, LocalVarContext Ctx,
    SmallVectorImpl<ReturnEvalOutcome> &Out) {
  if (State.Infeasible)
    return;
  ReturnEvalSteps = MaxReturnEvalSteps;
  ReturnScanSteps = MaxTrylockScanSteps;
  InReturnEval = true;
  ReturnEvalExhausted = false;
  llvm::scope_exit ResetBudget([&] {
    ReturnEvalSteps = 0;
    ReturnScanSteps = 0;
    InReturnEval = false;
    ReturnEvalExhausted = false;
  });

  auto CallCtx = [&](const CallExpr *CE) {
    auto It = DiscardedCallCtx.find(CE);
    return It != DiscardedCallCtx.end() ? It->second : Ctx;
  };

  // Sort the variables by source location for deterministic diagnostics.
  SmallVector<
      std::pair<const ValueDecl *, std::pair<const Expr *, LocalVarContext>>, 4>
      Defs(State.UnmaterializedVarDefs.begin(),
           State.UnmaterializedVarDefs.end());
  llvm::sort(Defs, [](const auto &A, const auto &B) {
    return A.first->getLocation().getRawEncoding() <
           B.first->getLocation().getRawEncoding();
  });

  const Expr *RetE = stripNoOpExprWrappers(RetVal);
  const auto *RetBO = dyn_cast_or_null<BinaryOperator>(RetE);
  const auto ShortCircuitIt = (RetBO && RetBO->isLogicalOp())
                                  ? State.ShortCircuitedOps.find(RetBO)
                                  : State.ShortCircuitedOps.end();
  const bool IsShortCircuited = ShortCircuitIt != State.ShortCircuitedOps.end();
  const bool IsDependentRet =
      RetE && (RetE->isTypeDependent() || RetE->isValueDependent());

  ReturnValueForker Forker(*this, State);
  ReturnValueForker::ForkList Forks = {{InLockset, {}, {}}};

  // The result of an earlier loop iteration is independent of the result of
  // the same definition in the final iteration that the return value refers
  // to. Fork on earlier-iteration results first and clear their AST bindings.
  for (const OverwrittenTrylockDef &Def : State.OverwrittenTrylockDefs) {
    if (ReturnEvalExhausted)
      break;
    if (Def.FromEarlierIteration)
      Forker.forkPendingDef(Def.DefE, Def.Ctx, Def.Ty,
                            Def.Allowed ? &*Def.Allowed : nullptr, Forks,
                            /*ClearBindings=*/true);
  }
  for (const OverwrittenTrylockDef &Def : State.OverwrittenTrylockDefs) {
    if (ReturnEvalExhausted)
      break;
    if (!Def.FromEarlierIteration)
      Forker.forkPendingDef(Def.DefE, Def.Ctx, Def.Ty,
                            Def.Allowed ? &*Def.Allowed : nullptr, Forks);
  }
  for (const auto &[VD, DefPair] : Defs) {
    if (ReturnEvalExhausted)
      break;
    auto VR = State.VarRanges.find(VD);
    Forker.forkPendingDef(DefPair.first, DefPair.second, VD->getType(),
                          VR != State.VarRanges.end() ? &VR->second : nullptr,
                          Forks);
  }
  for (const CallExpr *CE : State.DiscardedTrylockCalls) {
    if (ReturnEvalExhausted)
      break;
    Forker.forkPendingDef(CE, CallCtx(CE), CE->getType(), /*Allowed=*/nullptr,
                          Forks);
  }
  const Expr *EvalRetE = IsShortCircuited ? RetBO->getLHS() : RetE;
  if (!ReturnEvalExhausted && EvalRetE && !IsDependentRet)
    Forker.fork(EvalRetE, Ctx, /*UseStateDefs=*/true, Forks);

  if (!ReturnEvalExhausted) {
    std::optional<IntRangeSet> AllowedRet;
    if (RetE)
      if (auto It = State.ExprRanges.find(RetE); It != State.ExprRanges.end())
        AllowedRet = reprojectRangeSet(It->second, CurrentTrylockRetDom);

    auto SamePending = [](const SmallVectorImpl<PendingTrylockAcquire> &A,
                          const SmallVectorImpl<PendingTrylockAcquire> &B) {
      return A.size() == B.size() &&
             llvm::all_of(llvm::zip_equal(A, B), [](const auto &P) {
               const auto &[PA, PB] = P;
               return PA.LK == PB.LK && PA.Loc == PB.Loc &&
                      PA.MayOnly == PB.MayOnly && PA.Cap.equals(PB.Cap);
             });
    };

    SmallVector<ReturnEvalOutcome, 4> Merged;
    for (ReturnValueForker::Fork &F : Forks) {
      IntRangeSet Values = IntRangeSet::full(CurrentTrylockRetDom);
      if (IsShortCircuited) {
        Values = IntRangeSet::single(
            CurrentTrylockRetDom,
            llvm::APSInt::get(ShortCircuitIt->second ? 1 : 0));
      } else if (RetE && !IsDependentRet) {
        if (std::optional<IntRangeSet> R =
                Forker.eval(RetE, F, /*UseStateDefs=*/true))
          Values = reprojectRangeSet(*R, CurrentTrylockRetDom);
      }
      if (AllowedRet)
        Values = Values.intersect(*AllowedRet);
      if (Values.empty())
        continue;
      auto It = llvm::find_if(Merged, [&](const ReturnEvalOutcome &M) {
        return SamePending(M.PendingAcquires, F.Pending) &&
               factSetsEquivalent(M.Lockset, F.Lockset);
      });
      if (It != Merged.end())
        It->Values = It->Values.unionWith(Values);
      else
        Merged.push_back(
            {std::move(Values), std::move(F.Lockset), std::move(F.Pending)});
    }
    llvm::append_range(Out, std::move(Merged));
    return;
  }

  // Give up on tracking the lock state per outcome. Assume that every trylock
  // call that may have been executed may have acquired its capabilities for
  // every return value: such a capability is reported if it is not expected
  // to be held, but it does not satisfy a capability that is expected to be
  // held either. This may report false positives but never misses a leaked
  // or a missing capability.
  ReturnEvalOutcome Conservative;
  Conservative.Values = IntRangeSet::full(CurrentTrylockRetDom);
  if (RetVal) {
    const ThreadSafetyAnalyzer::RangeEvalCtx RetEC{&EscapedVars,
                                                   /*AssumeDerefValid=*/true};
    if (auto R = Analyzer.evaluatePureExprRange(RetVal, State, RetEC))
      if (IntRangeSet Mapped = reprojectRangeSet(*R, CurrentTrylockRetDom);
          !Mapped.empty())
        Conservative.Values = std::move(Mapped);
  }
  Conservative.Lockset = InLockset;
  llvm::SmallPtrSet<const Expr *, 16> Visited;
  collectTrylockAcquires(RetVal, Ctx, State, /*UseStateDefs=*/true,
                         Conservative.PendingAcquires, Visited);
  for (const auto &[VD, DefPair] : Defs)
    collectTrylockAcquires(DefPair.first, DefPair.second, State,
                           /*UseStateDefs=*/false, Conservative.PendingAcquires,
                           Visited);
  for (const OverwrittenTrylockDef &Def : State.OverwrittenTrylockDefs)
    collectTrylockAcquires(Def.DefE, Def.Ctx, State, /*UseStateDefs=*/false,
                           Conservative.PendingAcquires, Visited);
  for (const CallExpr *CE : State.DiscardedTrylockCalls)
    collectTrylockAcquires(CE, CallCtx(CE), State, /*UseStateDefs=*/false,
                           Conservative.PendingAcquires, Visited);
  for (PendingTrylockAcquire &PA : Conservative.PendingAcquires)
    PA.MayOnly = true;
  Out.push_back(std::move(Conservative));
}

void TrylockBodyVerifier::applyScopeExitCleanups(
    FactSet &StateSet, const CFGBlock *B, bool OnlyAfterReturn,
    const FactSet *PreReturnSet, ThreadSafetyHandler *DiagHandler) {
  ThreadSafetyHandler QuietHandler;
  bool SeenReturn = false;
  unsigned CtxIdx = Analyzer.BlockInfo[B->getBlockID()].EntryIndex;
  LocalVarContext StmtCtx = Analyzer.BlockInfo[B->getBlockID()].EntryContext;

  // StmtCtx advances while the statements of B are visited.
  ThreadSafetyAnalyzer::LocalVarLookupScope Lookup(Analyzer, &StmtCtx);

  auto ApplyCallee = [&](const NamedDecl *Callee, const Expr *Exp,
                         til::SExpr *Self, SourceLocation Loc,
                         bool FullyRemove) {
    if (!Callee || !Callee->hasAttrs())
      return;
    ThreadSafetyAnalyzer::CallLockEffects Effects;
    for (const Attr *At : Callee->attrs()) {
      if (Analyzer.collectLockEffects(At, Exp, Callee, Self, Effects))
        continue;
      if (const auto *A = dyn_cast<LocksExcludedAttr>(At)) {
        if (!DiagHandler || !PreReturnSet)
          continue;
        CapExprSet ExcludedLocks;
        Analyzer.getMutexIDs(ExcludedLocks, A, Exp, Callee, Self);
        for (const auto &ExclLock : ExcludedLocks) {
          if (!ExclLock.shouldIgnore() &&
              !PreReturnSet->findLock(Analyzer.FactMan, ExclLock) &&
              StateSet.findLock(Analyzer.FactMan, ExclLock))
            DiagHandler->handleFunExcludesLock(ExclLock.getKind(),
                                               Callee->getNameAsString(),
                                               ExclLock.toString(), Loc);
        }
        continue;
      }
      const auto *A = dyn_cast<AssertCapabilityAttr>(At);
      if (!A)
        continue;
      CapExprSet AssertLocks;
      Analyzer.getMutexIDs(AssertLocks, A, Exp, Callee, Self);
      for (const auto &AssertLock : AssertLocks) {
        if (!AssertLock.shouldIgnore() &&
            !StateSet.findLock(Analyzer.FactMan, AssertLock)) {
          StateSet.removeLock(Analyzer.FactMan, !AssertLock);
          StateSet.addLock(Analyzer.FactMan,
                           Analyzer.FactMan.createFact<LockableFactEntry>(
                               AssertLock,
                               A->isShared() ? LK_Shared : LK_Exclusive, Loc,
                               FactEntry::Asserted));
        }
      }
    }

    for (const CapabilityExpr &Cp : llvm::concat<const CapabilityExpr>(
             Effects.ExclusiveLocksToRemove, Effects.SharedLocksToRemove,
             Effects.GenericLocksToRemove)) {
      if (Cp.shouldIgnore())
        continue;
      if (const FactEntry *LDat = StateSet.findLock(Analyzer.FactMan, Cp))
        LDat->handleUnlock(StateSet, Analyzer.FactMan, Cp, Loc, FullyRemove,
                           QuietHandler);
    }

    auto QuietAdd = [&](const CapabilityExpr &Cp, LockKind LK) {
      if (Cp.shouldIgnore())
        return;
      const auto *Entry = Analyzer.FactMan.createFact<LockableFactEntry>(
          Cp, LK, Loc, FactEntry::Acquired);
      if (const FactEntry *Existing =
              StateSet.findLock(Analyzer.FactMan, *Entry)) {
        ThreadSafetyHandler &H =
            (DiagHandler && PreReturnSet &&
             !PreReturnSet->findLock(Analyzer.FactMan, *Entry))
                ? *DiagHandler
                : QuietHandler;
        Existing->handleLock(StateSet, Analyzer.FactMan, *Entry, H);
      } else {
        StateSet.removeLock(Analyzer.FactMan, !*Entry);
        StateSet.addLock(Analyzer.FactMan, Entry);
      }
    };
    for (const auto &M : Effects.ExclusiveLocksToAdd)
      QuietAdd(M, LK_Exclusive);
    for (const auto &M : Effects.SharedLocksToAdd)
      QuietAdd(M, LK_Shared);
  };

  for (const auto &BI : *B) {
    if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
      const Stmt *S = CS->getStmt();
      if (Analyzer.UnevaluatedStmts.contains(S))
        continue;
      llvm::scope_exit AdvanceCtx([&] {
        StmtCtx = Analyzer.LocalVarMap.getNextContext(CtxIdx, S, StmtCtx);
      });
      if (isa<ReturnStmt>(S)) {
        SeenReturn = true;
        continue;
      }
      if (!OnlyAfterReturn && !SeenReturn) {
        if (const auto *CE = dyn_cast<CallExpr>(S)) {
          const auto *Callee = dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
          if (Callee && Callee->hasAttrs())
            ApplyCallee(Callee, CE, /*Self=*/nullptr, CE->getExprLoc(),
                        /*FullyRemove=*/false);
        } else if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
          const auto *Callee = CCE->getConstructor();
          if (Callee && Callee->hasAttrs())
            ApplyCallee(Callee, CCE, /*Self=*/nullptr, CCE->getExprLoc(),
                        /*FullyRemove=*/false);
        }
      }
      continue;
    }
    if (OnlyAfterReturn && !SeenReturn)
      continue;
    if (!OnlyAfterReturn && SeenReturn)
      continue;

    if (std::optional<ThreadSafetyAnalyzer::ScopeExitCall> Call =
            Analyzer.getScopeExitCall(BI))
      ApplyCallee(Call->Callee, /*Exp=*/nullptr, Call->Self, Call->Loc,
                  /*FullyRemove=*/true);
  }
}

/// Remove the facts from \p Acc that are not in \p Other. Keep the shared
/// fact if a capability is held exclusively in one set and shared in the
/// other one.
void TrylockBodyVerifier::intersectExpectedSets(FactSet &Acc,
                                                const FactSet &Other) {
  FactSet AccOrig = Acc;
  for (const auto &Fact : AccOrig) {
    const FactEntry &AFact = Analyzer.FactMan[Fact];
    const FactEntry *BFact = Other.findLock(Analyzer.FactMan, AFact);
    if (!BFact || AFact.negative() != BFact->negative()) {
      Acc.removeLock(Analyzer.FactMan, AFact);
      continue;
    }
    if (AFact.kind() == LK_Exclusive && BFact->kind() == LK_Shared)
      if (FactSet::iterator It = Acc.findLockIter(Analyzer.FactMan, AFact);
          It != Acc.end())
        Acc.replaceLock(Analyzer.FactMan, It, BFact);
  }
}

void TrylockBodyVerifier::checkTrylockExitOutcome(
    const FactSet &BaseExpectedExitSet, const ReturnEvalOutcome &Outcome,
    SourceLocation DiagLoc, ThreadSafetyHandler &ExitHandler,
    std::optional<FactSet> *NonNullExpectedSet, const FactSet *MaySet) {
  if (Outcome.Values.empty())
    return;

  // The capabilities that may be held at the exit: the capabilities that are
  // held plus the capabilities that have only been acquired on some of the
  // paths that have been merged into Outcome.
  FactSet ExitSet = Outcome.Lockset;
  if (MaySet)
    for (const auto &Fact : *MaySet)
      if (!ExitSet.findLock(Analyzer.FactMan, Analyzer.FactMan[Fact]))
        ExitSet.addLock(Analyzer.FactMan, &Analyzer.FactMan[Fact]);

  struct ExitPartition {
    IntRangeSet Vals;
    FactSet ExpectedSet;
  };
  SmallVector<ExitPartition, 2> Partitions;
  Partitions.push_back({Outcome.Values, BaseExpectedExitSet});

  for (const TrylockExitSpec &Spec : CurrentTrylockExitSpecs) {
    IntRangeSet Comp = Spec.SuccessSet.complement(CurrentTrylockRetDom);
    SmallVector<ExitPartition, 2> Next;
    for (auto &P : Partitions) {
      IntRangeSet In = P.Vals.intersect(Spec.SuccessSet);
      IntRangeSet Out = P.Vals.intersect(Comp);
      if (!In.empty()) {
        FactSet WithSpec = P.ExpectedSet;
        addLockToExpectedSet(WithSpec, Spec.Cap, Spec.LK, Spec.Loc);
        Next.push_back({std::move(In), std::move(WithSpec)});
      }
      if (!Out.empty())
        Next.push_back({std::move(Out), std::move(P.ExpectedSet)});
    }
    Partitions = std::move(Next);
  }

  IntRangeSet ValidAddrs;
  if (NonNullExpectedSet)
    ValidAddrs = validObjectPtrRangeSet(CurrentTrylockRetDom);

  for (ExitPartition &P : Partitions) {
    // The caller may only access the pointee of a returned pointer if the
    // pointer is a valid object address, i.e. not null. Collect the
    // capabilities that the caller holds for every such return value.
    if (NonNullExpectedSet && P.Vals.intersectsSet(ValidAddrs)) {
      if (!*NonNullExpectedSet)
        *NonNullExpectedSet = P.ExpectedSet;
      else
        intersectExpectedSets(**NonNullExpectedSet, P.ExpectedSet);
    }

    // Report the expected capabilities that have only been acquired on some
    // of the merged paths. intersectAndWarn() does not report these because
    // they are in ExitSet.
    if (MaySet) {
      for (const auto &EFact : P.ExpectedSet) {
        const FactEntry &EntryFact = Analyzer.FactMan[EFact];
        if (EntryFact.negative() ||
            Outcome.Lockset.findLock(Analyzer.FactMan, EntryFact) ||
            !MaySet->findLock(Analyzer.FactMan, EntryFact))
          continue;
        EntryFact.handleRemovalFromIntersection(
            P.ExpectedSet, Analyzer.FactMan, DiagLoc,
            LEK_NotLockedAtEndOfFunction, ExitHandler);
      }
    }

    Analyzer.intersectAndWarn(P.ExpectedSet, ExitSet, DiagLoc,
                              LEK_LockedAtEndOfFunction,
                              LEK_NotLockedAtEndOfFunction,
                              /*IsIgnored=*/nullptr,
                              /*RebranchIgnoresDepth=*/false,
                              /*ReportMissingAcquires=*/true, &ExitHandler);
  }
}

static void addTrylockExitSpec(
    SmallVectorImpl<ThreadSafetyAnalyzer::TrylockExitSpec> &ExitSpecs,
    const CapabilityExpr &Cap, LockKind LK,
    const ThreadSafetyAnalyzer::IntRangeSet &SuccSet, SourceLocation AttrLoc) {
  if (Cap.shouldIgnore())
    return;
  for (ThreadSafetyAnalyzer::TrylockExitSpec &Existing : ExitSpecs) {
    if (Existing.Cap.equals(Cap) && Existing.LK == LK) {
      Existing.SuccessSet = Existing.SuccessSet.unionWith(SuccSet);
      return;
    }
  }
  ExitSpecs.push_back({Cap, LK, SuccSet, AttrLoc});
}

bool ThreadSafetyAnalyzer::addTrylockExitSpecs(
    const Attr *Attr, const NamedDecl *D,
    SmallVectorImpl<TrylockExitSpec> &ExitSpecs, IntDomain &RetDomOut) {
  if (isa_and_nonnull<CoroutineBodyStmt>(D->getBody()))
    return false;
  // Trylock attributes cannot be applied to Objective-C methods.
  QualType FuncReturnType;
  if (CurrentFunction)
    FuncReturnType = CurrentFunction->getReturnType();
  // Sema accepts try_acquire_capability on functions with any return
  // type for compatibility and drops attributes whose success value is
  // not a constant. Do not skip the body if the attribute cannot be
  // modeled, e.g. because the function returns void or during error
  // recovery.
  std::optional<IntDomain> RetDom;
  if (trylockAttrAppliesTo(Attr, FuncReturnType))
    RetDom = getScalarDomain(FuncReturnType);
  std::optional<IntRangeSet> SuccSet;
  if (RetDom)
    SuccSet = getTrylockSuccessSet(Attr, *RetDom);
  if (!SuccSet)
    return false;
  RetDomOut = *RetDom;
  CapExprSet AttrCaps;
  getTrylockMutexIDs(AttrCaps, Attr, nullptr, D);
  LockKind LK = isSharedTrylockAttr(Attr) ? LK_Shared : LK_Exclusive;
  size_t NumSpecs = ExitSpecs.size();
  for (const auto &Cap : AttrCaps)
    addTrylockExitSpec(ExitSpecs, Cap, LK, *SuccSet, Attr->getLocation());
  if (ExitSpecs.size() == NumSpecs &&
      llvm::none_of(AttrCaps, [](const CapabilityExpr &Cap) {
        return !Cap.shouldIgnore();
      }))
    return false;
  return true;
}

namespace {

/// Wrapper around ThreadSafetyHandler that deduplicates diagnostics emitted
/// while verifying multiple return outcomes/partitions at function exit. Every
/// callback is forwarded to the wrapped handler unless an identical callback
/// has already been forwarded.
///
/// The callbacks that can be reached while verifying the exit outcomes of a
/// trylock function are deduplicated: those of the code that adds the pending
/// trylock acquisitions to the lockset (handleNegativeNotHeld(),
/// BeforeSet::checkBeforeAfter() and FactEntry::handleLock()) and those of
/// checkTrylockExitOutcome(). All other callbacks are forwarded directly to
/// the wrapped handler.
class DedupThreadSafetyHandler final : public ThreadSafetyHandler {
  ThreadSafetyHandler &Inner;
  llvm::BumpPtrAllocator Alloc;
  llvm::DenseSet<llvm::FoldingSetNodeIDRef> Emitted;

  static void add(llvm::FoldingSetNodeID &ID, StringRef Str) {
    ID.AddString(Str);
  }
  static void add(llvm::FoldingSetNodeID &ID, SourceLocation Loc) {
    ID.Add(Loc);
  }
  static void add(llvm::FoldingSetNodeID &ID, unsigned long long Val) {
    ID.AddInteger(Val);
  }

  template <typename... Ts>
  bool shouldEmit(StringRef Callback, const Ts &...Args) {
    llvm::FoldingSetNodeID ID;
    add(ID, Callback);
    (add(ID, Args), ...);
    if (Emitted.find_as(ID) != Emitted.end())
      return false;
    Emitted.insert(ID.Intern(Alloc));
    return true;
  }

  template <typename E> static unsigned long long val(E V) {
    return static_cast<unsigned long long>(V);
  }

public:
  explicit DedupThreadSafetyHandler(ThreadSafetyHandler &Inner) : Inner(Inner) {
    setIssueBetaWarnings(Inner.issueBetaWarnings());
  }

  void handleInvalidLockExp(SourceLocation Loc) override {
    Inner.handleInvalidLockExp(Loc);
  }

  void handleUnmatchedUnlock(StringRef Kind, Name LockName, SourceLocation Loc,
                             SourceLocation LocPreviousUnlock) override {
    if (shouldEmit("UnmatchedUnlock", Kind, LockName, Loc, LocPreviousUnlock))
      Inner.handleUnmatchedUnlock(Kind, LockName, Loc, LocPreviousUnlock);
  }

  void handleIncorrectUnlockKind(StringRef Kind, Name LockName,
                                 LockKind Expected, LockKind Received,
                                 SourceLocation LocLocked,
                                 SourceLocation LocUnlock) override {
    Inner.handleIncorrectUnlockKind(Kind, LockName, Expected, Received,
                                    LocLocked, LocUnlock);
  }

  void handleDoubleLock(StringRef Kind, Name LockName, SourceLocation LocLocked,
                        SourceLocation LocDoubleLock) override {
    if (shouldEmit("DoubleLock", Kind, LockName, LocLocked, LocDoubleLock))
      Inner.handleDoubleLock(Kind, LockName, LocLocked, LocDoubleLock);
  }

  void handleMutexHeldEndOfScope(StringRef Kind, Name LockName,
                                 SourceLocation LocLocked,
                                 SourceLocation LocEndOfScope,
                                 LockErrorKind LEK,
                                 bool ReentrancyMismatch = false) override {
    // Different return outcomes may report the same problem with a different
    // acquisition location. Report each problem once.
    if (shouldEmit("MutexHeldEndOfScope", Kind, LockName, LocEndOfScope,
                   val(LEK), val(ReentrancyMismatch)))
      Inner.handleMutexHeldEndOfScope(Kind, LockName, LocLocked, LocEndOfScope,
                                      LEK, ReentrancyMismatch);
  }

  void handleExclusiveAndShared(StringRef Kind, Name LockName,
                                SourceLocation Loc1,
                                SourceLocation Loc2) override {
    if (shouldEmit("ExclusiveAndShared", Kind, LockName, Loc1, Loc2))
      Inner.handleExclusiveAndShared(Kind, LockName, Loc1, Loc2);
  }

  void handleNoMutexHeld(const NamedDecl *D, ProtectedOperationKind POK,
                         AccessKind AK, SourceLocation Loc) override {
    Inner.handleNoMutexHeld(D, POK, AK, Loc);
  }

  void handleGuardedByAnyReadNotHeld(const NamedDecl *D,
                                     ProtectedOperationKind POK,
                                     ArrayRef<StringRef> LockNames,
                                     SourceLocation Loc) override {
    Inner.handleGuardedByAnyReadNotHeld(D, POK, LockNames, Loc);
  }

  void handleMutexNotHeld(StringRef Kind, const NamedDecl *D,
                          ProtectedOperationKind POK, Name LockName,
                          LockKind LK, SourceLocation Loc,
                          Name *PossibleMatch = nullptr) override {
    Inner.handleMutexNotHeld(Kind, D, POK, LockName, LK, Loc, PossibleMatch);
  }

  void handleNegativeNotHeld(StringRef Kind, Name LockName, Name Neg,
                             SourceLocation Loc) override {
    if (shouldEmit("NegativeNotHeld", Kind, LockName, Neg, Loc))
      Inner.handleNegativeNotHeld(Kind, LockName, Neg, Loc);
  }

  void handleNegativeNotHeld(const NamedDecl *D, Name LockName,
                             SourceLocation Loc) override {
    Inner.handleNegativeNotHeld(D, LockName, Loc);
  }

  void handleFunExcludesLock(StringRef Kind, Name FunName, Name LockName,
                             SourceLocation Loc) override {
    if (shouldEmit("FunExcludesLock", Kind, FunName, LockName, Loc))
      Inner.handleFunExcludesLock(Kind, FunName, LockName, Loc);
  }

  void handleLockAcquiredBefore(StringRef Kind, Name L1Name, Name L2Name,
                                SourceLocation Loc) override {
    if (shouldEmit("LockAcquiredBefore", Kind, L1Name, L2Name, Loc))
      Inner.handleLockAcquiredBefore(Kind, L1Name, L2Name, Loc);
  }

  void handleBeforeAfterCycle(Name L1Name, SourceLocation Loc) override {
    if (shouldEmit("BeforeAfterCycle", L1Name, Loc))
      Inner.handleBeforeAfterCycle(L1Name, Loc);
  }

  void handleUnmatchedUnderlyingMutexes(SourceLocation Loc, SourceLocation DLoc,
                                        Name ScopeName, StringRef Kind,
                                        Name Expected, Name Actual) override {
    Inner.handleUnmatchedUnderlyingMutexes(Loc, DLoc, ScopeName, Kind, Expected,
                                           Actual);
  }

  void handleExpectMoreUnderlyingMutexes(SourceLocation Loc,
                                         SourceLocation DLoc, Name ScopeName,
                                         StringRef Kind,
                                         Name Expected) override {
    Inner.handleExpectMoreUnderlyingMutexes(Loc, DLoc, ScopeName, Kind,
                                            Expected);
  }

  void handleExpectFewerUnderlyingMutexes(SourceLocation Loc,
                                          SourceLocation DLoc, Name ScopeName,
                                          StringRef Kind,
                                          Name Actual) override {
    Inner.handleExpectFewerUnderlyingMutexes(Loc, DLoc, ScopeName, Kind,
                                             Actual);
  }

  void enterFunction(const FunctionDecl *FD) override {
    Inner.enterFunction(FD);
  }

  void leaveFunction(const FunctionDecl *FD) override {
    Inner.leaveFunction(FD);
  }
};

} // namespace

void TrylockBodyVerifier::begin(AnalysisDeclContext &AC) {
  for (const auto &Spec : CurrentTrylockExitSpecs)
    CurrentTrylockExitCaps.push_back_nodup(Spec.Cap);

  // Collect the trylock calls whose result the analysis may lose track of.
  const ParentMap &PM = AC.getParentMap();
  CurrentParentMap = &PM;
  auto IsTrackedVar = [&](const ValueDecl *VD) {
    return Analyzer.isTrackableLocalVar(cast<ValueDecl>(VD->getCanonicalDecl()),
                                        EscapedVars);
  };

  auto MarkValueLogicalOps = [&](auto &Self, const Stmt *Root) -> void {
    if (!Root)
      return;
    if (const auto *BO = dyn_cast_or_null<BinaryOperator>(
            stripNoOpExprWrappers(dyn_cast<Expr>(Root)));
        BO && BO->isLogicalOp())
      ValueLogicalOps.insert(BO);
    for (const Stmt *Child : Root->children())
      if (Child)
        Self(Self, Child);
  };

  RPOIdx.assign(NumBlocks, UINT_MAX);
  unsigned CurRPO = 0;
  SmallVector<const CallExpr *, 4> BranchTrylockCalls;
  for (const CFGBlock *B : *SortedGraph) {
    RPOIdx[B->getBlockID()] = CurRPO++;
    for (const CFGElement &BI : *B) {
      std::optional<CFGStmt> CS = BI.getAs<CFGStmt>();
      if (!CS || Analyzer.UnevaluatedStmts.contains(CS->getStmt()))
        continue;
      const Stmt *S = CS->getStmt();
      if (const auto *RS = dyn_cast<ReturnStmt>(S)) {
        MarkValueLogicalOps(MarkValueLogicalOps, RS->getRetValue());
      } else if (const auto *DS = dyn_cast<DeclStmt>(S)) {
        for (const Decl *D : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(D);
              VD && VD->getInit() && IsTrackedVar(VD))
            MarkValueLogicalOps(MarkValueLogicalOps, VD->getInit());
        forEachEvaluatedDeclVLAStmt(
            DS, *Analyzer.ASTCtx, /*IncludeTopLevelVLA=*/false,
            [&](const Stmt *SubS) {
              if (const auto *Call = dyn_cast<CallExpr>(SubS);
                  Call && getTrylockCallee(Call))
                DiscardedCalls.insert(Call);
            });
      } else if (const auto *BO = dyn_cast<BinaryOperator>(S);
                 BO && BO->isAssignmentOp()) {
        if (const auto *DRE = unwrapDirectLValueDRE(BO->getLHS());
            DRE && IsTrackedVar(DRE->getDecl()))
          MarkValueLogicalOps(MarkValueLogicalOps, BO->getRHS());
      } else if (const auto *Call = dyn_cast<CallExpr>(S)) {
        if (getTrylockCallee(Call)) {
          bool ReachedBranchCond = false;
          if (isDiscardedValue(Call, PM, *Analyzer.ASTCtx, IsTrackedVar,
                               &ReachedBranchCond))
            DiscardedCalls.insert(Call);
          else if (ReachedBranchCond)
            BranchTrylockCalls.push_back(Call);
        }
      }
    }
    if (const auto *TermBO =
            dyn_cast_or_null<BinaryOperator>(B->getTerminatorStmt());
        TermBO && TermBO->isLogicalOp()) {
      const Stmt *P = PM.getParent(TermBO);
      while (P && (isa<ParenExpr, FullExpr>(P) ||
                   (isa<BinaryOperator>(P) &&
                    cast<BinaryOperator>(P)->isLogicalOp())))
        P = PM.getParent(P);
      if (!isa_and_nonnull<IfStmt, WhileStmt, ForStmt>(P))
        ValueLogicalOps.insert(TermBO);
    }
  }
  if (!BranchTrylockCalls.empty()) {
    llvm::SmallPtrSet<const CallExpr *, 4> ModeledBranchCalls;
    for (const CFGBlock *B : *SortedGraph) {
      Analyzer.InlineExpansionCount = 0;
      ThreadSafetyAnalyzer::TrylockRangeCondResult CondRes;
      const ThreadSafetyAnalyzer::SwitchCaseTable *Table = nullptr;
      SmallVector<const CastExpr *, 2> SwitchCasts;
      if (Analyzer.getTerminatorTrylockCond(B, CondRes, Table, SwitchCasts))
        ModeledBranchCalls.insert(CondRes.Call);
    }
    for (const CallExpr *Call : BranchTrylockCalls)
      if (!ModeledBranchCalls.contains(Call))
        DiscardedCalls.insert(Call);
  }

  PureExitPathBlocks.assign(NumBlocks, false);
  for (const CFGBlock *B : llvm::reverse(*SortedGraph)) {
    if (B == ExitBlock || B == &CFGraph->getEntry())
      continue;
    if (neverReturns(B) || B->succ_empty())
      continue;

    bool HasNonForwardPred = false;
    for (auto PI = B->pred_begin(), PE = B->pred_end(); PI != PE; ++PI) {
      if (!*PI || RPOIdx[(*PI)->getBlockID()] == UINT_MAX)
        continue;
      if (RPOIdx[(*PI)->getBlockID()] >= RPOIdx[B->getBlockID()] ||
          isa_and_nonnull<ContinueStmt>((*PI)->getTerminatorStmt())) {
        HasNonForwardPred = true;
        break;
      }
    }
    if (HasNonForwardPred)
      continue;

    bool AllSuccsPureToExit = true;
    bool HasReachableSucc = false;
    for (auto SI = B->succ_begin(), SE = B->succ_end(); SI != SE; ++SI) {
      const CFGBlock *Succ = *SI;
      if (!Succ || RPOIdx[Succ->getBlockID()] == UINT_MAX)
        continue;
      HasReachableSucc = true;
      if (RPOIdx[Succ->getBlockID()] <= RPOIdx[B->getBlockID()] ||
          (Succ != ExitBlock && !PureExitPathBlocks[Succ->getBlockID()])) {
        AllSuccsPureToExit = false;
        break;
      }
    }
    if (!HasReachableSucc || !AllSuccsPureToExit)
      continue;

    CapExprSet TCaps;
    Analyzer.getTerminatorTrylockCaps(B, TCaps);
    if (!TCaps.empty())
      continue;

    if (!isPureExitBlock(B, CurrentTrylockExitCaps))
      continue;

    PureExitPathBlocks[B->getBlockID()] = true;
  }

  BlockExitValState.resize(NumBlocks);
  KeepStateForExit.assign(NumBlocks, false);
  for (const CFGBlock *ExitPred : CFGraph->getExit().preds()) {
    if (!ExitPred)
      continue;
    KeepStateForExit[ExitPred->getBlockID()] = true;
    for (const CFGBlock *Q : ExitPred->preds())
      if (Q)
        KeepStateForExit[Q->getBlockID()] = true;
  }
  PureBlockBundles.resize(NumBlocks);
  CollapsedBundles.assign(NumBlocks, false);
  BundleOverflow.assign(NumBlocks, false);
  PreReturnLocksets.resize(NumBlocks);
  PreReturnValStates.resize(NumBlocks);
  PreReturnVarCtx.resize(NumBlocks, Analyzer.LocalVarMap.getEmptyContext());
}

bool TrylockBodyVerifier::sameUnmaterializedDefs(const TrylockValueState &A,
                                                 const TrylockValueState &B) {
  if (A.UnmaterializedVarDefs.size() != B.UnmaterializedVarDefs.size())
    return false;
  for (const auto &[VD, DefPair] : A.UnmaterializedVarDefs) {
    auto It = B.UnmaterializedVarDefs.find(VD);
    if (It == B.UnmaterializedVarDefs.end() ||
        It->second.first != DefPair.first)
      return false;
  }
  return true;
}

bool TrylockBodyVerifier::sameOverwrittenDefs(const TrylockValueState &A,
                                              const TrylockValueState &B) {
  return A.OverwrittenTrylockDefs.size() == B.OverwrittenTrylockDefs.size() &&
         llvm::all_of(A.OverwrittenTrylockDefs, [&](const auto &ADef) {
           return llvm::any_of(B.OverwrittenTrylockDefs, [&](const auto &BDef) {
             return ADef.DefE == BDef.DefE &&
                    ADef.FromEarlierIteration == BDef.FromEarlierIteration;
           });
         });
}

bool TrylockBodyVerifier::sameBundleState(const TrylockEdgeBundle &A,
                                          const TrylockEdgeBundle &B) {
  return factSetsEquivalent(A.Lockset, B.Lockset) &&
         A.ValState.ShortCircuitedOps == B.ValState.ShortCircuitedOps &&
         A.ValState.AcquiredTrylockAttrs == B.ValState.AcquiredTrylockAttrs &&
         A.ValState.ConsumedTrylockAttrs == B.ValState.ConsumedTrylockAttrs &&
         A.ValState.DiscardedTrylockCalls == B.ValState.DiscardedTrylockCalls &&
         sameUnmaterializedDefs(A.ValState, B.ValState) &&
         sameOverwrittenDefs(A.ValState, B.ValState);
}

bool TrylockBodyVerifier::sameCollapsedBundleState(const TrylockEdgeBundle &A,
                                                   const TrylockEdgeBundle &B) {
  return factSetsEquivalent(A.Lockset, B.Lockset) &&
         A.ValState.DiscardedTrylockCalls == B.ValState.DiscardedTrylockCalls &&
         sameUnmaterializedDefs(A.ValState, B.ValState) &&
         sameOverwrittenDefs(A.ValState, B.ValState);
}

// Add Candidate to the bundles of BlockID, merging it with a bundle that
// only differs in its value ranges.
void TrylockBodyVerifier::mergeOrAppendBundle(
    SmallVectorImpl<TrylockEdgeBundle> &Bundles, TrylockEdgeBundle Candidate) {
  for (TrylockEdgeBundle &Existing : Bundles) {
    if (sameBundleState(Existing, Candidate)) {
      unionIntoValueState(Existing.ValState, Candidate.ValState,
                          *Analyzer.ASTCtx);
      return;
    }
  }
  Bundles.push_back(std::move(Candidate));
}

// Merge Candidate with a bundle that has the same lockset and pending trylock
// definitions, widening their value states, or append Candidate if no bundle
// matches.
void TrylockBodyVerifier::collapseAndMergeBundle(
    SmallVectorImpl<TrylockEdgeBundle> &Bundles, TrylockEdgeBundle Candidate) {
  Candidate.ValState.ShortCircuitedOps.clear();
  for (TrylockEdgeBundle &Existing : Bundles) {
    if (sameCollapsedBundleState(Existing, Candidate)) {
      unionIntoValueState(Existing.ValState, Candidate.ValState,
                          *Analyzer.ASTCtx);
      return;
    }
  }
  Bundles.push_back(std::move(Candidate));
}

void TrylockBodyVerifier::addOrMergeBundle(unsigned BlockID,
                                           TrylockEdgeBundle Candidate) {
  if (BundleOverflow[BlockID] || Candidate.ValState.Infeasible)
    return;
  auto &Bundles = PureBlockBundles[BlockID];
  if (CollapsedBundles[BlockID]) {
    collapseAndMergeBundle(Bundles, std::move(Candidate));
  } else {
    mergeOrAppendBundle(Bundles, std::move(Candidate));
    if (Bundles.size() <= MaxBundlesPerBlock)
      return;
    // Too many bundles. Merge bundles that have the same lockset,
    // widening their value states.
    CollapsedBundles[BlockID] = true;
    SmallVector<TrylockEdgeBundle, 2> Old = std::move(Bundles);
    Bundles.clear();
    for (TrylockEdgeBundle &B : Old)
      collapseAndMergeBundle(Bundles, std::move(B));
  }
  if (Bundles.size() <= MaxBundlesPerBlock)
    return;
  BundleOverflow[BlockID] = true;
  Bundles.clear();
}

void TrylockBodyVerifier::intersectFactSetsQuietly(FactSet &Acc,
                                                   const FactSet &Other) {
  FactSet AccOrig = Acc;
  for (const auto &Fact : AccOrig) {
    const FactEntry &AFact = Analyzer.FactMan[Fact];
    const FactEntry *BFact = Other.findLock(Analyzer.FactMan, AFact);
    if (!BFact || AFact.negative() != BFact->negative()) {
      Acc.removeLock(Analyzer.FactMan, AFact);
      continue;
    }
    FactSet::iterator It = Acc.findLockIter(Analyzer.FactMan, AFact);
    if (It == Acc.end())
      continue;
    unsigned DepthA = getFactReentrancyDepth(AFact);
    unsigned DepthB = getFactReentrancyDepth(*BFact);
    if (DepthA != DepthB ? DepthB < DepthA : preferJoinedFact(AFact, *BFact))
      Acc.replaceLock(Analyzer.FactMan, It, BFact);
  }
}

// Compute the lockset and the value state on the edge Pred -> Succ.
TrylockBodyVerifier::TrylockValueState
TrylockBodyVerifier::getEdgeState(const CFGBlock *Pred, const CFGBlock *Succ,
                                  FactSet &Lockset) {
  TrylockValueState State = BlockExitValState[Pred->getBlockID()];
  SmallVector<OverwrittenTrylockDef, 1> MixedEdgeCalls;
  Analyzer.getEdgeLockset(Lockset,
                          Analyzer.BlockInfo[Pred->getBlockID()].ExitSet, Pred,
                          Succ, &State.AcquiredTrylockAttrs,
                          &State.ConsumedTrylockAttrs, &MixedEdgeCalls);
  // Remember the trylock calls that may have succeeded on this edge
  // without the edge implying success, e.g. the false edge of
  // 'if (trylock() == 1)' if trylock() may also return 2 on success.
  for (OverwrittenTrylockDef &Def : MixedEdgeCalls)
    addOverwrittenTrylockDef(State, std::move(Def));
  constrainValueStateOnEdge(State, Pred, Succ);
  materializeNarrowedTrylocks(Lockset, State);
  return State;
}

// Propagate the per-path states of the pure block Pred over the edge
// Pred -> Succ and pass the feasible ones to F.
void TrylockBodyVerifier::forEachEdgeBundle(
    const CFGBlock *Pred, const CFGBlock *Succ,
    llvm::function_ref<void(TrylockEdgeBundle)> F) {
  for (const TrylockEdgeBundle &Bnd : PureBlockBundles[Pred->getBlockID()]) {
    TrylockEdgeBundle Next = Bnd;
    constrainValueStateOnEdge(Next.ValState, Pred, Succ);
    if (Next.ValState.Infeasible)
      continue;
    materializeNarrowedTrylocks(Next.Lockset, Next.ValState);
    F(std::move(Next));
  }
}

void TrylockBodyVerifier::visitExitBlock(CFGBlockInfo *CurrBlockInfo) {
  for (CFGBlock::const_pred_iterator PI = ExitBlock->pred_begin(),
                                     PE = ExitBlock->pred_end();
       PI != PE; ++PI) {
    if (*PI == nullptr || RPOIdx[(*PI)->getBlockID()] == UINT_MAX ||
        !VisitedBlocks.alreadySet(*PI))
      continue;
    if (!neverReturns(*PI) &&
        Analyzer.BlockInfo[(*PI)->getBlockID()].Reachable) {
      CurrBlockInfo->Reachable = true;
      break;
    }
  }
}

void TrylockBodyVerifier::beginBlock(const CFGBlock *B) {
  CurrBlock = B;
  CurrBlockID = B->getBlockID();
  IsPureBlock = PureExitPathBlocks[CurrBlockID];
  CurrValState = TrylockValueState();
  if (CurrBlock != &CFGraph->getEntry())
    CurrValState.Infeasible = true;
  UnvisitedBackPreds.clear();
  PurePredLocksets.clear();
}

void TrylockBodyVerifier::joinPredecessor(const CFGBlock *Pred,
                                          FactSet &PrevLockset) {
  unsigned PrevBlockID = Pred->getBlockID();
  TrylockValueState EdgeValState = getEdgeState(Pred, CurrBlock, PrevLockset);
  if (IsPureBlock) {
    if (BundleOverflow[PrevBlockID]) {
      BundleOverflow[CurrBlockID] = true;
      PureBlockBundles[CurrBlockID].clear();
    } else if (PureExitPathBlocks[PrevBlockID]) {
      forEachEdgeBundle(Pred, CurrBlock, [&](TrylockEdgeBundle Bnd) {
        PurePredLocksets.push_back(Bnd.Lockset);
        addOrMergeBundle(CurrBlockID, std::move(Bnd));
      });
    } else if (!EdgeValState.Infeasible) {
      addOrMergeBundle(CurrBlockID, {PrevLockset, EdgeValState});
    }
  }
  pruneOutOfScopeVars(EdgeValState, CurrBlock);
  if (!CurrValState.Infeasible && !EdgeValState.Infeasible) {
    auto DropNonAcquiringMismatchedDefs = [&](TrylockValueState &S,
                                              const TrylockValueState &Other) {
      SmallVector<const ValueDecl *, 2> ToErase;
      for (const auto &[VD, DefPair] : S.UnmaterializedVarDefs) {
        auto It = Other.UnmaterializedVarDefs.find(VD);
        if (It != Other.UnmaterializedVarDefs.end() &&
            It->second.first == DefPair.first)
          continue;
        auto VR = S.VarRanges.find(VD);
        if (!trylockDefMayAcquire(
                S, DefPair.first, DefPair.second, VD->getType(),
                VR != S.VarRanges.end() ? &VR->second : nullptr))
          ToErase.push_back(VD);
      }
      for (const ValueDecl *VD : ToErase)
        S.UnmaterializedVarDefs.erase(VD);
    };
    DropNonAcquiringMismatchedDefs(CurrValState, EdgeValState);
    DropNonAcquiringMismatchedDefs(EdgeValState, CurrValState);
  }
  unionIntoValueState(CurrValState, EdgeValState, *Analyzer.ASTCtx);
}

void TrylockBodyVerifier::reportOverflowedJoin(
    const CFGBlockInfo *CurrBlockInfo) {
  // The join of a pure block does not report differences in the
  // capabilities that the function is expected to acquire because these
  // are verified per path at the function exit. If there are too many
  // paths to track them separately, report these differences after all.
  if (IsPureBlock && BundleOverflow[CurrBlockID] &&
      PurePredLocksets.size() > 1) {
    CapExprSet TermCaps;
    Analyzer.getTerminatorTrylockCaps(CurrBlock, TermCaps);
    for (const CapabilityExpr &Cap : CurrentTrylockExitCaps) {
      if (llvm::any_of(TermCaps, [&](const CapabilityExpr &TC) {
            return TC.equals(Cap);
          }))
        continue;
      const FactSet *HeldIn = nullptr;
      const FactEntry *Held = nullptr;
      bool MissingSomewhere = false;
      for (const FactSet &L : PurePredLocksets) {
        const FactEntry *FE = L.findLock(Analyzer.FactMan, Cap);
        if (FE && !FE->negative()) {
          if (!Held) {
            Held = FE;
            HeldIn = &L;
          }
        } else {
          MissingSomewhere = true;
        }
      }
      if (Held && MissingSomewhere)
        Held->handleRemovalFromIntersection(
            *HeldIn, Analyzer.FactMan, CurrBlockInfo->EntryLoc,
            LEK_LockedSomePredecessors, Analyzer.Handler);
    }
  }
}

void TrylockBodyVerifier::enterBlock(CFGBlockInfo *CurrBlockInfo) {
  if (IsPureBlock && !BundleOverflow[CurrBlockID]) {
    for (TrylockEdgeBundle &Bnd : PureBlockBundles[CurrBlockID])
      pruneOutOfScopeVars(Bnd.ValState, CurrBlock);
  } else {
    pruneOutOfScopeVars(CurrValState, CurrBlock);
  }
  if (!UnvisitedBackPreds.empty())
    enterLoopHeader();
  if (IsPureBlock && !BundleOverflow[CurrBlockID] &&
      !PureBlockBundles[CurrBlockID].empty()) {
    FactSet BundleEntrySet = PureBlockBundles[CurrBlockID].front().Lockset;
    for (const TrylockEdgeBundle &Bnd :
         llvm::drop_begin(PureBlockBundles[CurrBlockID]))
      intersectFactSetsQuietly(BundleEntrySet, Bnd.Lockset);
    CurrBlockInfo->EntrySet = std::move(BundleEntrySet);
  }
  ValCtxIdx = CurrBlockInfo->EntryIndex;
  ValStmtCtx = CurrBlockInfo->EntryContext;
}

void TrylockBodyVerifier::enterLoopHeader() {
  const CFGBlock *EntryBlock = &CFGraph->getEntry();
  llvm::SmallPtrSet<const CFGBlock *, 16> LoopBlocks;
  SmallVector<const CFGBlock *, 16> Worklist;
  LoopBlocks.insert(CurrBlock);
  for (const CFGBlock *BP : UnvisitedBackPreds)
    if (LoopBlocks.insert(BP).second)
      Worklist.push_back(BP);

  bool IrreducibleLoop = false;
  while (!Worklist.empty()) {
    const CFGBlock *LB = Worklist.pop_back_val();
    if (LB == EntryBlock) {
      IrreducibleLoop = true;
      break;
    }
    for (auto LPI = LB->pred_begin(), LPE = LB->pred_end(); LPI != LPE; ++LPI) {
      const CFGBlock *Pred = *LPI;
      if (!Pred || RPOIdx[Pred->getBlockID()] == UINT_MAX)
        continue;
      if (LoopBlocks.insert(Pred).second)
        Worklist.push_back(Pred);
    }
  }

  if (IrreducibleLoop)
    enterIrreducibleCycle();
  else
    enterNaturalLoop(LoopBlocks);
  CurrValState.ExprRanges.clear();
  CurrValState.ShortCircuitedOps.clear();
}

void TrylockBodyVerifier::eraseModifiedVar(const ValueDecl *VD) {
  retireVarDef(CurrValState, VD, /*NewRHS=*/nullptr);
  CurrValState.VarRanges.erase(VD);
  CurrValState.DerefNonNullVars.erase(VD);
}

// A block of an irreducible cycle may be entered from outside the
// cycle through another block of the cycle. Hence, it is reachable
// even if all its forward predecessor edges are infeasible. Since
// its state is not known, start from an empty state. Keep the trylock
// calls whose capabilities may have been acquired before entering
// the cycle.
void TrylockBodyVerifier::enterIrreducibleCycle() {
  // The blocks of the cycle, i.e. the blocks that can reach CurrBlock
  // and that CurrBlock can reach.
  llvm::SmallPtrSet<const CFGBlock *, 16> CanReach, Cycle;
  SmallVector<const CFGBlock *, 16> Work{CurrBlock};
  CanReach.insert(CurrBlock);
  while (!Work.empty())
    for (const CFGBlock *Pred : Work.pop_back_val()->preds())
      if (Pred && RPOIdx[Pred->getBlockID()] != UINT_MAX &&
          CanReach.insert(Pred).second)
        Work.push_back(Pred);
  Work.push_back(CurrBlock);
  Cycle.insert(CurrBlock);
  while (!Work.empty())
    for (const CFGBlock *Succ : Work.pop_back_val()->succs())
      if (Succ && CanReach.contains(Succ) && Cycle.insert(Succ).second)
        Work.push_back(Succ);
  if (CurrValState.Infeasible) {
    CurrValState = TrylockValueState();
    SmallVector<const CFGBlock *, 16> SortedCycle(Cycle.begin(), Cycle.end());
    llvm::sort(SortedCycle, [this](const CFGBlock *A, const CFGBlock *B) {
      return RPOIdx[A->getBlockID()] < RPOIdx[B->getBlockID()];
    });
    for (const CFGBlock *B : SortedCycle) {
      for (const CFGBlock *Pred : B->preds()) {
        if (!Pred || Cycle.contains(Pred) || !VisitedBlocks.alreadySet(Pred) ||
            neverReturns(Pred) ||
            !Analyzer.BlockInfo[Pred->getBlockID()].Reachable)
          continue;
        const TrylockValueState &PS = BlockExitValState[Pred->getBlockID()];
        if (PS.Infeasible)
          continue;
        CurrValState.DiscardedTrylockCalls.insert(
            PS.DiscardedTrylockCalls.begin(), PS.DiscardedTrylockCalls.end());
        for (const OverwrittenTrylockDef &Def : PS.OverwrittenTrylockDefs)
          addOverwrittenTrylockDef(CurrValState, Def);
        // Sort the variables by source location for deterministic
        // diagnostics.
        SmallVector<std::pair<const ValueDecl *,
                              std::pair<const Expr *, LocalVarContext>>,
                    4>
            Defs(PS.UnmaterializedVarDefs.begin(),
                 PS.UnmaterializedVarDefs.end());
        llvm::sort(Defs, [](const auto &A, const auto &B) {
          return A.first->getLocation().getRawEncoding() <
                 B.first->getLocation().getRawEncoding();
        });
        for (const auto &[VD, Def] : Defs)
          addOverwrittenTrylockDef(
              CurrValState, makeOverwrittenTrylockDef(VD, Def, std::nullopt));
      }
    }
  }
  for (const CFGBlock *B : Cycle)
    for (const ValueDecl *VD :
         Analyzer.LocalVarMap.getBlockModifiedVars(B->getBlockID()))
      eraseModifiedVar(VD);
}

// Forget the values of all variables that the loop modifies, then recover
// the ranges of modified variables whose pre-loop range and back-edge range
// are both known, e.g. for a retry loop that initializes a result variable to
// a failure value and breaks out of the loop when the trylock succeeds.
void TrylockBodyVerifier::enterNaturalLoop(
    const llvm::SmallPtrSetImpl<const CFGBlock *> &LoopBlocks) {
  llvm::SmallDenseMap<const ValueDecl *, IntRangeSet, 4> PreLoopRanges;
  for (const CFGBlock *LB : LoopBlocks) {
    for (const ValueDecl *VD :
         Analyzer.LocalVarMap.getBlockModifiedVars(LB->getBlockID())) {
      if (!CurrValState.UnmaterializedVarDefs.contains(VD))
        if (auto It = CurrValState.VarRanges.find(VD);
            It != CurrValState.VarRanges.end())
          PreLoopRanges.try_emplace(VD, It->second);
      eraseModifiedVar(VD);
    }
  }
  addLoopPendingTrylocks(LoopBlocks);
  CurrValState.ExprRanges.clear();
  CurrValState.ShortCircuitedOps.clear();

  if (CurrValState.Infeasible || PreLoopRanges.empty())
    return;

  for (const CFGBlock *LB : LoopBlocks) {
    if (LB == CurrBlock)
      continue;
    for (const CFGBlock *Pred : LB->preds())
      if (Pred && LoopBlocks.contains(Pred) &&
          RPOIdx[Pred->getBlockID()] >= RPOIdx[LB->getBlockID()])
        return;
  }

  SmallVector<const CFGBlock *, 16> SortedLoopBlocks(LoopBlocks.begin(),
                                                     LoopBlocks.end());
  llvm::sort(SortedLoopBlocks, [this](const CFGBlock *A, const CFGBlock *B) {
    return RPOIdx[A->getBlockID()] < RPOIdx[B->getBlockID()];
  });
  llvm::SmallDenseMap<const CFGBlock *, TrylockValueState, 16> SimExitStates;
  for (const CFGBlock *LB : SortedLoopBlocks) {
    TrylockValueState BState;
    if (LB == CurrBlock) {
      BState = CurrValState;
    } else {
      BState.Infeasible = true;
      for (const CFGBlock *Pred : LB->preds()) {
        if (!Pred || !LoopBlocks.contains(Pred) || neverReturns(Pred))
          continue;
        auto It = SimExitStates.find(Pred);
        if (It == SimExitStates.end() || It->second.Infeasible)
          continue;
        TrylockValueState EdgeState = It->second;
        constrainValueStateOnEdge(EdgeState, Pred, LB);
        unionIntoValueState(BState, EdgeState, *Analyzer.ASTCtx);
      }
      pruneOutOfScopeVars(BState, LB);
    }
    if (!BState.Infeasible) {
      LocalVarContext Ctx = Analyzer.BlockInfo[LB->getBlockID()].EntryContext;
      unsigned CtxIdx = Analyzer.BlockInfo[LB->getBlockID()].EntryIndex;
      for (const CFGElement &BI : *LB) {
        if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
          const Stmt *S = CS->getStmt();
          recordStmtMetadata(S, Ctx);
          updateValueStateForStmt(BState, S, Ctx);
          Ctx = Analyzer.LocalVarMap.getNextContext(CtxIdx, S, Ctx);
        }
      }
    }
    SimExitStates.try_emplace(LB, std::move(BState));
  }

  TrylockValueState BackState;
  BackState.Infeasible = true;
  for (const CFGBlock *BP : UnvisitedBackPreds) {
    if (neverReturns(BP))
      continue;
    auto It = SimExitStates.find(BP);
    if (It == SimExitStates.end() || It->second.Infeasible)
      continue;
    TrylockValueState EdgeState = It->second;
    constrainValueStateOnEdge(EdgeState, BP, CurrBlock);
    unionIntoValueState(BackState, EdgeState, *Analyzer.ASTCtx);
  }

  for (const auto &[VD, EntryR] : PreLoopRanges) {
    if (BackState.Infeasible) {
      CurrValState.VarRanges[VD] = EntryR;
    } else if (auto It = BackState.VarRanges.find(VD);
               It != BackState.VarRanges.end()) {
      IntRangeSet Joined = EntryR.unionWith(It->second);
      Joined.widen(MaxStateRangeIntervals);
      auto Dom = Analyzer.getScalarDomain(VD->getType());
      if (Dom && !IntRangeSet::full(*Dom).subsetOfSet(Joined))
        CurrValState.VarRanges[VD] = std::move(Joined);
    }
  }
}

// The state of the header does not include the back edges, which have not
// been visited yet. Hence, the edges that leave the loop at the header would
// miss the trylock calls of the loop body whose results are discarded or
// overwritten before they are tested, e.g. 'while (cond()) trylock(&mu);'.
// Assume that each of these calls may have been executed and may have
// acquired its capabilities.
void TrylockBodyVerifier::addLoopPendingTrylocks(
    const llvm::SmallPtrSetImpl<const CFGBlock *> &LoopBlocks) {
  if (CurrValState.Infeasible)
    return;

  // The trylock results that a branch condition in the loop tests, and the
  // blocks whose terminators test these. The main pass adds the capabilities
  // of such a result to the lockset on the edges where the result implies
  // success, such that the lockset checks at joins and at the end of loop
  // iterations report capabilities that are not released. Hence, do not add
  // these results if every path from their definition back to the loop
  // header passes such a test.
  llvm::SmallDenseMap<const Expr *, llvm::SmallPtrSet<const CFGBlock *, 2>, 4>
      TestBlocks;
  for (const CFGBlock *B : LoopBlocks) {
    ThreadSafetyAnalyzer::TrylockRangeCondResult CondRes;
    const ThreadSafetyAnalyzer::SwitchCaseTable *Table = nullptr;
    SmallVector<const CastExpr *, 2> SwitchCasts;
    if (!Analyzer.getTerminatorTrylockCond(B, CondRes, Table, SwitchCasts))
      continue;
    SmallVector<IntRangeSet, 4> BranchSets;
    if (Table) {
      for (const auto &[CS, CaseSet] : Table->CaseSets)
        BranchSets.push_back(mapRangeBackwardThroughBijectiveCasts(
            CaseSet, SwitchCasts, CondRes.Dom, *Analyzer.ASTCtx));
      BranchSets.push_back(mapRangeBackwardThroughBijectiveCasts(
          Table->DefaultSet, SwitchCasts, CondRes.Dom, *Analyzer.ASTCtx));
    } else {
      BranchSets.push_back(CondRes.TrueSet);
      BranchSets.push_back(CondRes.FalseSet);
    }
    bool AcquiresOnSomeBranch = false;
    for (const Attr *A : trylockAttrs(CondRes.Callee)) {
      if (!trylockAttrAppliesTo(A, CondRes.Call->getType()))
        continue;
      auto SuccSet = Analyzer.getCombinedTrylockSuccessSet(
          A, CondRes.Call, CondRes.Callee, CondRes.Dom);
      if (!SuccSet)
        continue;
      bool HasSuccessEdge = llvm::any_of(BranchSets, [&](const IntRangeSet &S) {
        return !S.empty() && S.subsetOfSet(*SuccSet);
      });
      bool CleanPartition = llvm::all_of(BranchSets, [&](const IntRangeSet &S) {
        return S.empty() || S.subsetOfSet(*SuccSet) ||
               !S.intersectsSet(*SuccSet);
      });
      if (HasSuccessEdge && CleanPartition) {
        AcquiresOnSomeBranch = true;
        break;
      }
    }
    if (AcquiresOnSomeBranch)
      TestBlocks[stripNoOpExprWrappers(CondRes.Call)].insert(B);
  }

  // Whether every path from the end of DefBlock back to the loop header
  // passes a block in Tests. A path that leaves the loop does not matter: the
  // main pass visits its blocks with the trylock result in the value state.
  auto TestedOnAllBackEdgePaths =
      [&](const CFGBlock *DefBlock,
          const llvm::SmallPtrSetImpl<const CFGBlock *> &Tests) {
        if (Tests.contains(DefBlock))
          return true;
        llvm::SmallPtrSet<const CFGBlock *, 16> Seen;
        SmallVector<const CFGBlock *, 8> Work{DefBlock};
        while (!Work.empty()) {
          for (const CFGBlock *Succ : Work.pop_back_val()->succs()) {
            if (!Succ || !LoopBlocks.contains(Succ))
              continue;
            if (Succ == CurrBlock)
              return false;
            if (!Tests.contains(Succ) && Seen.insert(Succ).second)
              Work.push_back(Succ);
          }
        }
        return true;
      };
  // Whether every trylock call in the definition RHS, e.g. 'trylock()' in
  // 'bool ok = trylock() == 0;', is tested on all paths back to the header.
  auto IsTestedDef = [&](const CFGBlock *DefBlock, const Expr *RHS,
                         LocalVarContext Ctx) {
    llvm::SmallPtrSet<const CallExpr *, 4> DefCalls;
    // DefCalls may be incomplete if the scan exceeds its budget.
    const bool SavedExhausted = ReturnEvalExhausted;
    ReturnEvalExhausted = false;
    exprHasUnmaterializedTrylock(RHS, Ctx, CurrValState,
                                 /*UseStateDefs=*/false,
                                 /*IncludeMaterialized=*/true, &DefCalls);
    const bool Exhausted = ReturnEvalExhausted;
    ReturnEvalExhausted = SavedExhausted;
    return !Exhausted && !DefCalls.empty() &&
           llvm::all_of(DefCalls, [&](const CallExpr *CE) {
             auto It = TestBlocks.find(stripNoOpExprWrappers(CE));
             return It != TestBlocks.end() &&
                    TestedOnAllBackEdgePaths(DefBlock, It->second);
           });
  };

  for (const CFGBlock *B : LoopBlocks) {
    LocalVarContext Ctx = Analyzer.BlockInfo[B->getBlockID()].EntryContext;
    unsigned CtxIdx = Analyzer.BlockInfo[B->getBlockID()].EntryIndex;
    for (const CFGElement &BI : *B) {
      std::optional<CFGStmt> CS = BI.getAs<CFGStmt>();
      if (!CS)
        continue;
      const Stmt *S = CS->getStmt();
      if (!Analyzer.UnevaluatedStmts.contains(S)) {
        auto CheckAssignedRHS = [&](const ValueDecl *VD, const Expr *RHS) {
          if (VD && RHS && Analyzer.isTrackableLocalVar(VD, EscapedVars) &&
              !IsTestedDef(B, RHS, Ctx) &&
              exprHasUnmaterializedTrylock(RHS, Ctx, CurrValState,
                                           /*UseStateDefs=*/false)) {
            OverwrittenTrylockDef Def = makeOverwrittenTrylockDef(
                cast<ValueDecl>(VD->getCanonicalDecl()), {RHS, Ctx},
                std::nullopt);
            Def.FromEarlierIteration = true;
            addOverwrittenTrylockDef(CurrValState, std::move(Def));
          }
        };
        if (const auto *CE = dyn_cast<CallExpr>(S);
            CE && DiscardedCalls.contains(CE)) {
          CurrValState.DiscardedTrylockCalls.insert(CE);
          DiscardedCallCtx.try_emplace(CE, Ctx);
        } else if (const auto *BO = dyn_cast<BinaryOperator>(S);
                   BO && BO->getOpcode() == BO_Assign) {
          if (const DeclRefExpr *DRE = unwrapDirectLValueDRE(BO->getLHS()))
            CheckAssignedRHS(DRE->getDecl(), BO->getRHS());
        } else if (const auto *DS = dyn_cast<DeclStmt>(S)) {
          forEachEvaluatedDeclVLAStmt(
              DS, *Analyzer.ASTCtx, /*IncludeTopLevelVLA=*/false,
              [&](const Stmt *SubS) {
                if (const auto *CE = dyn_cast<CallExpr>(SubS);
                    CE && DiscardedCalls.contains(CE)) {
                  CurrValState.DiscardedTrylockCalls.insert(CE);
                  DiscardedCallCtx.try_emplace(CE, Ctx);
                }
              });
          for (const Decl *D : DS->decls())
            if (const auto *Var = dyn_cast<VarDecl>(D))
              CheckAssignedRHS(Var, Var->getInit());
        }
      }
      Ctx = Analyzer.LocalVarMap.getNextContext(CtxIdx, S, Ctx);
    }
  }
}

void TrylockBodyVerifier::handleStatement(const Stmt *S, const FactSet &FSet) {
  if (isa<ReturnStmt>(S)) {
    PreReturnVarCtx[CurrBlockID] = ValStmtCtx;
    if (!IsPureBlock) {
      PreReturnLocksets[CurrBlockID] = FSet;
      PreReturnValStates[CurrBlockID] = CurrValState;
    }
  }
  if (!S || Analyzer.UnevaluatedStmts.contains(S)) {
    ValStmtCtx = Analyzer.LocalVarMap.getNextContext(ValCtxIdx, S, ValStmtCtx);
    return;
  }
  recordStmtMetadata(S, ValStmtCtx);
  if (!IsPureBlock || BundleOverflow[CurrBlockID]) {
    updateValueStateForStmt(CurrValState, S, ValStmtCtx);
  } else {
    for (auto &Bnd : PureBlockBundles[CurrBlockID])
      updateValueStateForStmt(Bnd.ValState, S, ValStmtCtx);
  }
  ValStmtCtx = Analyzer.LocalVarMap.getNextContext(ValCtxIdx, S, ValStmtCtx);
}

void TrylockBodyVerifier::addReturnedTrylockCaps(
    const ReturnStmt *RS, const ThreadSafetyAnalyzer::ScopeExitCall &Call,
    FactSet &FSet) {
  const Expr *RetVal = RS->getRetValue();
  if (!RetVal || !Call.Callee->hasAttrs())
    return;
  ThreadSafetyAnalyzer::CallLockEffects Effects;
  for (const Attr *At : Call.Callee->attrs())
    Analyzer.collectLockEffects(At, /*Exp=*/nullptr, Call.Callee, Call.Self,
                                Effects);
  auto Released = llvm::concat<const CapabilityExpr>(
      Effects.ExclusiveLocksToRemove, Effects.SharedLocksToRemove,
      Effects.GenericLocksToRemove);
  if (Released.begin() == Released.end())
    return;
  SmallVector<PendingTrylockAcquire, 2> Acquires;
  llvm::SmallPtrSet<const Expr *, 8> Visited;
  collectTrylockAcquires(RetVal, PreReturnVarCtx[CurrBlockID], CurrValState,
                         /*UseStateDefs=*/true, Acquires, Visited,
                         /*Depth=*/0);
  for (const PendingTrylockAcquire &PA : Acquires) {
    if (FSet.findLock(Analyzer.FactMan, PA.Cap) ||
        llvm::none_of(Released, [&](const CapabilityExpr &Cp) {
          return Cp.equals(PA.Cap);
        }))
      continue;
    FSet.removeLock(Analyzer.FactMan, !PA.Cap);
    FSet.addLock(Analyzer.FactMan,
                 Analyzer.FactMan.createFact<LockableFactEntry>(
                     PA.Cap, PA.LK, PA.Loc, FactEntry::Acquired));
  }
}

void TrylockBodyVerifier::exitBlock(const CFGBlockInfo *CurrBlockInfo) {
  bool NeedBlockExitValState = true;
  if (IsPureBlock && !BundleOverflow[CurrBlockID]) {
    for (auto &Bnd : PureBlockBundles[CurrBlockID])
      applyScopeExitCleanups(Bnd.Lockset, CurrBlock,
                             /*OnlyAfterReturn=*/false);
    NeedBlockExitValState =
        llvm::any_of(CurrBlock->succs(), [&](const CFGBlock *Succ) {
          return Succ && Succ != ExitBlock &&
                 RPOIdx[Succ->getBlockID()] != UINT_MAX;
        });
    if (NeedBlockExitValState) {
      CurrValState = TrylockValueState();
      CurrValState.Infeasible = true;
      for (const auto &Bnd : PureBlockBundles[CurrBlockID])
        unionIntoValueState(CurrValState, Bnd.ValState, *Analyzer.ASTCtx);
    }
  }
  if (NeedBlockExitValState) {
    // A trylock call has been consumed if one of the capabilities that it
    // acquired was held when entering this block and has been released by
    // a statement in this block. Capabilities that are dropped while
    // joining locksets, e.g. because the terminator of a block checks the
    // trylock result again, have not been consumed.
    for (const auto &Key : CurrValState.AcquiredTrylockAttrs) {
      if (CurrValState.ConsumedTrylockAttrs.contains(Key))
        continue;
      CapExprSet Caps;
      getAcquiredTrylockCaps(Key, Caps);
      if (llvm::any_of(Caps, [&](const CapabilityExpr &Cap) {
            return CurrBlockInfo->EntrySet.findLock(Analyzer.FactMan, Cap) &&
                   !CurrBlockInfo->ExitSet.findLock(Analyzer.FactMan, Cap);
          }))
        CurrValState.ConsumedTrylockAttrs.insert(Key);
    }
    BlockExitValState[CurrBlockID] = std::move(CurrValState);
  }

  // Free the states of predecessors whose successors have all been
  // visited. Only the exit verification reads them after that, and only
  // for the predecessors of the exit block and their predecessors. This
  // keeps the memory use proportional to the number of live states.
  for (const CFGBlock *Pred : CurrBlock->preds()) {
    if (!Pred || !VisitedBlocks.alreadySet(Pred) ||
        KeepStateForExit[Pred->getBlockID()])
      continue;
    if (llvm::all_of(Pred->succs(), [&](const CFGBlock *Succ) {
          return !Succ || VisitedBlocks.alreadySet(Succ);
        })) {
      BlockExitValState[Pred->getBlockID()] = TrylockValueState();
      PureBlockBundles[Pred->getBlockID()].clear();
    }
  }
}

void TrylockBodyVerifier::verifyExits(const FactSet &ExpectedFunctionExitSet,
                                      const CFGBlockInfo &Final) {
  DedupThreadSafetyHandler DedupHandler(Analyzer.Handler);
  // For each return statement that returns a pointer, the capabilities
  // that the caller holds for every non-null return value and the local
  // variable context of the return statement.
  const bool ReturnsPointer =
      Analyzer.CurrentFunction && Analyzer.CurrentFunction->getReturnType()
                                      .getCanonicalType()
                                      ->isPointerType();
  llvm::MapVector<const ReturnStmt *, PtReturnInfo> PtReturnExpectedSets;

  for (CFGBlock::const_pred_iterator PI = ExitBlock->pred_begin(),
                                     PE = ExitBlock->pred_end();
       PI != PE; ++PI) {
    const CFGBlock *PredBlock = *PI;
    if (!PredBlock || !VisitedBlocks.alreadySet(PredBlock))
      continue;
    unsigned PredID = PredBlock->getBlockID();
    const CFGBlockInfo &PredInfo = Analyzer.BlockInfo[PredID];
    if (neverReturns(PredBlock) || !PredInfo.Reachable)
      continue;

    const ReturnStmt *RS = nullptr;
    for (const CFGElement &BI : llvm::reverse(*PredBlock)) {
      if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
        if ((RS = dyn_cast<ReturnStmt>(CS->getStmt())))
          break;
      }
    }
    SourceLocation DiagLoc = RS ? RS->getBeginLoc() : Final.ExitLoc;
    const Expr *RetVal = RS ? RS->getRetValue() : nullptr;

    LocalVarContext EvalCtx =
        RS ? PreReturnVarCtx[PredID] : PredInfo.ExitContext;
    const ExitContext Exit{PredBlock,
                           PredInfo,
                           RS,
                           RetVal,
                           DiagLoc,
                           EvalCtx,
                           DedupHandler,
                           ExpectedFunctionExitSet,
                           ReturnsPointer,
                           PtReturnExpectedSets};

    // If there are too many distinct lock and value states to track them
    // per path, verify the states per predecessor edge instead. Their
    // number is bounded by the number of CFG edges plus MaxBundlesPerBlock.
    if (PureExitPathBlocks[PredID] && BundleOverflow[PredID]) {
      SmallVector<TrylockEdgeBundle, 2> EdgeBundles;
      for (const CFGBlock *Q : PredBlock->preds()) {
        if (!Q || !VisitedBlocks.alreadySet(Q) || neverReturns(Q) ||
            !Analyzer.BlockInfo[Q->getBlockID()].Reachable)
          continue;
        unsigned QID = Q->getBlockID();
        if (PureExitPathBlocks[QID] && !BundleOverflow[QID] &&
            (PureBlockBundles[QID].size() <= 1 ||
             EdgeBundles.size() + PureBlockBundles[QID].size() <=
                 MaxBundlesPerBlock)) {
          forEachEdgeBundle(Q, PredBlock, [&](TrylockEdgeBundle Bnd) {
            collapseAndMergeBundle(EdgeBundles, std::move(Bnd));
          });
          continue;
        }
        FactSet EdgeLockset;
        TrylockValueState EdgeState = getEdgeState(Q, PredBlock, EdgeLockset);
        if (!EdgeState.Infeasible)
          collapseAndMergeBundle(
              EdgeBundles, {std::move(EdgeLockset), std::move(EdgeState)});
      }
      for (TrylockEdgeBundle &Bnd : EdgeBundles)
        verifyEdgeState(Exit, std::move(Bnd.Lockset), std::move(Bnd.ValState));
    } else if (PureExitPathBlocks[PredID]) {
      for (const TrylockEdgeBundle &Bnd : PureBlockBundles[PredID])
        verifyReturn(Exit, Bnd.Lockset, Bnd.ValState);
    } else if (RS) {
      verifyReturn(Exit, PreReturnLocksets[PredID], PreReturnValStates[PredID]);
    } else {
      // Control flows off the end of the function. Take the trylock calls
      // into account whose result is not stored anywhere.
      verifyReturn(Exit, PredInfo.ExitSet, BlockExitValState[PredID]);
    }
  }

  // Check that the caller holds the capabilities that protect the pointee
  // of a returned pointer for every non-null value that may be returned.
  for (const auto &[RS, Info] : PtReturnExpectedSets) {
    if (!Info.Expected)
      continue;
    ThreadSafetyAnalyzer::LocalVarLookupScope Lookup(Analyzer, Info.Ctx);
    const AccessKind AK = Analyzer.CurrentFunction->getReturnType()
                                  ->getPointeeType()
                                  .isConstQualified()
                              ? AK_Read
                              : AK_Written;
    ReturnedPtrWalk Walk;
    checkReturnedPointerExpr(RS->getRetValue(), Info.Ctx, Info.Expected, AK,
                             Walk);
  }
}

// Verify the lock state at the exit for each value that the function
// may return if it leaves Exit.PredBlock with Lockset and State.
void TrylockBodyVerifier::verifyReturn(const ExitContext &Exit,
                                       const FactSet &Lockset,
                                       TrylockValueState State) {
  const auto &[PredBlock, PredInfo, RS, RetVal, DiagLoc, EvalCtx, DedupHandler,
               ExpectedFunctionExitSet, ReturnsPointer, PtReturnExpectedSets] =
      Exit;
  if (!RS) {
    constrainValueStateOnEdge(State, PredBlock, ExitBlock);
    if (State.Infeasible)
      return;
  }
  Analyzer.InlineExpansionCount = 0;
  SmallVector<ReturnEvalOutcome, 2> Outcomes;
  evaluateReturnWithPendingTrylocks(RetVal, Lockset, State, EvalCtx, Outcomes);
  for (ReturnEvalOutcome &Outcome : Outcomes) {
    FactSet MaySet;
    for (auto It = Outcome.PendingAcquires.begin();
         It != Outcome.PendingAcquires.end(); ++It) {
      const PendingTrylockAcquire &PA = *It;
      const FactEntry *FE = Analyzer.FactMan.createFact<LockableFactEntry>(
          PA.Cap, PA.LK, PA.Loc, FactEntry::Acquired);
      if (PA.MayOnly) {
        if (!MaySet.findLock(Analyzer.FactMan, *FE))
          MaySet.addLock(Analyzer.FactMan, FE);
        continue;
      }
      if (llvm::any_of(llvm::make_range(Outcome.PendingAcquires.begin(), It),
                       [&](const PendingTrylockAcquire &Prev) {
                         return !Prev.MayOnly && Prev.LK == PA.LK &&
                                Prev.Loc == PA.Loc && Prev.Cap.equals(PA.Cap);
                       }))
        continue;
      Analyzer.addLock(Outcome.Lockset, FE, /*ReqAttr=*/false, &DedupHandler);
    }
    applyScopeExitCleanups(Outcome.Lockset, PredBlock,
                           /*OnlyAfterReturn=*/true, &Lockset, &DedupHandler);
    applyScopeExitCleanups(MaySet, PredBlock,
                           /*OnlyAfterReturn=*/true);
    std::optional<FactSet> *NonNullExpectedSet = nullptr;
    if (ReturnsPointer && RetVal)
      NonNullExpectedSet =
          &PtReturnExpectedSets
               .try_emplace(RS, PtReturnInfo{std::nullopt, EvalCtx})
               .first->second.Expected;
    checkTrylockExitOutcome(ExpectedFunctionExitSet, Outcome, DiagLoc,
                            DedupHandler, NonNullExpectedSet, &MaySet);
  }
}

void TrylockBodyVerifier::verifyEdgeState(const ExitContext &Exit,
                                          FactSet Lockset,
                                          TrylockValueState State) {
  const auto &[PredBlock, PredInfo, RS, RetVal, DiagLoc, EvalCtx, DedupHandler,
               ExpectedFunctionExitSet, ReturnsPointer, PtReturnExpectedSets] =
      Exit;
  unsigned Idx = PredInfo.EntryIndex;
  LocalVarContext Ctx = PredInfo.EntryContext;
  for (const CFGElement &BI : *PredBlock) {
    std::optional<CFGStmt> CS = BI.getAs<CFGStmt>();
    if (!CS)
      continue;
    const Stmt *S = CS->getStmt();
    if (Analyzer.UnevaluatedStmts.contains(S))
      continue;
    if (S == RS)
      break;
    updateValueStateForStmt(State, S, Ctx);
    Ctx = Analyzer.LocalVarMap.getNextContext(Idx, S, Ctx);
  }
  if (State.Infeasible)
    return;
  // Apply the lock effects of PredBlock that precede its return
  // statement, e.g. an unlock before the return.
  applyScopeExitCleanups(Lockset, PredBlock,
                         /*OnlyAfterReturn=*/false);
  verifyReturn(Exit, Lockset, std::move(State));
}

/// Return the pointer \p P such that checking the address \p E with
/// checkPtAccess() checks the pointee of \p P, or null if \p E is not the
/// address of an object that is accessed through a pointer. E.g. return 'p'
/// for '&*p', '&p->field', '&(*p).field', '&p[i]', 'p->arr', '&p->arr[0]' and
/// '*p_arr' if 'p_arr' points to an array. Set \p RefVD if the access is
/// through a local reference variable, e.g. 'r' in 'int &r = *p; &r'. This
/// mirrors how checkPtAccess() and checkAccess() look through these
/// expressions.
static const Expr *getAccessedPointer(const Expr *E, const VarDecl *&RefVD) {
  // The pointer whose pointee the lvalue LV designates, as checkAccess()
  // determines it.
  auto LValuePointer = [&](auto &Self, const Expr *LV) -> const Expr * {
    LV = LV->IgnoreImplicit()->IgnoreParenCasts();
    while (const auto *DRE = dyn_cast<DeclRefExpr>(LV)) {
      const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()->getCanonicalDecl());
      if (!VD || !VD->isLocalVarDecl() || !VD->getType()->isReferenceType())
        break;
      const Expr *Init = VD->getInit();
      if (!Init || Init == LV)
        break;
      RefVD = VD;
      LV = Init->IgnoreImplicit()->IgnoreParenCasts();
    }
    if (const auto *UO = dyn_cast<UnaryOperator>(LV))
      return UO->getOpcode() == UO_Deref ? UO->getSubExpr() : nullptr;
    if (const auto *BO = dyn_cast<BinaryOperator>(LV)) {
      if (BO->getOpcode() == BO_PtrMemD)
        return Self(Self, BO->getLHS());
      if (BO->getOpcode() == BO_PtrMemI)
        return BO->getLHS();
      return nullptr;
    }
    if (const auto *ASE = dyn_cast<ArraySubscriptExpr>(LV)) {
      const Expr *Base = ASE->getLHS();
      for (const Expr *B = Base;;) {
        if (const auto *PE = dyn_cast<ParenExpr>(B)) {
          B = PE->getSubExpr();
          continue;
        }
        if (const auto *CE = dyn_cast<CastExpr>(B)) {
          if (CE->getCastKind() == CK_ArrayToPointerDecay)
            return Self(Self, CE->getSubExpr());
          B = CE->getSubExpr();
          continue;
        }
        break;
      }
      return Base;
    }
    if (const auto *ME = dyn_cast<MemberExpr>(LV))
      return ME->isArrow() ? ME->getBase() : Self(Self, ME->getBase());
    return nullptr;
  };
  while (true) {
    if (const auto *PE = dyn_cast<ParenExpr>(E)) {
      E = PE->getSubExpr();
      continue;
    }
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (CE->getCastKind() == CK_ArrayToPointerDecay)
        return LValuePointer(LValuePointer, CE->getSubExpr());
      E = CE->getSubExpr();
      continue;
    }
    break;
  }
  if (const auto *UO = dyn_cast<UnaryOperator>(E);
      UO && UO->getOpcode() == UO_AddrOf)
    return LValuePointer(LValuePointer, UO->getSubExpr());
  return nullptr;
}

void TrylockBodyVerifier::checkReturnedPointerExpr(
    const Expr *E, LocalVarContext CurCtx,
    const std::optional<FactSet> &Expected, AccessKind AK,
    ReturnedPtrWalk &Walk, bool Checked) {
  // Checking an expression again in the same local variable context would not
  // find anything new. Stopping there also prevents infinite recursion for
  // definitions in loops, e.g. 'p = p + 1'. Limit the total number of steps
  // since every definition may be reached along multiple paths.
  if (!E || Walk.StepsLeft == 0 ||
      !Walk.Visited.insert({E, CurCtx.getRootWithoutRetain()}).second)
    return;
  --Walk.StepsLeft;
  const Expr *Stripped = E->IgnoreParenCasts();
  if (!Checked) {
    LocalVarLookupScope Scope(Analyzer, CurCtx);
    Analyzer.checkPtAccess(*Expected, E, AK, POK_ReturnPointer);
  }
  // checkPtAccess() checks the pointee of P for '&*P', '&P->field', 'P->arr'
  // etc. like for 'P'. Trace the definitions of P if it is a local pointer
  // variable, without checking P itself again.
  const VarDecl *RefVD = nullptr;
  if (const Expr *P = getAccessedPointer(E, RefVD)) {
    // A local reference variable is bound to the object that P points to
    // where the reference is initialized, e.g. in 'int &r = *p;'. Check the
    // definitions of P that reach that point rather than the definition of P
    // in CurCtx.
    LocalVarContext PtrCtx =
        RefVD ? Analyzer.LocalVarMap.lookupRefVarInitContext(RefVD, CurCtx)
              : CurCtx;
    checkReturnedPointerExpr(P, PtrCtx, Expected, AK, Walk, /*Checked=*/true);
    return;
  }
  if (const auto *BO = dyn_cast<BinaryOperator>(Stripped)) {
    if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign) {
      checkReturnedPointerExpr(BO->getRHS(), CurCtx, Expected, AK, Walk);
      return;
    }
    if (BO->isAdditiveOp()) {
      if (BO->getLHS()->getType()->isPointerType())
        checkReturnedPointerExpr(BO->getLHS(), CurCtx, Expected, AK, Walk);
      else if (BO->getRHS()->getType()->isPointerType())
        checkReturnedPointerExpr(BO->getRHS(), CurCtx, Expected, AK, Walk);
      return;
    }
    if (BO->getOpcode() == BO_AddAssign || BO->getOpcode() == BO_SubAssign) {
      checkReturnedPointerExpr(BO->getLHS(), CurCtx, Expected, AK, Walk);
      return;
    }
  }
  if (const auto *UO = dyn_cast<UnaryOperator>(Stripped)) {
    if (UO->isIncrementDecrementOp()) {
      checkReturnedPointerExpr(UO->getSubExpr(), CurCtx, Expected, AK, Walk);
      return;
    }
  }
  if (const auto *CO = dyn_cast<ConditionalOperator>(Stripped)) {
    checkReturnedPointerExpr(CO->getTrueExpr(), CurCtx, Expected, AK, Walk);
    checkReturnedPointerExpr(CO->getFalseExpr(), CurCtx, Expected, AK, Walk);
    return;
  }
  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(Stripped)) {
    checkReturnedPointerExpr(BCO->getCommon(), CurCtx, Expected, AK, Walk);
    checkReturnedPointerExpr(BCO->getFalseExpr(), CurCtx, Expected, AK, Walk);
    return;
  }
  if (const auto *SE = dyn_cast<StmtExpr>(Stripped)) {
    if (const CompoundStmt *CS = SE->getSubStmt(); CS && !CS->body_empty())
      if (const auto *LastE = dyn_cast<Expr>(CS->body_back()))
        checkReturnedPointerExpr(LastE, CurCtx, Expected, AK, Walk);
    return;
  }
  if (const auto *DRE = dyn_cast<DeclRefExpr>(Stripped)) {
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()->getCanonicalDecl());
        VD && VD->hasLocalStorage() && VD->getType()->isPointerType()) {
      LocalVarContext LookupCtx = CurCtx;
      if (const Expr *DefE = Analyzer.LocalVarMap.lookupExpr(VD, LookupCtx)) {
        checkReturnedPointerExpr(DefE, LookupCtx, Expected, AK, Walk);
      } else if (Analyzer.isTrackableLocalVar(VD, EscapedVars)) {
        SmallVector<std::pair<const Expr *, LocalVarContext>, 2> Defs;
        Analyzer.LocalVarMap.collectDefinitions(VD, CurCtx, *Analyzer.ASTCtx,
                                                Defs);
        for (const auto &[DefE, DefCtx] : Defs)
          checkReturnedPointerExpr(DefE, DefCtx, Expected, AK, Walk);
      }
    }
  }
}
