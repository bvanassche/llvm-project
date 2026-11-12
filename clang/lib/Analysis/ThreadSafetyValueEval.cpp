//===- ThreadSafetyValueEval.cpp - Expression value evaluation ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Expression range evaluation, condition constraint propagation, and local
// variable escape/modification scanning for the thread safety analysis.
//
//===----------------------------------------------------------------------===//

#include "ThreadSafetyInternal.h"
#include "clang/AST/IgnoreExpr.h"
#include "llvm/ADT/SetOperations.h"
#include "llvm/Support/SaveAndRestore.h"

using namespace clang;
using namespace threadSafety;

static bool isValuePreservingIntegralCast(QualType SrcTy, QualType DstTy,
                                          const ASTContext &Ctx) {
  if (!SrcTy->isIntegralOrEnumerationType() ||
      !DstTy->isIntegralOrEnumerationType() || DstTy->isBooleanType())
    return false;
  if (const auto *ED = SrcTy->getAsEnumDecl(); ED && !ED->isComplete())
    return false;
  if (const auto *ED = DstTy->getAsEnumDecl(); ED && !ED->isComplete())
    return false;
  unsigned SrcBits = Ctx.getIntWidth(SrcTy);
  unsigned DstBits = Ctx.getIntWidth(DstTy);
  if (DstBits < SrcBits)
    return false;
  bool SrcUnsigned = SrcTy->isUnsignedIntegerOrEnumerationType();
  bool DstUnsigned = DstTy->isUnsignedIntegerOrEnumerationType();
  return SrcUnsigned == DstUnsigned || (SrcUnsigned && DstBits > SrcBits);
}

/// Whether \p CE is a user-defined conversion through a conversion function,
/// e.g. 'operator bool()'. The operand of such a cast is the call of the
/// conversion function, whose value is the value of the cast.
bool threadSafety::isConversionFunctionCast(const CastExpr *CE) {
  return CE->getCastKind() == CK_UserDefinedConversion &&
         isa<CXXMemberCallExpr>(CE->getSubExpr()->IgnoreParens()) &&
         CE->getType().getCanonicalType().getUnqualifiedType() ==
             CE->getSubExpr()
                 ->getType()
                 .getCanonicalType()
                 .getUnqualifiedType();
}

bool threadSafety::isValuePreservingCast(const CastExpr *CE,
                                         const ASTContext &Ctx) {
  QualType SubTy = CE->getSubExpr()->getType();
  QualType DstTy = CE->getType();
  switch (CE->getCastKind()) {
  case CK_LValueToRValue:
  case CK_NoOp:
    return true;
  case CK_UserDefinedConversion:
    return isConversionFunctionCast(CE);
  case CK_IntegralCast:
    return isValuePreservingIntegralCast(SubTy, DstTy, Ctx);
  case CK_BitCast:
    return DstTy->isAnyPointerType() && SubTy->isAnyPointerType();
  case CK_PointerToIntegral:
    return SubTy->isAnyPointerType() &&
           DstTy->isUnsignedIntegerOrEnumerationType() &&
           !DstTy->isBooleanType() &&
           Ctx.getIntWidth(DstTy) >= Ctx.getIntWidth(Ctx.getUIntPtrType());
  case CK_IntegralToPointer:
    return DstTy->isAnyPointerType() &&
           SubTy->isUnsignedIntegerOrEnumerationType() &&
           !SubTy->isBooleanType() &&
           Ctx.getIntWidth(SubTy) <= Ctx.getIntWidth(Ctx.getUIntPtrType());
  default:
    return false;
  }
}

bool threadSafety::isBuiltinExpectCall(const CallExpr *CallExp) {
  unsigned BuiltinID = CallExp->getBuiltinCallee();
  return BuiltinID == Builtin::BI__builtin_expect ||
         BuiltinID == Builtin::BI__builtin_expect_with_probability;
}

/// Skip the expressions that do not change the value of \p E: parentheses,
/// full expressions, value-preserving casts, __builtin_expect(), statement
/// expressions that consist of a single expression and calls of inline
/// helpers that return their argument unchanged. If \p C is not null, also
/// look through local variables to their known definitions and update \p C
/// to the context of the definition. If \p IgnoreSideEffects is set, also
/// look through assignments and statement expressions with multiple
/// statements. That is only correct if the caller does not reason about the
/// values of variables, e.g. if it only determines the call that produced a
/// value. Returns the first expression that is not such a wrapper.
const Expr *ThreadSafetyAnalyzer::skipValuePreservingWrappers(
    const Expr *E, LocalVarContext *C, bool IgnoreSideEffects) {
  while (E) {
    E = stripNoOpExprWrappers(E);
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (!isValuePreservingCast(CE, *ASTCtx))
        return E;
      E = CE->getSubExpr();
      continue;
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      const Expr *Def =
          C ? LocalVarMap.lookupValueExpr(DRE->getDecl(), *C) : nullptr;
      if (!Def)
        return E;
      E = Def;
      continue;
    }
    if (const auto *BOP = dyn_cast<BinaryOperator>(E)) {
      if (!IgnoreSideEffects || BOP->getOpcode() != BO_Assign ||
          BOP->getLHS()->refersToBitField())
        return E;
      E = BOP->getRHS();
      continue;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(E)) {
      if (IgnoreSideEffects) {
        const CompoundStmt *CS = SE->getSubStmt();
        if (!CS || CS->body_empty())
          return E;
        E = dyn_cast<Expr>(CS->body_back());
        continue;
      }
      if (const Expr *Inner = getCachedPureStmtExpr(SE)) {
        E = Inner;
        continue;
      }
      return E;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      if (isBuiltinExpectCall(CallExp)) {
        E = CallExp->getArg(0);
        continue;
      }
      if (auto ParamIdx = getIdentityInlineParamIndex(CallExp)) {
        E = CallExp->getArg(*ParamIdx);
        continue;
      }
      return E;
    }
    return E;
  }
  return nullptr;
}

const CallExpr *
ThreadSafetyAnalyzer::unwrapValuePreservingToCallExpr(const Expr *E,
                                                      LocalVarContext &C) {
  return dyn_cast_or_null<CallExpr>(skipValuePreservingWrappers(E, &C));
}

const CallExpr *
ThreadSafetyAnalyzer::unwrapTrylockValueExpr(const Expr *E,
                                             LocalVarContext &C) {
  const CallExpr *CallExp = unwrapValuePreservingToCallExpr(E, C);
  return getTrylockCallee(CallExp) ? CallExp : nullptr;
}

bool ThreadSafetyAnalyzer::isGuaranteedZeroOrOneExpr(const Expr *E,
                                                     LocalVarContext C) {
  if (!E)
    return false;
  auto IsZeroOrOneLeaf = [&](const Expr *Leaf) -> std::optional<bool> {
    if (Leaf->getType()->isBooleanType())
      return true;
    if (Leaf->getType()->isIntegralOrEnumerationType())
      if (auto ICE = evaluateRuntimeIntConstant(Leaf, *ASTCtx))
        return *ICE == 0 || *ICE == 1;
    return std::nullopt;
  };
  if (auto Res = IsZeroOrOneLeaf(E))
    return *Res;
  E = skipValuePreservingWrappers(E, &C);
  if (!E)
    return false;
  if (auto Res = IsZeroOrOneLeaf(E))
    return *Res;
  if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
    const TrivialInlineBody *InlineInfo = getCachedTrivialInlineBody(CallExp);
    if (!InlineInfo)
      return false;
    InlineExpansionScope Scope(*this, *InlineInfo);
    LocalVarContext EmptyCtx = LocalVarMap.getEmptyContext();
    if (InlineInfo->SingleRet)
      return isGuaranteedZeroOrOneExpr(InlineInfo->SingleRet, EmptyCtx);
    return isGuaranteedZeroOrOneExpr(InlineInfo->ThenRet, EmptyCtx) &&
           isGuaranteedZeroOrOneExpr(InlineInfo->ElseRet, EmptyCtx);
  }
  if (const auto *UOP = dyn_cast<UnaryOperator>(E))
    return UOP->getOpcode() == UO_LNot;
  if (const auto *BOP = dyn_cast<BinaryOperator>(E))
    return BOP->isRelationalOp() || BOP->isEqualityOp() || BOP->isLogicalOp();
  return false;
}

static Expr *ignoreFullExprOrOpaqueValueSingleStep(Expr *E) {
  if (auto *FE = dyn_cast<FullExpr>(E))
    return FE->getSubExpr();
  if (auto *OVE = dyn_cast<OpaqueValueExpr>(E))
    if (Expr *Src = OVE->getSourceExpr())
      return Src;
  return E;
}

const Expr *threadSafety::stripNoOpExprWrappers(const Expr *E) {
  if (!E)
    return nullptr;
  return IgnoreExprNodes(E, IgnoreParensSingleStep,
                         ignoreFullExprOrOpaqueValueSingleStep,
                         ignoreNoOpCastSingleStep);
}

static void visitEvaluatedStmts(const Stmt *Root, const ASTContext &Ctx,
                                llvm::function_ref<void(const Stmt *)> Fn) {
  if (!Root)
    return;
  SmallVector<const Stmt *, 16> Worklist = {Root};
  while (!Worklist.empty()) {
    const Stmt *S = Worklist.pop_back_val();
    if (!S)
      continue;
    if (const auto *CE = dyn_cast<CallExpr>(S);
        CE && CE->isUnevaluatedBuiltinCall(Ctx))
      continue;
    if (isa<CXXNoexceptExpr>(S))
      continue;
    if (const auto *TE = dyn_cast<UnaryExprOrTypeTraitExpr>(S)) {
      if (isEvaluatedUnaryExprOrTypeTrait(TE))
        llvm::append_range(Worklist, TE->children());
      continue;
    }
    if (const auto *TE = dyn_cast<CXXTypeidExpr>(S)) {
      if (!TE->isTypeOperand() && TE->isPotentiallyEvaluated())
        Worklist.push_back(TE->getExprOperand());
      continue;
    }
    if (const auto *GSE = dyn_cast<GenericSelectionExpr>(S)) {
      if (!GSE->isResultDependent())
        Worklist.push_back(GSE->getResultExpr());
      continue;
    }
    Fn(S);
    if (const auto *DS = dyn_cast<DeclStmt>(S))
      forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/true,
                         [&](const Expr *Sz) { Worklist.push_back(Sz); });
    llvm::append_range(Worklist, S->children());
  }
}

void threadSafety::forEachEvaluatedDeclVLAStmt(
    const DeclStmt *DS, const ASTContext &Ctx, bool IncludeTopLevelVLA,
    llvm::function_ref<void(const Stmt *)> Fn) {
  forEachDeclVLAExpr(DS, IncludeTopLevelVLA,
                     [&](const Expr *Sz) { visitEvaluatedStmts(Sz, Ctx, Fn); });
}

namespace {
/// Merges deduplicated variable lists across AST children while reusing a
/// child's existing BumpPtrAllocator-backed ArrayRef whenever one child's set
/// already contains all variables of the other children.
class SubtreeVarMerger {
  llvm::ArrayRef<const ValueDecl *> Current;
  SmallVector<const ValueDecl *, 4> Scratch;
  bool UsingScratch = false;

public:
  void add(const ValueDecl *VD) {
    if (!VD)
      return;
    if (UsingScratch) {
      if (!llvm::is_contained(Scratch, VD))
        Scratch.push_back(VD);
      return;
    }
    if (llvm::is_contained(Current, VD))
      return;
    Scratch.assign(Current.begin(), Current.end());
    Scratch.push_back(VD);
    UsingScratch = true;
  }

  void merge(llvm::ArrayRef<const ValueDecl *> Other) {
    if (Other.empty())
      return;
    if (!UsingScratch) {
      if (Current.empty()) {
        Current = Other;
        return;
      }
      if (Current.data() == Other.data() && Current.size() == Other.size())
        return;
      if (Current.size() >= Other.size() &&
          llvm::all_of(Other, [&](const ValueDecl *VD) {
            return llvm::is_contained(Current, VD);
          }))
        return;
      if (Other.size() > Current.size() &&
          llvm::all_of(Current, [&](const ValueDecl *VD) {
            return llvm::is_contained(Other, VD);
          })) {
        Current = Other;
        return;
      }
      if (Other.size() > Current.size()) {
        Scratch.assign(Other.begin(), Other.end());
        Other = Current;
      } else {
        Scratch.assign(Current.begin(), Current.end());
      }
      UsingScratch = true;
    }
    for (const ValueDecl *VD : Other)
      if (!llvm::is_contained(Scratch, VD))
        Scratch.push_back(VD);
  }

  llvm::ArrayRef<const ValueDecl *>
  finalize(llvm::BumpPtrAllocator &Bpa) const {
    if (!UsingScratch)
      return Current;
    return llvm::ArrayRef(Scratch).copy(Bpa);
  }
};

/// The prototype of the function that the indirect call \p CE calls, if
/// known, e.g. for a call through a function pointer, a block or a pointer to
/// member function.
static const FunctionProtoType *getIndirectCalleeProtoType(const CallExpr *CE) {
  if (CE->getDirectCallee() || isa<CXXOperatorCallExpr>(CE))
    return nullptr;
  const Expr *Callee = CE->getCallee()->IgnoreParens();
  QualType T = Callee->getType();
  if (const auto *BO = dyn_cast<BinaryOperator>(Callee); BO && BO->isPtrMemOp())
    T = BO->getRHS()->getType();
  if (const auto *MPT = T->getAs<MemberPointerType>())
    T = MPT->getPointeeType();
  else if (const auto *PT = T->getAs<PointerType>())
    T = PT->getPointeeType();
  else if (const auto *BPT = T->getAs<BlockPointerType>())
    T = BPT->getPointeeType();
  return T->getAs<FunctionProtoType>();
}

static bool isConstRefType(QualType T) {
  return T->isReferenceType() && T->getPointeeType().isConstQualified();
}

/// The type of parameter \p ParamIdx of the callee \p FD or, if \p FD is
/// null, of the prototype \p Proto, or a null type if it is not known.
static QualType getCallParamType(const FunctionDecl *FD,
                                 const FunctionProtoType *Proto,
                                 unsigned ParamIdx) {
  if (FD)
    return ParamIdx < FD->getNumParams() ? FD->getParamDecl(ParamIdx)->getType()
                                         : QualType();
  if (Proto && ParamIdx < Proto->getNumParams())
    return Proto->getParamType(ParamIdx);
  return QualType();
}

static bool
isSafeCallOrCtorLValueArg(const FunctionDecl *FD, bool HasImplicitObjArg,
                          unsigned Idx,
                          const FunctionProtoType *Proto = nullptr) {
  if (HasImplicitObjArg && Idx == 0)
    return cast<CXXMethodDecl>(FD)->isConst();
  unsigned ParamIdx = HasImplicitObjArg ? Idx - 1 : Idx;
  QualType ParamType = getCallParamType(FD, Proto, ParamIdx);
  return !ParamType.isNull() && isConstRefType(ParamType);
}

/// The type of the parameter of the callee of \p CE that argument \p Idx
/// initializes, or a null type if it is not known.
static QualType getCallArgParamType(const CallExpr *CE, unsigned Idx) {
  const FunctionDecl *FD = CE->getDirectCallee();
  if (const auto *MD = dyn_cast_or_null<CXXMethodDecl>(FD);
      MD && isa<CXXOperatorCallExpr>(CE)) {
    if (MD->isStatic() || MD->isImplicitObjectMemberFunction()) {
      // The first argument is the object expression.
      if (Idx == 0)
        return QualType();
      --Idx;
    }
  }
  return getCallParamType(FD, getIndirectCalleeProtoType(CE), Idx);
}

static bool isSafeCallLValueArg(const CallExpr *CE, unsigned Idx) {
  const FunctionDecl *FD = CE->getDirectCallee();
  bool HasImplicitObjArg = false;
  if (const auto *MD = dyn_cast_or_null<CXXMethodDecl>(FD);
      MD && isa<CXXOperatorCallExpr>(CE)) {
    if (MD->isStatic()) {
      if (Idx == 0)
        return true;
      return isSafeCallOrCtorLValueArg(FD, /*HasImplicitObjArg=*/false,
                                       Idx - 1);
    }
    HasImplicitObjArg = MD->isImplicitObjectMemberFunction();
  }
  return isSafeCallOrCtorLValueArg(FD, HasImplicitObjArg, Idx,
                                   getIndirectCalleeProtoType(CE));
}

/// Whether the result of the call \p CE cannot designate or point to an
/// argument of the call, such that the callee cannot pass on the address of
/// an argument through its result.
static bool callResultCannotAliasArgs(const CallExpr *CE) {
  QualType T = CE->getType();
  return CE->isPRValue() &&
         (T->isVoidType() || T->isArithmeticType() || T->isEnumeralType());
}

/// Whether \p ParamType is a pointer to a const-qualified type or a reference
/// to such a pointer.
static bool isConstPointeeParamType(QualType ParamType) {
  if (ParamType.isNull())
    return false;
  QualType T = ParamType.getNonReferenceType();
  return T->isPointerType() && T->getPointeeType().isConstQualified();
}

/// Helper class for scanTrylockVars() and getSubtreeModifiedVars() that
/// recursively visits a statement and collects the escaped and the modified
/// local variables.
class TrylockVarScanner {
public:
  using ModVarCacheKey = llvm::PointerIntPair<const Stmt *, 1, bool>;
  using ModVarCacheMap =
      llvm::DenseMap<ModVarCacheKey, llvm::ArrayRef<const ValueDecl *>>;

  TrylockVarScanner(const ASTContext &Ctx,
                    llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
                    llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars,
                    ModVarCacheMap *ModCache = nullptr,
                    llvm::BumpPtrAllocator *Bpa = nullptr)
      : Ctx(Ctx), EscapedVars(EscapedVars), ModifiedVars(ModifiedVars),
        ModCache(ModCache), Bpa(Bpa) {}

  llvm::ArrayRef<const ValueDecl *> visit(const Stmt *S, bool InNestedClosure,
                                          bool LValueIsSafe) {
    static constexpr unsigned MaxASTWalkDepth = 512;
    if (!S || Depth >= MaxASTWalkDepth)
      return {};

    // Do not cache DeclRefExpr, ParenExpr, or CK_NoOp CastExpr nodes directly,
    // because recordSafeUse() on an enclosing assignment or increment marks the
    // unwrapped DeclRefExpr in SafeDREs before visiting the LHS with
    // LValueIsSafe=false.
    bool IsDirectLValueWrapper =
        isa<DeclRefExpr, ParenExpr>(S) ||
        (isa<CastExpr>(S) && cast<CastExpr>(S)->getCastKind() == CK_NoOp);
    bool CanCache = ModCache && Bpa && !InNestedClosure &&
                    !IsDirectLValueWrapper && !InConstPointeeArg;
    ModVarCacheKey CacheKey(S, LValueIsSafe);
    if (CanCache) {
      if (auto It = ModCache->find(CacheKey); It != ModCache->end()) {
        for (const ValueDecl *VD : It->second)
          ModifiedVars.insert(VD);
        return It->second;
      }
    }

    SubtreeVarMerger Merger;
    ++Depth;

    // Skip unevaluated operands completely.
    if (visitUnevaluatedOperand(S, InNestedClosure, LValueIsSafe, Merger)) {
      --Depth;
      if (!ModCache || !Bpa)
        return {};
      llvm::ArrayRef<const ValueDecl *> Res = Merger.finalize(*Bpa);
      if (CanCache)
        ModCache->try_emplace(CacheKey, Res);
      return Res;
    }

    if (recordClosureCaptures(S, Merger))
      InNestedClosure = true;

    if (!InNestedClosure)
      recordSafeUse(S, LValueIsSafe, Merger);

    recordDeclRef(S, InNestedClosure, LValueIsSafe, Merger);

    visitChildren(S, InNestedClosure, LValueIsSafe, Merger);
    --Depth;

    if (!ModCache || !Bpa)
      return {};
    llvm::ArrayRef<const ValueDecl *> Res = Merger.finalize(*Bpa);
    if (CanCache)
      ModCache->try_emplace(CacheKey, Res);
    return Res;
  }

private:
  void recordModVar(const ValueDecl *VD, SubtreeVarMerger &Merger) {
    ModifiedVars.insert(VD);
    if (ModCache && Bpa)
      Merger.add(VD);
  }

  /// Record that the variable \p VD escapes and may be modified.
  void recordEscapedVar(const ValueDecl *VD, SubtreeVarMerger &Merger) {
    EscapedVars.insert(VD);
    recordModVar(VD, Merger);
  }

  /// If \p S is an operand that may not be evaluated, visit only its
  /// evaluated parts and return true.
  bool visitUnevaluatedOperand(const Stmt *S, bool InNestedClosure,
                               bool LValueIsSafe, SubtreeVarMerger &Merger) {
    if (const auto *CE = dyn_cast<CallExpr>(S);
        CE && CE->isUnevaluatedBuiltinCall(Ctx))
      return true;
    if (isa<CXXNoexceptExpr>(S))
      return true;
    if (const auto *TE = dyn_cast<UnaryExprOrTypeTraitExpr>(S)) {
      if (isEvaluatedUnaryExprOrTypeTrait(TE))
        for (const Stmt *Child : TE->children())
          Merger.merge(visit(Child, InNestedClosure, /*LValueIsSafe=*/false));
      return true;
    }
    if (const auto *TE = dyn_cast<CXXTypeidExpr>(S)) {
      if (!TE->isTypeOperand() && TE->isPotentiallyEvaluated())
        Merger.merge(visit(TE->getExprOperand(), InNestedClosure,
                           /*LValueIsSafe=*/false));
      return true;
    }
    if (const auto *GSE = dyn_cast<GenericSelectionExpr>(S)) {
      if (!GSE->isResultDependent())
        Merger.merge(
            visit(GSE->getResultExpr(), InNestedClosure, LValueIsSafe));
      return true;
    }
    return false;
  }

  /// If \p S is a closure, record the variables that it captures by
  /// reference and return true.
  bool recordClosureCaptures(const Stmt *S, SubtreeVarMerger &Merger) {
    if (const auto *LE = dyn_cast<LambdaExpr>(S)) {
      for (const LambdaCapture &Cap : LE->captures()) {
        if (Cap.capturesVariable() && Cap.getCaptureKind() == LCK_ByRef) {
          const ValueDecl *VD =
              cast<ValueDecl>(Cap.getCapturedVar()->getCanonicalDecl());
          recordEscapedVar(VD, Merger);
        }
      }
      return true;
    }
    if (const auto *BE = dyn_cast<BlockExpr>(S)) {
      // The body of a block is not a child of the BlockExpr. Variables
      // captured by reference (__block variables) may be modified whenever
      // the block runs.
      for (const BlockDecl::Capture &Cap : BE->getBlockDecl()->captures()) {
        if (Cap.isByRef()) {
          const ValueDecl *VD =
              cast<ValueDecl>(Cap.getVariable()->getCanonicalDecl());
          recordEscapedVar(VD, Merger);
        }
      }
      return true;
    }
    return isa<CapturedStmt>(S);
  }

  /// Record the variable references in \p S that only read or assign the
  /// value of a variable and the variables that \p S modifies.
  void recordSafeUse(const Stmt *S, bool LValueIsSafe,
                     SubtreeVarMerger &Merger) {
    if (const auto *CE = dyn_cast<CastExpr>(S)) {
      if (CE->getCastKind() == CK_LValueToRValue)
        if (const auto *DRE = unwrapDirectLValueDRE(CE->getSubExpr()))
          SafeDREs.insert(DRE);
      return;
    }
    const Expr *ModLV = nullptr;
    if (const auto *BO = dyn_cast<BinaryOperator>(S);
        BO && BO->isAssignmentOp())
      ModLV = BO->getLHS();
    else if (const auto *UO = dyn_cast<UnaryOperator>(S);
             UO && UO->isIncrementDecrementOp())
      ModLV = UO->getSubExpr();
    if (ModLV) {
      SmallVector<const DeclRefExpr *, 2> DREs;
      collectModifiedLValueDREs(ModLV, DREs);
      const bool IsSafe = !cast<Expr>(S)->isGLValue() || LValueIsSafe;
      for (const DeclRefExpr *DRE : DREs) {
        if (IsSafe)
          SafeDREs.insert(DRE);
        if (isa<VarDecl>(DRE->getDecl()))
          recordModVar(cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()),
                       Merger);
      }
    }
  }

  /// If \p S is a reference to a variable other than by reading or assigning
  /// its value, record that the variable escapes.
  void recordDeclRef(const Stmt *S, bool InNestedClosure, bool LValueIsSafe,
                     SubtreeVarMerger &Merger) {
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
      if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        const ValueDecl *CanonVD = cast<ValueDecl>(VD->getCanonicalDecl());
        if (InNestedClosure || (!LValueIsSafe && !SafeDREs.contains(DRE)))
          recordEscapedVar(CanonVD, Merger);
      }
    }
  }

  /// Visit the children of \p S and whether an lvalue child is used safely.
  void visitChildren(const Stmt *S, bool InNestedClosure, bool LValueIsSafe,
                     SubtreeVarMerger &Merger) {
    if (const auto *PE = dyn_cast<ParenExpr>(S)) {
      Merger.merge(visit(PE->getSubExpr(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *FE = dyn_cast<FullExpr>(S)) {
      Merger.merge(visit(FE->getSubExpr(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *CE = dyn_cast<CastExpr>(S)) {
      // The CFG does not contain the size expressions of variable length
      // array types in casts.
      if (const auto *ECE = dyn_cast<ExplicitCastExpr>(CE))
        forEachTypeVLAExpr(ECE->getTypeAsWritten(), [&](const Expr *Sz) {
          Merger.merge(visit(Sz, InNestedClosure, /*LValueIsSafe=*/true));
        });
      bool ChildSafe = false;
      if (CE->getCastKind() == CK_LValueToRValue ||
          CE->getCastKind() == CK_ToVoid)
        ChildSafe = true;
      else if (CE->getCastKind() == CK_NoOp && CE->isGLValue())
        ChildSafe = LValueIsSafe;
      Merger.merge(visit(CE->getSubExpr(), InNestedClosure, ChildSafe));
      return;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(S);
        BO && BO->getOpcode() == BO_Comma) {
      Merger.merge(visit(BO->getLHS(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(visit(BO->getRHS(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *CO = dyn_cast<ConditionalOperator>(S)) {
      Merger.merge(
          visit(CO->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(visit(CO->getTrueExpr(), InNestedClosure, LValueIsSafe));
      Merger.merge(visit(CO->getFalseExpr(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(S)) {
      Merger.merge(visit(BCO->getCommon(), InNestedClosure, LValueIsSafe));
      Merger.merge(visit(BCO->getFalseExpr(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *OVE = dyn_cast<OpaqueValueExpr>(S)) {
      Merger.merge(visit(OVE->getSourceExpr(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(S)) {
      if (const CompoundStmt *CS = SE->getSubStmt()) {
        for (const Stmt *Sub : llvm::drop_end(CS->body()))
          Merger.merge(visit(Sub, InNestedClosure, /*LValueIsSafe=*/true));
        if (!CS->body_empty())
          Merger.merge(
              visit(CS->body_back(), InNestedClosure, /*LValueIsSafe=*/false));
      }
      return;
    }
    if (const auto *CS = dyn_cast<CompoundStmt>(S)) {
      for (const Stmt *Sub : CS->body())
        Merger.merge(visit(Sub, InNestedClosure, /*LValueIsSafe=*/true));
      return;
    }
    if (const auto *LS = dyn_cast<LabelStmt>(S)) {
      Merger.merge(visit(LS->getSubStmt(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *AS = dyn_cast<AttributedStmt>(S)) {
      Merger.merge(visit(AS->getSubStmt(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *DS = dyn_cast<DefaultStmt>(S)) {
      Merger.merge(visit(DS->getSubStmt(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *CS = dyn_cast<CaseStmt>(S)) {
      Merger.merge(
          visit(CS->getLHS(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(
          visit(CS->getRHS(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(visit(CS->getSubStmt(), InNestedClosure, LValueIsSafe));
      return;
    }
    if (const auto *IS = dyn_cast<IfStmt>(S)) {
      Merger.merge(
          visit(IS->getInit(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(visit(IS->getConditionVariableDeclStmt(), InNestedClosure,
                         /*LValueIsSafe=*/false));
      Merger.merge(
          visit(IS->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(
          visit(IS->getThen(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(
          visit(IS->getElse(), InNestedClosure, /*LValueIsSafe=*/true));
      return;
    }
    if (const auto *WS = dyn_cast<WhileStmt>(S)) {
      Merger.merge(visit(WS->getConditionVariableDeclStmt(), InNestedClosure,
                         /*LValueIsSafe=*/false));
      Merger.merge(
          visit(WS->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(
          visit(WS->getBody(), InNestedClosure, /*LValueIsSafe=*/true));
      return;
    }
    if (const auto *DS = dyn_cast<DoStmt>(S)) {
      Merger.merge(
          visit(DS->getBody(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(
          visit(DS->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      return;
    }
    if (const auto *FS = dyn_cast<ForStmt>(S)) {
      Merger.merge(
          visit(FS->getInit(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(visit(FS->getConditionVariableDeclStmt(), InNestedClosure,
                         /*LValueIsSafe=*/false));
      Merger.merge(
          visit(FS->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(visit(FS->getInc(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(
          visit(FS->getBody(), InNestedClosure, /*LValueIsSafe=*/true));
      return;
    }
    if (const auto *SS = dyn_cast<SwitchStmt>(S)) {
      Merger.merge(
          visit(SS->getInit(), InNestedClosure, /*LValueIsSafe=*/true));
      Merger.merge(visit(SS->getConditionVariableDeclStmt(), InNestedClosure,
                         /*LValueIsSafe=*/false));
      Merger.merge(
          visit(SS->getCond(), InNestedClosure, /*LValueIsSafe=*/false));
      Merger.merge(
          visit(SS->getBody(), InNestedClosure, /*LValueIsSafe=*/true));
      return;
    }
    if (const auto *CE = dyn_cast<CallExpr>(S)) {
      Merger.merge(
          visit(CE->getCallee(), InNestedClosure, /*LValueIsSafe=*/false));
      bool CanPropagateConstRef =
          LValueIsSafe || !CE->isGLValue() || CE->getType().isConstQualified();
      // A variable whose address is passed as a pointer to const cannot be
      // modified through it, unless the callee returns the pointer, e.g.
      // strchr().
      const bool ResultCannotAliasArgs = callResultCannotAliasArgs(CE);
      for (unsigned I = 0, N = CE->getNumArgs(); I < N; ++I) {
        llvm::SaveAndRestore InConstPointee(InConstPointeeArg);
        SmallVector<const DeclRefExpr *, 2> ConstPointeeDREs;
        if (ResultCannotAliasArgs &&
            isConstPointeeParamType(getCallArgParamType(CE, I)) &&
            collectAddrOfDREs(CE->getArg(I), ConstPointeeDREs)) {
          SafeDREs.insert_range(ConstPointeeDREs);
          InConstPointeeArg = true;
        }
        bool ArgSafe = CanPropagateConstRef && isSafeCallLValueArg(CE, I);
        Merger.merge(visit(CE->getArg(I), InNestedClosure, ArgSafe));
      }
      return;
    }
    if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
      const CXXConstructorDecl *CD = CCE->getConstructor();
      for (unsigned I = 0, N = CCE->getNumArgs(); I < N; ++I) {
        bool ArgSafe =
            isSafeCallOrCtorLValueArg(CD, /*HasImplicitObjArg=*/false, I);
        Merger.merge(visit(CCE->getArg(I), InNestedClosure, ArgSafe));
      }
      return;
    }

    // Note: DeclStmt::children() includes the variable initializers.
    if (const auto *DS = dyn_cast<DeclStmt>(S)) {
      visitDeclStmt(DS, InNestedClosure, Merger);
      return;
    }
    for (const Stmt *Child : S->children())
      if (Child)
        Merger.merge(visit(Child, InNestedClosure, /*LValueIsSafe=*/false));
  }

  void visitDeclStmt(const DeclStmt *DS, bool InNestedClosure,
                     SubtreeVarMerger &Merger) {
    forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/true, [&](const Expr *Sz) {
      Merger.merge(visit(Sz, InNestedClosure, /*LValueIsSafe=*/true));
    });
    // The lvalue that a const reference is bound to cannot be modified
    // through the reference. The value of the reference changes with the
    // lvalue though, so the reference cannot be tracked as a variable.
    llvm::SmallPtrSet<const Stmt *, 2> ConstRefInits;
    for (const Decl *D : DS->decls()) {
      const auto *VD = dyn_cast<VarDecl>(D);
      if (!VD || !VD->getInit() || !isConstRefType(VD->getType()))
        continue;
      ConstRefInits.insert(VD->getInit());
      if (!isa<MaterializeTemporaryExpr>(stripNoOpExprWrappers(VD->getInit())))
        recordEscapedVar(cast<ValueDecl>(VD->getCanonicalDecl()), Merger);
    }
    for (const Stmt *Child : DS->children())
      if (Child)
        Merger.merge(visit(Child, InNestedClosure,
                           /*LValueIsSafe=*/ConstRefInits.contains(Child)));
  }

  const ASTContext &Ctx;
  llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars;
  llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars;
  ModVarCacheMap *ModCache;
  llvm::BumpPtrAllocator *Bpa;
  llvm::SmallPtrSet<const DeclRefExpr *, 16> SafeDREs;
  // Whether an argument that passes the address of a variable as a pointer
  // to const is visited. Its variable references have been added to SafeDREs
  // in advance, so the results of the visit must not be cached.
  bool InConstPointeeArg = false;
  unsigned Depth = 0;
};
} // namespace

/// Collect the local variables that are referenced in \p Root other than by
/// reading or assigning their value (EscapedVars) and the variables that may
/// be modified (ModifiedVars).
void threadSafety::scanTrylockVars(
    const Stmt *Root, const ASTContext &Ctx,
    llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
    llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars) {
  if (!Root)
    return;

  TrylockVarScanner Scanner(Ctx, EscapedVars, ModifiedVars);
  (void)Scanner.visit(Root, /*InNestedClosure=*/false,
                      /*LValueIsSafe=*/isa<CompoundStmt>(Root));
}

bool threadSafety::isScopedLockable(const TagDecl *TD) {
  return TD->getMostRecentDecl()->hasAttr<ScopedLockableAttr>();
}

bool threadSafety::hasThreadSafetyCallEffects(const NamedDecl *Callee,
                                              const Expr *CallOrCtor) {
  if (CallOrCtor) {
    if (const auto *TagT = CallOrCtor->getType()->getAs<TagType>())
      if (isScopedLockable(TagT->getDecl()))
        return true;
  }
  if (!Callee)
    return false;
  Callee = cast<NamedDecl>(Callee->getMostRecentDecl());
  if (Callee->hasAttr<AcquireCapabilityAttr>() ||
      Callee->hasAttr<ReleaseCapabilityAttr>() ||
      Callee->hasAttr<AssertCapabilityAttr>() || hasTrylockAttr(Callee) ||
      Callee->hasAttr<LocksExcludedAttr>() ||
      Callee->hasAttr<RequiresCapabilityAttr>())
    return true;
  if (const auto *FD = dyn_cast<FunctionDecl>(Callee)) {
    for (const FunctionDecl *Redecl : FD->redecls())
      for (const ParmVarDecl *P : Redecl->parameters())
        if (P->hasAttrs())
          return true;
  }
  return false;
}

static const ReturnStmt *unwrapSingleReturnStmt(const Stmt *S) {
  while (const auto *CS = dyn_cast_or_null<CompoundStmt>(S)) {
    if (CS->size() != 1)
      return nullptr;
    S = CS->body_front();
  }
  const auto *RS = dyn_cast_or_null<ReturnStmt>(S);
  return (RS && RS->getRetValue()) ? RS : nullptr;
}

static unsigned countReturnStmts(const Stmt *S) {
  if (!S || isa<LambdaExpr, BlockExpr, CapturedStmt>(S))
    return 0;
  unsigned Count = isa<ReturnStmt>(S) ? 1 : 0;
  for (const Stmt *Child : S->children())
    if (Child)
      Count += countReturnStmts(Child);
  return Count;
}

static std::unique_ptr<TrivialInlineBody>
getTrivialInlineBody(const FunctionDecl *DefFD, const Stmt *Body) {
  if (const auto *MD = dyn_cast<CXXMethodDecl>(DefFD))
    if (!MD->isStatic())
      return nullptr;
  if ((!DefFD->isInlined() && !DefFD->isConstexpr()) || DefFD->isWeak() ||
      DefFD->isVariadic())
    return nullptr;
  if (const auto *TagT = DefFD->getReturnType()->getAs<TagType>())
    if (isScopedLockable(TagT->getDecl()))
      return nullptr;
  if (hasThreadSafetyCallEffects(DefFD, /*CallOrCtor=*/nullptr) ||
      hasThreadSafetyCallEffects(DefFD->getMostRecentDecl(),
                                 /*CallOrCtor=*/nullptr))
    return nullptr;

  for (const ParmVarDecl *P : DefFD->parameters()) {
    QualType PTy = P->getType();
    if (PTy.isNull() || PTy->isReferenceType() || PTy.isVolatileQualified())
      return nullptr;
  }

  // Reject large inline functions before walking their AST.
  const auto *CS = dyn_cast<CompoundStmt>(Body);
  if (!CS || CS->body_empty() || CS->size() > 2)
    return nullptr;

  bool HasCallEffects = false;
  visitEvaluatedStmts(CS, DefFD->getASTContext(), [&](const Stmt *S) {
    if (HasCallEffects)
      return;
    if (const auto *CE = dyn_cast<CallExpr>(S)) {
      if (hasThreadSafetyCallEffects(
              llvm::dyn_cast_if_present<NamedDecl>(CE->getCalleeDecl()), CE))
        HasCallEffects = true;
    } else if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
      const CXXConstructorDecl *CD = CCE->getConstructor();
      if (hasThreadSafetyCallEffects(CD, CCE))
        HasCallEffects = true;
      else if (const CXXDestructorDecl *DD =
                   CD ? CD->getParent()->getDestructor() : nullptr;
               DD && hasThreadSafetyCallEffects(DD, /*CallOrCtor=*/nullptr))
        HasCallEffects = true;
    }
  });
  if (HasCallEffects)
    return nullptr;

  auto Info = std::make_unique<TrivialInlineBody>();
  Info->DefFD = DefFD;
  llvm::SmallPtrSet<const ValueDecl *, 8> CalleeModified;
  scanTrylockVars(CS, DefFD->getASTContext(), Info->CalleeEscaped,
                  CalleeModified);
  for (const ParmVarDecl *P : DefFD->parameters()) {
    const auto *PVD = cast<ValueDecl>(P->getCanonicalDecl());
    if (Info->CalleeEscaped.contains(PVD) || CalleeModified.contains(PVD))
      return nullptr;
  }

  unsigned NumRets = countReturnStmts(CS);
  if (NumRets == 1 && (CS->size() == 1 || !isa<DeclStmt>(CS->body_front()))) {
    if (const auto *RS = dyn_cast<ReturnStmt>(CS->body_back());
        RS && RS->getRetValue()) {
      Info->SingleRet = RS->getRetValue();
      return Info;
    }
    return nullptr;
  }

  if (NumRets == 2) {
    if (CS->size() == 1) {
      if (const auto *IS = dyn_cast<IfStmt>(CS->body_front());
          IS && !IS->getInit() && !IS->getConditionVariable() &&
          IS->getCond() && IS->getElse()) {
        const ReturnStmt *ThenRS = unwrapSingleReturnStmt(IS->getThen());
        const ReturnStmt *ElseRS = unwrapSingleReturnStmt(IS->getElse());
        if (ThenRS && ElseRS) {
          Info->CondExpr = IS->getCond();
          Info->ThenRet = ThenRS->getRetValue();
          Info->ElseRet = ElseRS->getRetValue();
          return Info;
        }
      }
    } else if (CS->size() == 2) {
      const auto *IS = dyn_cast<IfStmt>(CS->body_front());
      const auto *ElseRS = dyn_cast<ReturnStmt>(CS->body_back());
      if (IS && !IS->getInit() && !IS->getConditionVariable() &&
          IS->getCond() && !IS->getElse() && ElseRS && ElseRS->getRetValue()) {
        if (const ReturnStmt *ThenRS = unwrapSingleReturnStmt(IS->getThen())) {
          Info->CondExpr = IS->getCond();
          Info->ThenRet = ThenRS->getRetValue();
          Info->ElseRet = ElseRS->getRetValue();
          return Info;
        }
      }
    }
  }

  return nullptr;
}

/// The ranges of the arguments of \p CallExp, or std::nullopt for arguments
/// whose range is unknown or covers the whole domain.
SmallVector<std::optional<ThreadSafetyAnalyzer::IntRangeSet>, 4>
ThreadSafetyAnalyzer::evaluateInlineArgRanges(const CallExpr *CallExp,
                                              const TrylockValueState &State,
                                              const RangeEvalCtx &EC,
                                              unsigned Depth) {
  SmallVector<std::optional<IntRangeSet>, 4> ArgRanges;
  for (const Expr *Arg : CallExp->arguments()) {
    std::optional<IntRangeSet> ArgR;
    if (auto ArgDom = getScalarDomain(Arg->getType())) {
      ArgR = evaluatePureExprRange(Arg, State, EC, Depth);
      if (ArgR && IntRangeSet::full(*ArgDom).subsetOfSet(*ArgR))
        ArgR.reset();
    }
    ArgRanges.push_back(std::move(ArgR));
  }
  return ArgRanges;
}

/// Profiles a key that identifies an inline expansion of \p DefFD for
/// arguments with the ranges \p ArgRanges into \p ID. \p Kind distinguishes
/// the kinds of results that are cached. Returns false if the result must not
/// be cached: only results computed outside other expansions are cached
/// because the results of nested expansions depend on the remaining
/// recursion depth.
bool ThreadSafetyAnalyzer::profileInlineCallCacheKey(
    llvm::FoldingSetNodeID &ID, const FunctionDecl *DefFD, unsigned Kind,
    ArrayRef<std::optional<IntRangeSet>> ArgRanges) const {
  if (!DefFD || InlineDepth != 0)
    return false;
  ID.AddPointer(DefFD);
  ID.AddInteger(Kind);
  ID.AddInteger(ArgRanges.size());
  for (const auto &R : ArgRanges) {
    if (!R) {
      ID.AddBoolean(false);
      continue;
    }
    ID.AddBoolean(true);
    ID.AddInteger(R->ranges().size());
    for (const auto &[Lo, Hi] : R->ranges()) {
      Lo.Profile(ID);
      Hi.Profile(ID);
    }
  }
  return true;
}

/// The value state in which the parameters of \p Info have the ranges
/// \p ArgRanges.
ThreadSafetyAnalyzer::TrylockValueState ThreadSafetyAnalyzer::makeCalleeState(
    const TrivialInlineBody &Info,
    ArrayRef<std::optional<IntRangeSet>> ArgRanges) const {
  TrylockValueState CalleeState;
  for (auto [I, ArgR] : llvm::enumerate(ArgRanges))
    if (auto PDom = getScalarDomain(Info.param(I)->getType()); PDom && ArgR)
      CalleeState.VarRanges[Info.param(I)] = reprojectRangeSet(*ArgR, *PDom);
  return CalleeState;
}

const TrivialInlineBody *
ThreadSafetyAnalyzer::lookupTrivialInlineBody(const CallExpr *CallExp) const {
  const FunctionDecl *FD = CallExp ? CallExp->getDirectCallee() : nullptr;
  if (!FD || CallExp->isTypeDependent() || CallExp->isValueDependent())
    return nullptr;
  const FunctionDecl *DefFD = nullptr;
  const Stmt *Body = FD->getBody(DefFD);
  if (!Body || !DefFD || DefFD->isVariadic() ||
      CallExp->getNumArgs() != DefFD->getNumParams() ||
      hasThreadSafetyCallEffects(FD, CallExp))
    return nullptr;
  if (auto It = GlobalCache->InlineBodyCache.find(DefFD);
      It != GlobalCache->InlineBodyCache.end())
    return It->second.get();
  auto BodyInfo = getTrivialInlineBody(DefFD, Body);
  const TrivialInlineBody *Res = BodyInfo.get();
  GlobalCache->InlineBodyCache.try_emplace(DefFD, std::move(BodyInfo));
  return Res;
}

const TrivialInlineBody *ThreadSafetyAnalyzer::getCachedTrivialInlineBody(
    const CallExpr *CallExp) const {
  if (InlineExpansionCount >= MaxInlineExpansions) {
    InlineEvalHitCutoff = true;
    return nullptr;
  }
  const TrivialInlineBody *Info = lookupTrivialInlineBody(CallExp);
  // Do not expand recursive calls.
  if (Info && ActiveInlineCallees.contains(Info->DefFD))
    return nullptr;
  return Info;
}

/// If the statement expression \p SE consists of local variable declarations
/// without side effects followed by a final expression without side effects,
/// returns the pure expression that determines its value.
const Expr *threadSafety::extractPureStmtExpr(const StmtExpr *SE,
                                              const ASTContext &Ctx) {
  const CompoundStmt *CS = SE ? SE->getSubStmt() : nullptr;
  if (!CS || CS->body_empty())
    return nullptr;
  const auto *LastExpr = dyn_cast<Expr>(CS->body_back());
  if (!LastExpr)
    return nullptr;
  llvm::SmallPtrSet<const ValueDecl *, 4> LocalDecls, Escaped, Mod;
  llvm::DenseMap<const ValueDecl *, const Expr *> LocalInits;
  for (const Stmt *S : llvm::drop_end(CS->body())) {
    if (const auto *DS = dyn_cast<DeclStmt>(S)) {
      for (const Decl *D : DS->decls()) {
        const auto *VD = dyn_cast<VarDecl>(D);
        if (!VD || !VD->hasLocalStorage() ||
            VD->getType()->isVariablyModifiedType())
          return nullptr;
        const auto *Canon = cast<ValueDecl>(VD->getCanonicalDecl());
        LocalDecls.insert(Canon);
        LocalInits[Canon] = VD->getInit();
      }
    } else if (!isa<Expr, NullStmt>(S)) {
      return nullptr;
    }
  }
  scanTrylockVars(CS, Ctx, Escaped, Mod);
  if (!Mod.empty())
    return nullptr;
  const Expr *Unwrapped = stripNoOpExprWrappers(LastExpr);
  if (const auto *L2R = dyn_cast<CastExpr>(Unwrapped);
      L2R && L2R->getCastKind() == CK_LValueToRValue)
    Unwrapped = stripNoOpExprWrappers(L2R->getSubExpr());
  if (const auto *DRE = dyn_cast<DeclRefExpr>(Unwrapped)) {
    const auto *VD = cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (auto It = LocalInits.find(VD);
        It != LocalInits.end() && !Escaped.contains(VD))
      return It->second && !exprReferencesAnyVar(It->second, LocalDecls)
                 ? It->second
                 : nullptr;
  }
  return LocalDecls.empty() ? LastExpr : nullptr;
}

const Expr *
ThreadSafetyAnalyzer::getCachedPureStmtExpr(const StmtExpr *SE) const {
  if (!SE)
    return nullptr;
  if (!GlobalCache)
    return extractPureStmtExpr(SE, *ASTCtx);
  if (auto It = GlobalCache->PureStmtExprCache.find(SE);
      It != GlobalCache->PureStmtExprCache.end())
    return It->second;
  const Expr *Res = extractPureStmtExpr(SE, *ASTCtx);
  GlobalCache->PureStmtExprCache.try_emplace(SE, Res);
  return Res;
}

bool ThreadSafetyAnalyzer::isTrackableLocalVar(
    const ValueDecl *VD,
    const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const {
  const auto *Var = dyn_cast_or_null<VarDecl>(VD);
  if (!Var || !Var->hasLocalStorage())
    return false;
  QualType Ty = Var->getType();
  if (Ty.isNull() || Ty->isReferenceType() || Ty.isVolatileQualified() ||
      Var->hasAttr<BlocksAttr>())
    return false;
  if (EscapedVars.contains(cast<ValueDecl>(Var->getCanonicalDecl())))
    return false;
  return getScalarDomain(Ty).has_value();
}

const ValueDecl *ThreadSafetyAnalyzer::extractTrackableVarExpr(
    const Expr *E,
    const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const {
  while (E) {
    E = stripNoOpExprWrappers(E);
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (isValuePreservingCast(CE, *ASTCtx)) {
        E = CE->getSubExpr();
        continue;
      }
      return nullptr;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      if (isBuiltinExpectCall(CallExp)) {
        E = CallExp->getArg(0);
        continue;
      }
      return nullptr;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
      if (BO->getOpcode() == BO_Assign) {
        E = BO->getLHS();
        continue;
      }
      return nullptr;
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      return isTrackableLocalVar(VD, EscapedVars) ? VD : nullptr;
    }
    return nullptr;
  }
  return nullptr;
}

/// Range of addresses that a valid object or function can have, i.e. all
/// non-null addresses.
ThreadSafetyAnalyzer::IntRangeSet threadSafety::validObjectPtrRangeSet(
    const ThreadSafetyAnalyzer::IntDomain &Dom) {
  return ThreadSafetyAnalyzer::IntRangeSet::truthSet(Dom, true);
}

/// Whether the address of lvalue \p E is guaranteed to be a valid non-null
/// object or function address (excluding weak symbols and arbitrary pointer
/// dereferences).
static bool isKnownValidObjectOrFunctionLValue(const Expr *E) {
  while (E) {
    E = stripNoOpExprWrappers(E);
    if (isa<StringLiteral, CompoundLiteralExpr, PredefinedExpr, ObjCEncodeExpr>(
            E))
      return true;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      const ValueDecl *D = DRE->getDecl();
      if (D->isWeak())
        return false;
      if (const auto *VD = dyn_cast<VarDecl>(D))
        return !VD->getType()->isReferenceType();
      if (isa<FieldDecl, IndirectFieldDecl>(D))
        return !D->getType()->isReferenceType();
      return isa<FunctionDecl>(D);
    }
    if (const auto *ME = dyn_cast<MemberExpr>(E)) {
      const ValueDecl *MD = ME->getMemberDecl();
      if (const auto *VD = dyn_cast<VarDecl>(MD))
        return !VD->isWeak() && !VD->getType()->isReferenceType();
      if (const auto *FD = dyn_cast<FunctionDecl>(MD))
        return !FD->isWeak();
      if (!isa<FieldDecl, IndirectFieldDecl>(MD))
        return false;
      // The address of a reference member is the address of the object that
      // it is bound to and not an address inside the base object.
      if (MD->getType()->isReferenceType())
        return false;
      if (ME->isArrow())
        return isa_and_nonnull<CXXThisExpr>(
            stripNoOpExprWrappers(ME->getBase()));
      E = ME->getBase();
      continue;
    }
    return false;
  }
  return false;
}

bool threadSafety::exprReferencesAnyVar(
    const Stmt *Root, const llvm::SmallPtrSetImpl<const ValueDecl *> &Vars) {
  if (!Root || Vars.empty())
    return false;
  SmallVector<const Stmt *, 16> Worklist = {Root};
  while (!Worklist.empty()) {
    const Stmt *S = Worklist.pop_back_val();
    if (!S)
      continue;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S))
      if (Vars.contains(cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl())))
        return true;
    for (const Stmt *Child : S->children())
      if (Child)
        Worklist.push_back(Child);
  }
  return false;
}

llvm::ArrayRef<const ValueDecl *>
ThreadSafetyAnalyzer::getSubtreeModifiedVars(const Stmt *S) {
  if (!S)
    return {};
  llvm::PointerIntPair<const Stmt *, 1, bool> CacheKey(S, true);
  if (auto It = SubtreeModifiedVarsCache.find(CacheKey);
      It != SubtreeModifiedVarsCache.end())
    return It->second;
  llvm::SmallPtrSet<const ValueDecl *, 4> UnusedEscaped, UnusedModified;
  TrylockVarScanner Scanner(*ASTCtx, UnusedEscaped, UnusedModified,
                            &SubtreeModifiedVarsCache, &Bpa);
  llvm::ArrayRef<const ValueDecl *> Res =
      Scanner.visit(S, /*InNestedClosure=*/false,
                    /*LValueIsSafe=*/true);
  SubtreeModifiedVarsCache.try_emplace(CacheKey, Res);
  return Res;
}

llvm::ArrayRef<const ValueDecl *>
ThreadSafetyAnalyzer::getSubtreeReferencedVars(const Stmt *Root) {
  if (!Root)
    return {};
  if (auto It = SubtreeReferencedVarsCache.find(Root);
      It != SubtreeReferencedVarsCache.end())
    return It->second;
  SmallVector<std::pair<const Stmt *, bool>, 32> Worklist;
  Worklist.emplace_back(Root, false);
  while (!Worklist.empty()) {
    auto [S, Expanded] = Worklist.pop_back_val();
    if (!S || SubtreeReferencedVarsCache.contains(S))
      continue;
    if (!Expanded) {
      Worklist.emplace_back(S, true);
      for (const Stmt *Child : S->children())
        if (Child && !SubtreeReferencedVarsCache.contains(Child))
          Worklist.emplace_back(Child, false);
      continue;
    }
    SubtreeVarMerger Merger;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S))
      if (isa<VarDecl>(DRE->getDecl()))
        Merger.add(cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
    for (const Stmt *Child : S->children())
      if (Child)
        if (auto It = SubtreeReferencedVarsCache.find(Child);
            It != SubtreeReferencedVarsCache.end())
          Merger.merge(It->second);
    llvm::ArrayRef<const ValueDecl *> Res = Merger.finalize(Bpa);
    SubtreeReferencedVarsCache.try_emplace(S, Res);
  }
  return SubtreeReferencedVarsCache.lookup(Root);
}

bool ThreadSafetyAnalyzer::exprReferencesAnyVar(
    const Stmt *S, llvm::ArrayRef<const ValueDecl *> Vars) {
  if (!S || Vars.empty())
    return false;
  llvm::ArrayRef<const ValueDecl *> RefVars = getSubtreeReferencedVars(S);
  if (RefVars.empty())
    return false;
  if (Vars.size() <= 4) {
    for (const ValueDecl *RefVD : RefVars)
      if (llvm::is_contained(Vars, RefVD))
        return true;
    return false;
  }
  llvm::SmallPtrSet<const ValueDecl *, 8> VarSet(Vars.begin(), Vars.end());
  for (const ValueDecl *RefVD : RefVars)
    if (VarSet.contains(RefVD))
      return true;
  return false;
}

void threadSafety::eraseModifiedVarsFromState(
    ThreadSafetyAnalyzer::TrylockValueState &State,
    llvm::ArrayRef<const ValueDecl *> ModVars,
    const llvm::SmallPtrSetImpl<const Expr *> *PinnedExprs) {
  for (const ValueDecl *VD : ModVars)
    State.VarRanges.erase(VD);
  // The recorded value of a call is the value that the call returned, which
  // modifying a variable afterwards does not change. Keep these such that the
  // outcome of a trylock call is not forgotten, e.g. in the condition of
  // 'trylock(&s.a) ? trylock(&s.b) : 0', whose arms modify 's'. The same
  // holds for the pinned expressions, e.g. the condition 's.flag' that
  // ReturnValueForker has split 's.flag && trylock(&s.b)' on, and for
  // statement expressions that do not refer to a modified variable, e.g.
  // '({ int v = 1; v; })'.
  auto RefersToModVar = [&](const Stmt *Root) {
    SmallVector<const Stmt *, 8> Worklist = {Root};
    while (!Worklist.empty()) {
      const Stmt *S = Worklist.pop_back_val();
      if (!S)
        continue;
      if (const auto *DRE = dyn_cast<DeclRefExpr>(S))
        if (llvm::is_contained(
                ModVars, cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl())))
          return true;
      llvm::append_range(Worklist, S->children());
    }
    return false;
  };
  SmallVector<const Expr *, 8> Stale;
  for (const auto &[E, Values] : State.ExprRanges)
    if (!isa<CallExpr>(E) && !(PinnedExprs && PinnedExprs->contains(E)) &&
        (!isa<StmtExpr>(E) || RefersToModVar(E)))
      Stale.push_back(E);
  for (const Expr *E : Stale)
    State.ExprRanges.erase(E);
}

static const Expr *getStmtExprLocalValue(const StmtExpr *SE,
                                         const ASTContext &Ctx) {
  const CompoundStmt *CS = SE->getSubStmt();
  const auto *Last =
      CS && !CS->body_empty() ? dyn_cast<Expr>(CS->body_back()) : nullptr;
  if (!Last || Last->HasSideEffects(Ctx))
    return nullptr;
  llvm::SmallPtrSet<const Decl *, 4> LocalDecls;
  for (const Stmt *S : CS->body())
    if (const auto *DS = dyn_cast<DeclStmt>(S))
      for (const Decl *D : DS->decls())
        LocalDecls.insert(D->getCanonicalDecl());
  if (LocalDecls.empty())
    return nullptr;
  for (SmallVector<const Stmt *, 8> W = {Last}; !W.empty();) {
    const Stmt *S = W.pop_back_val();
    if (!S)
      continue;
    if (isa<StmtExpr, LambdaExpr, BlockExpr>(S))
      return nullptr;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S);
        DRE && isa<VarDecl>(DRE->getDecl()) &&
        !LocalDecls.contains(DRE->getDecl()->getCanonicalDecl()))
      return nullptr;
    llvm::append_range(W, S->children());
  }
  return Last;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureExprRange(const Expr *E,
                                            const TrylockValueState &State,
                                            const RangeEvalCtx &EC,
                                            unsigned Depth) {
  if (Depth == 0 && InlineDepth == 0)
    EvalStepCount = 0;
  if (!E || ++EvalStepCount > MaxEvalSteps || Depth > MaxConstrainExprDepth ||
      E->isTypeDependent() || E->isValueDependent()) {
    if (E && (EvalStepCount > MaxEvalSteps || Depth > MaxConstrainExprDepth))
      InlineEvalHitCutoff = true;
    return std::nullopt;
  }

  E = stripNoOpExprWrappers(E);
  auto DomOpt = getScalarDomain(E->getType());
  if (!DomOpt)
    return std::nullopt;
  const IntDomain &Dom = *DomOpt;

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->isLogicalOp()) {
      if (auto It = State.ShortCircuitedOps.find(BO);
          It != State.ShortCircuitedOps.end())
        return IntRangeSet::single(Dom, llvm::APSInt::get(It->second ? 1 : 0));
    }
  }

  if (auto It = State.ExprRanges.find(E); It != State.ExprRanges.end())
    return reprojectRangeSet(It->second, Dom);

  if (isa<CXXNullPtrLiteralExpr, GNUNullExpr>(E))
    return IntRangeSet::single(Dom, llvm::APSInt::get(0));
  if (isa<CXXThisExpr>(E))
    return validObjectPtrRangeSet(Dom);

  if (const auto *DRE = dyn_cast<DeclRefExpr>(E))
    return evaluatePureDeclRefRange(DRE, Dom, State, EC);

  if (const auto *CE = dyn_cast<CastExpr>(E))
    return evaluatePureCastRange(CE, Dom, State, EC, Depth);

  if (const auto *CallExp = dyn_cast<CallExpr>(E))
    return evaluatePureCallRange(CallExp, Dom, State, EC, Depth);

  if (const auto *UO = dyn_cast<UnaryOperator>(E))
    return evaluatePureUnaryRange(UO, Dom, State, EC, Depth);

  if (const auto *BO = dyn_cast<BinaryOperator>(E))
    return evaluatePureBinaryRange(BO, Dom, State, EC, Depth);

  if (const auto *COP = dyn_cast<AbstractConditionalOperator>(E))
    return evaluatePureConditionalRange(COP, Dom, State, EC, Depth);

  if (const auto *SE = dyn_cast<StmtExpr>(E)) {
    if (const Expr *Inner = getCachedPureStmtExpr(SE))
      if (auto R = evaluatePureExprRange(Inner, State, EC, Depth + 1))
        return reprojectRangeSet(*R, Dom);
    // The statements before the last one have already been executed when the
    // value of a statement expression is used. If the last expression only
    // refers to variables that are declared by the statement expression,
    // which cannot be modified after it, its value is the value of the last
    // expression in State, e.g. for '({ bool r = trylock(&mu); r; })'.
    if (const Expr *Last = getStmtExprLocalValue(SE, *ASTCtx))
      if (auto R = evaluatePureExprRange(Last, State, EC, Depth + 1))
        return reprojectRangeSet(*R, Dom);
    if (EC.EscapedVars)
      return std::nullopt;
  }

  // Leave other expressions to the constant evaluator. Only invoke it on leaf
  // or unmodeled nodes; calling it at every interior operator of a deep
  // expression tree would re-traverse the subtree at each level.
  if (E->getType()->isIntegralOrEnumerationType())
    if (auto ICE = evaluateRuntimeIntConstant(E, *ASTCtx))
      return IntRangeSet::single(Dom, *ICE);

  return std::nullopt;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureDeclRefRange(const DeclRefExpr *DRE,
                                               const IntDomain &Dom,
                                               const TrylockValueState &State,
                                               const RangeEvalCtx &EC) {
  const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
  if (!VD)
    return std::nullopt;
  if (DRE->getType()->isIntegralOrEnumerationType()) {
    bool TryConstEval = isa<EnumConstantDecl>(VD);
    if (const auto *VarD = dyn_cast<VarDecl>(VD))
      TryConstEval =
          VarD->isUsableInConstantExpressions(*ASTCtx) ||
          (VarD->getType().isConstQualified() && !State.VarRanges.contains(VD));
    if (TryConstEval)
      if (auto ICE = evaluateRuntimeIntConstant(DRE, *ASTCtx))
        return IntRangeSet::single(Dom, *ICE);
  }
  if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
    return reprojectRangeSet(It->second, Dom);
  return std::nullopt;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureCastRange(const CastExpr *CE,
                                            const IntDomain &Dom,
                                            const TrylockValueState &State,
                                            const RangeEvalCtx &EC,
                                            unsigned Depth) {
  switch (CE->getCastKind()) {
  case CK_NullToPointer:
  case CK_NullToMemberPointer:
    return IntRangeSet::single(Dom, llvm::APSInt::get(0));
  case CK_ArrayToPointerDecay:
  case CK_FunctionToPointerDecay: {
    // Like &*p, *p decays to the value of p.
    const Expr *Sub = stripNoOpExprWrappers(CE->getSubExpr());
    if (const auto *Deref = dyn_cast<UnaryOperator>(Sub);
        Deref && Deref->getOpcode() == UO_Deref) {
      auto SubR =
          evaluatePureExprRange(Deref->getSubExpr(), State, EC, Depth + 1);
      return SubR ? std::optional(reprojectRangeSet(*SubR, Dom)) : std::nullopt;
    }
    if (isKnownValidObjectOrFunctionLValue(Sub))
      return validObjectPtrRangeSet(Dom);
    return std::nullopt;
  }
  default:
    break;
  }
  if (!isRangeMappableCast(CE)) {
    if (CE->getType()->isIntegralOrEnumerationType())
      if (auto ICE = evaluateRuntimeIntConstant(CE, *ASTCtx))
        return IntRangeSet::single(Dom, *ICE);
    return std::nullopt;
  }
  auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, EC, Depth + 1);
  return Sub ? std::optional(applyCast(CE, *Sub, Dom, *ASTCtx)) : std::nullopt;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureCallRange(const CallExpr *CallExp,
                                            const IntDomain &Dom,
                                            const TrylockValueState &State,
                                            const RangeEvalCtx &EC,
                                            unsigned Depth) {
  if (isBuiltinExpectCall(CallExp)) {
    auto Sub = evaluatePureExprRange(CallExp->getArg(0), State, EC, Depth + 1);
    if (!Sub)
      return std::nullopt;
    return castIntegralRangeSet(*Sub, CallExp->getType(), *ASTCtx);
  }
  auto TryConstCall = [&]() -> std::optional<IntRangeSet> {
    if (CallExp->getType()->isIntegralOrEnumerationType()) {
      const FunctionDecl *FD = CallExp->getDirectCallee();
      if (CallExp->getBuiltinCallee() != 0 || (FD && FD->isConstexpr()))
        if (auto ICE = evaluateRuntimeIntConstant(CallExp, *ASTCtx))
          return IntRangeSet::single(Dom, *ICE);
    }
    return std::nullopt;
  };
  // Check whether the callee is a trivial inline helper before evaluating
  // arguments or profiling cache keys, so unrelated calls cost O(1).
  const TrivialInlineBody *InlineInfo = lookupTrivialInlineBody(CallExp);
  if (!InlineInfo || ActiveInlineCallees.contains(InlineInfo->DefFD))
    return TryConstCall();

  SmallVector<std::optional<IntRangeSet>, 4> ArgRanges =
      evaluateInlineArgRanges(CallExp, State, EC, Depth + 1);
  llvm::FoldingSetNodeID CacheID;
  bool CanCache =
      profileInlineCallCacheKey(CacheID, InlineInfo->DefFD, 0, ArgRanges);
  if (CanCache)
    if (auto It = InlineCallRangeCache.find_as(CacheID);
        It != InlineCallRangeCache.end())
      return It->second ? std::optional(reprojectRangeSet(*It->second, Dom))
                        : std::nullopt;

  if (InlineExpansionCount >= MaxInlineExpansions) {
    InlineEvalHitCutoff = true;
    return TryConstCall();
  }

  // The union of the values of the return values, or std::nullopt if the
  // value of one of them is unknown.
  bool PrevHitCutoff = InlineEvalHitCutoff;
  InlineEvalHitCutoff = false;
  std::optional<IntRangeSet> Res = IntRangeSet();
  {
    InlineExpansionScope Scope(*this, *InlineInfo);
    RangeEvalCtx CalleeEC = EC.withEscaped(&InlineInfo->CalleeEscaped);
    forEachInlineReturn(
        *InlineInfo, makeCalleeState(*InlineInfo, ArgRanges), EC, Depth + 1,
        [&](const Expr *RetE, const TrylockValueState &S) {
          if (!Res)
            return;
          if (auto R = evaluatePureExprRange(RetE, S, CalleeEC, Depth + 1))
            Res = Res->unionWith(reprojectRangeSet(*R, Dom));
          else
            Res.reset();
        });
  }
  bool HitCutoff = InlineEvalHitCutoff;
  InlineEvalHitCutoff = PrevHitCutoff || HitCutoff;
  if (!Res)
    Res = TryConstCall();
  if (CanCache && !HitCutoff)
    InlineCallRangeCache.try_emplace(CacheID.Intern(Bpa), Res);
  return Res;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureUnaryRange(const UnaryOperator *UO,
                                             const IntDomain &Dom,
                                             const TrylockValueState &State,
                                             const RangeEvalCtx &EC,
                                             unsigned Depth) {
  switch (UO->getOpcode()) {
  case UO_AddrOf: {
    const Expr *Sub = stripNoOpExprWrappers(UO->getSubExpr());
    if (const auto *Deref = dyn_cast_or_null<UnaryOperator>(Sub);
        Deref && Deref->getOpcode() == UO_Deref) {
      auto SubR =
          evaluatePureExprRange(Deref->getSubExpr(), State, EC, Depth + 1);
      return SubR ? std::optional(reprojectRangeSet(*SubR, Dom)) : std::nullopt;
    }
    if (isKnownValidObjectOrFunctionLValue(Sub))
      return validObjectPtrRangeSet(Dom);
    return std::nullopt;
  }
  case UO_Plus:
    return evaluatePureExprRange(UO->getSubExpr(), State, EC, Depth + 1);
  case UO_Minus: {
    if (!UO->getType()->isIntegralOrEnumerationType())
      return std::nullopt;
    auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, EC, Depth + 1);
    if (!Sub)
      return std::nullopt;
    return negateRangeSet(*Sub, UO->getType(), *ASTCtx);
  }
  case UO_Not: {
    if (!UO->getType()->isIntegralOrEnumerationType())
      return std::nullopt;
    auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, EC, Depth + 1);
    llvm::APSInt V;
    if (!Sub || !Sub->isSingleValue(V))
      return std::nullopt;
    return IntRangeSet::single(Dom, truncToType(~V, UO->getType(), *ASTCtx));
  }
  case UO_LNot: {
    auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, EC, Depth + 1);
    if (!Sub)
      return std::nullopt;
    return IntRangeSet::boolSet(Dom, Sub->mayBeNonZero(), Sub->mayBeZero());
  }
  default:
    return std::nullopt;
  }
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureBinaryRange(const BinaryOperator *BO,
                                              const IntDomain &Dom,
                                              const TrylockValueState &State,
                                              const RangeEvalCtx &EC,
                                              unsigned Depth) {
  if (BO->getOpcode() == BO_Comma) {
    if (EC.EscapedVars) {
      llvm::ArrayRef<const ValueDecl *> LHSMod =
          getSubtreeModifiedVars(BO->getLHS());
      if (exprReferencesAnyVar(BO->getRHS(), LHSMod)) {
        TrylockValueState RHSState = State;
        eraseModifiedVarsFromState(RHSState, LHSMod, EC.PinnedExprs);
        return evaluatePureExprRange(BO->getRHS(), RHSState, EC, Depth + 1);
      }
    }
    return evaluatePureExprRange(BO->getRHS(), State, EC, Depth + 1);
  }
  if (BO->getOpcode() == BO_Assign) {
    auto Sub = evaluatePureExprRange(BO->getRHS(), State, EC, Depth + 1);
    if (!Sub)
      return std::nullopt;
    if (const FieldDecl *BF = BO->getLHS()->getSourceBitField()) {
      if (!BF->hasConstantIntegerBitWidth())
        return std::nullopt;
      unsigned BW = BF->getBitWidthValue();
      return truncateToBitField(*Sub, BW, BO->getType(), Dom, *ASTCtx);
    }
    if (BO->getLHS()->refersToBitField())
      return std::nullopt;
    return reprojectRangeSet(*Sub, Dom);
  }

  if (BO->isLogicalOp()) {
    if (auto It = State.ShortCircuitedOps.find(BO);
        It != State.ShortCircuitedOps.end())
      return IntRangeSet::single(Dom, llvm::APSInt::get(It->second ? 1 : 0));
    // Whether the value of Op may be false and whether it may be true.
    auto EvalBool = [&](const Expr *Op,
                        const TrylockValueState &S) -> std::pair<bool, bool> {
      auto OpR = evaluatePureExprRange(Op, S, EC, Depth + 1);
      if (!OpR)
        return {true, true};
      return {OpR->mayBeZero(), OpR->mayBeNonZero()};
    };
    bool IsAnd = BO->getOpcode() == BO_LAnd;
    llvm::ArrayRef<const ValueDecl *> LHSMod =
        EC.EscapedVars ? getSubtreeModifiedVars(BO->getLHS())
                       : llvm::ArrayRef<const ValueDecl *>{};
    llvm::ArrayRef<const ValueDecl *> RHSMod =
        EC.EscapedVars ? getSubtreeModifiedVars(BO->getRHS())
                       : llvm::ArrayRef<const ValueDecl *>{};
    const bool LHSRefsRHSMod = exprReferencesAnyVar(BO->getLHS(), RHSMod);
    const bool RHSRefsLHSMod = exprReferencesAnyVar(BO->getRHS(), LHSMod);
    std::pair<bool, bool> LHSBool{true, true};
    if (LHSRefsRHSMod) {
      TrylockValueState LHSState = State;
      eraseModifiedVarsFromState(LHSState, RHSMod, EC.PinnedExprs);
      LHSBool = EvalBool(BO->getLHS(), LHSState);
    } else {
      LHSBool = EvalBool(BO->getLHS(), State);
    }
    auto [L0, L1] = LHSBool;
    if (IsAnd ? !L1 : !L0)
      return IntRangeSet::single(Dom, llvm::APSInt::get(IsAnd ? 0 : 1));
    std::pair<bool, bool> RHSBool{true, true};
    if (RHSRefsLHSMod || (Depth < 8 && EC.EscapedVars && !LHSRefsRHSMod)) {
      TrylockValueState RHSState = State;
      if (RHSRefsLHSMod)
        eraseModifiedVarsFromState(RHSState, LHSMod, EC.PinnedExprs);
      if (Depth < 8 && EC.EscapedVars && !LHSRefsRHSMod) {
        constrainLeafCondition(RHSState, BO->getLHS(), /*WantTrue=*/IsAnd, EC,
                               Depth + 1);
      }
      RHSBool = RHSState.Infeasible ? std::make_pair(false, false)
                                    : EvalBool(BO->getRHS(), RHSState);
    } else {
      RHSBool = EvalBool(BO->getRHS(), State);
    }
    auto [R0, R1] = RHSBool;
    return IntRangeSet::boolSet(Dom, IsAnd ? (L0 || R0) : (L0 && R0),
                                IsAnd ? (L1 && R1) : (L1 || R1));
  }

  if (EC.EscapedVars &&
      (exprReferencesModifiedVars(BO->getLHS(), BO->getRHS()) ||
       exprReferencesModifiedVars(BO->getRHS(), BO->getLHS())))
    return std::nullopt;

  if (BO->isRelationalOp() || BO->isEqualityOp()) {
    auto L = evaluatePureExprRange(BO->getLHS(), State, EC, Depth + 1);
    auto R = evaluatePureExprRange(BO->getRHS(), State, EC, Depth + 1);
    if (!L || !R)
      return std::nullopt;
    bool IsMemberPtrCmp = BO->getLHS()->getType()->isMemberPointerType();
    return compareRangeSets(BO->getOpcode(), *L, *R, Dom, IsMemberPtrCmp);
  }

  if (BO->getOpcode() == BO_Sub && BO->getLHS()->getType()->isPointerType() &&
      BO->getRHS()->getType()->isPointerType()) {
    auto L = evaluatePureExprRange(BO->getLHS(), State, EC, Depth + 1);
    auto R = evaluatePureExprRange(BO->getRHS(), State, EC, Depth + 1);
    llvm::APSInt LV, RV;
    if (L && R && L->isSingleValue(LV) && R->isSingleValue(RV)) {
      QualType PointeeTy = BO->getLHS()->getType()->getPointeeType();
      if (auto ElemChars = ASTCtx->getTypeSizeInCharsIfKnown(PointeeTy);
          ElemChars && !ElemChars->isZero()) {
        unsigned PtrDiffBits = ASTCtx->getIntWidth(BO->getType());
        unsigned W = std::max(PtrDiffBits, 64u) + 2;
        llvm::APInt RawByteDiff =
            LV.extOrTrunc(PtrDiffBits) - RV.extOrTrunc(PtrDiffBits);
        llvm::APSInt Diff(RawByteDiff.sext(W), /*isUnsigned=*/false);
        llvm::APSInt ElemSz(
            llvm::APInt(W, ElemChars->getQuantity(), /*isSigned=*/true),
            /*isUnsigned=*/false);
        return IntRangeSet::single(
            Dom, truncToType(Diff / ElemSz, BO->getType(), *ASTCtx));
      }
    }
    return std::nullopt;
  }

  if (BO->getType()->isIntegralOrEnumerationType()) {
    auto L = evaluatePureExprRange(BO->getLHS(), State, EC, Depth + 1);
    auto R = evaluatePureExprRange(BO->getRHS(), State, EC, Depth + 1);
    llvm::APSInt LV, RV;
    if (L && R && L->isSingleValue(LV) && R->isSingleValue(RV))
      if (auto ResV =
              foldIntBinOp(BO->getOpcode(), LV, RV, BO->getType(), *ASTCtx))
        return IntRangeSet::single(Dom, *ResV);
    if (L && R && (BO->getOpcode() == BO_And || BO->getOpcode() == BO_Or) &&
        EC.EscapedVars) {
      if (const ValueDecl *LVD =
              extractTrackableVarExpr(BO->getLHS(), *EC.EscapedVars))
        if (LVD == extractTrackableVarExpr(BO->getRHS(), *EC.EscapedVars))
          return reprojectRangeSet(L->intersect(*R), Dom);
    }
    if (L && R && (BO->getOpcode() == BO_Add || BO->getOpcode() == BO_Sub)) {
      bool Sub = BO->getOpcode() == BO_Sub;
      if (R->isSingleValue(RV))
        return addConstToRangeSet(*L, RV, Sub, BO->getType(), *ASTCtx);
      if (L->isSingleValue(LV))
        return Sub ? subRangeSetFromConst(LV, *R, BO->getType(), *ASTCtx)
                   : addConstToRangeSet(*R, LV, /*Subtract=*/false,
                                        BO->getType(), *ASTCtx);
    }
  }
  return std::nullopt;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureConditionalRange(
    const AbstractConditionalOperator *COP, const IntDomain &Dom,
    const TrylockValueState &State, const RangeEvalCtx &EC, unsigned Depth) {
  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(COP)) {
    const Expr *Common = BCO->getCommon();
    auto CommonDom = getScalarDomain(Common->getType());
    if (!CommonDom)
      return std::nullopt;
    llvm::ArrayRef<const ValueDecl *> FalseMod =
        EC.EscapedVars ? getSubtreeModifiedVars(BCO->getFalseExpr())
                       : llvm::ArrayRef<const ValueDecl *>{};
    const bool CommonRefsFalseMod = exprReferencesAnyVar(Common, FalseMod);
    std::optional<IntRangeSet> CR;
    if (CommonRefsFalseMod) {
      TrylockValueState CommonState = State;
      eraseModifiedVarsFromState(CommonState, FalseMod, EC.PinnedExprs);
      CR = evaluatePureExprRange(Common, CommonState, EC, Depth + 1);
    } else {
      CR = evaluatePureExprRange(Common, State, EC, Depth + 1);
    }
    bool MayBeTrue = !CR || CR->mayBeNonZero();
    bool MayBeFalse = !CR || CR->mayBeZero();
    IntRangeSet Res;
    if (MayBeTrue) {
      if (!CR)
        return std::nullopt;
      IntRangeSet TrueVals =
          CR->intersect(IntRangeSet::truthSet(*CommonDom, true));
      if (!TrueVals.empty()) {
        const auto *TrueCast =
            dyn_cast<CastExpr>(stripNoOpExprWrappers(BCO->getTrueExpr()));
        if (TrueCast && isRangeMappableCast(TrueCast) &&
            stripNoOpExprWrappers(TrueCast->getSubExpr()) ==
                stripNoOpExprWrappers(Common))
          Res = Res.unionWith(reprojectRangeSet(
              applyCast(TrueCast, TrueVals, Dom, *ASTCtx), Dom));
        else
          Res = Res.unionWith(reprojectRangeSet(TrueVals, Dom));
      }
    }
    if (MayBeFalse) {
      std::optional<IntRangeSet> FR;
      if (Depth < 8 && EC.EscapedVars && !CommonRefsFalseMod) {
        TrylockValueState FalseState = State;
        constrainLeafCondition(FalseState, Common, /*WantTrue=*/false, EC,
                               Depth + 1);
        FR = FalseState.Infeasible
                 ? IntRangeSet{}
                 : evaluatePureExprRange(BCO->getFalseExpr(), FalseState, EC,
                                         Depth + 1);
      } else {
        FR = evaluatePureExprRange(BCO->getFalseExpr(), State, EC, Depth + 1);
      }
      if (!FR)
        return std::nullopt;
      Res = Res.unionWith(reprojectRangeSet(*FR, Dom));
    }
    return Res;
  }
  if (!getScalarDomain(COP->getCond()->getType()))
    return std::nullopt;
  llvm::ArrayRef<const ValueDecl *> TrueMod =
      EC.EscapedVars ? getSubtreeModifiedVars(COP->getTrueExpr())
                     : llvm::ArrayRef<const ValueDecl *>{};
  llvm::ArrayRef<const ValueDecl *> FalseMod =
      EC.EscapedVars ? getSubtreeModifiedVars(COP->getFalseExpr())
                     : llvm::ArrayRef<const ValueDecl *>{};
  const bool CondRefsTrueMod = exprReferencesAnyVar(COP->getCond(), TrueMod);
  const bool CondRefsFalseMod = exprReferencesAnyVar(COP->getCond(), FalseMod);
  std::optional<IntRangeSet> CR;
  if (CondRefsTrueMod || CondRefsFalseMod) {
    TrylockValueState CondState = State;
    eraseModifiedVarsFromState(CondState, TrueMod, EC.PinnedExprs);
    eraseModifiedVarsFromState(CondState, FalseMod, EC.PinnedExprs);
    CR = evaluatePureExprRange(COP->getCond(), CondState, EC, Depth + 1);
  } else {
    CR = evaluatePureExprRange(COP->getCond(), State, EC, Depth + 1);
  }
  bool MayBeTrue = true, MayBeFalse = true;
  if (CR) {
    MayBeTrue = CR->mayBeNonZero();
    MayBeFalse = CR->mayBeZero();
  }
  IntRangeSet Res;
  auto EvalArm = [&](const Expr *ArmE, bool WantTrue,
                     bool CondRefsArmMod) -> std::optional<IntRangeSet> {
    if (Depth < 8 && EC.EscapedVars && !CondRefsArmMod) {
      TrylockValueState ArmState = State;
      {
        constrainLeafCondition(ArmState, COP->getCond(), WantTrue, EC,
                               Depth + 1);
      }
      if (ArmState.Infeasible)
        return IntRangeSet{};
      return evaluatePureExprRange(ArmE, ArmState, EC, Depth + 1);
    }
    return evaluatePureExprRange(ArmE, State, EC, Depth + 1);
  };
  if (MayBeTrue) {
    auto TR = EvalArm(COP->getTrueExpr(), /*WantTrue=*/true, CondRefsTrueMod);
    if (!TR)
      return std::nullopt;
    Res = Res.unionWith(reprojectRangeSet(*TR, Dom));
  }
  if (MayBeFalse) {
    auto FR =
        EvalArm(COP->getFalseExpr(), /*WantTrue=*/false, CondRefsFalseMod);
    if (!FR)
      return std::nullopt;
    Res = Res.unionWith(reprojectRangeSet(*FR, Dom));
  }
  return Res;
}

bool threadSafety::stmtContainsExpr(const Stmt *Root, const Expr *Target) {
  if (!Root || !Target)
    return false;
  SmallVector<const Stmt *, 16> Worklist = {Root};
  while (!Worklist.empty()) {
    const Stmt *S = Worklist.pop_back_val();
    if (!S)
      continue;
    if (S == Target)
      return true;
    for (const Stmt *Child : S->children())
      if (Child)
        Worklist.push_back(Child);
  }
  return false;
}

/// Record in \p State that the trylock result \p Def is no longer stored in
/// any variable.
void threadSafety::addOverwrittenTrylockDef(
    ThreadSafetyAnalyzer::TrylockValueState &State,
    ThreadSafetyAnalyzer::OverwrittenTrylockDef Def, bool CheckUnmaterialized) {
  if (CheckUnmaterialized)
    for (const auto &[VD, DefPair] : State.UnmaterializedVarDefs)
      if (stmtContainsExpr(DefPair.first, Def.DefE))
        return;
  for (auto &Existing : State.OverwrittenTrylockDefs) {
    if (Existing.DefE != Def.DefE)
      continue;
    if (!Existing.Allowed || !Def.Allowed || Existing.Ty != Def.Ty)
      Existing.Allowed = std::nullopt;
    else
      Existing.Allowed = Existing.Allowed->unionWith(*Def.Allowed);
    return;
  }
  State.OverwrittenTrylockDefs.push_back(std::move(Def));
}

/// Return the trylock definition stored in \p VD as an OverwrittenTrylockDef.
/// \p Allowed is the set of values that \p VD may have.
ThreadSafetyAnalyzer::OverwrittenTrylockDef
threadSafety::makeOverwrittenTrylockDef(
    const ValueDecl *VD, const std::pair<const Expr *, LocalVarContext> &Def,
    std::optional<ThreadSafetyAnalyzer::IntRangeSet> Allowed) {
  return {Def.first, Def.second, VD->getType(), std::move(Allowed)};
}

void threadSafety::unionIntoValueState(
    ThreadSafetyAnalyzer::TrylockValueState &Dst,
    const ThreadSafetyAnalyzer::TrylockValueState &Src, const ASTContext &Ctx) {
  if (Src.Infeasible)
    return;
  if (Dst.Infeasible) {
    Dst = Src;
    return;
  }

  // A variable that holds different trylock results on the two paths, or a
  // trylock result on one path only, no longer holds a trylock result after
  // the join. Remember these results such that the capabilities that the
  // calls may have acquired are not forgotten.
  {
    using OverwrittenDef = ThreadSafetyAnalyzer::OverwrittenTrylockDef;
    SmallVector<std::pair<const ValueDecl *, OverwrittenDef>, 2> Lost;
    auto RangeOf = [](const ThreadSafetyAnalyzer::TrylockValueState &S,
                      const ValueDecl *VD)
        -> std::optional<ThreadSafetyAnalyzer::IntRangeSet> {
      if (auto It = S.VarRanges.find(VD); It != S.VarRanges.end())
        return It->second;
      return std::nullopt;
    };
    SmallVector<const ValueDecl *, 2> DefsToErase;
    for (const auto &[VD, DefPair] : Dst.UnmaterializedVarDefs) {
      auto It = Src.UnmaterializedVarDefs.find(VD);
      if (It == Src.UnmaterializedVarDefs.end() ||
          It->second.first != DefPair.first) {
        Lost.emplace_back(
            VD, makeOverwrittenTrylockDef(VD, DefPair, RangeOf(Dst, VD)));
        DefsToErase.push_back(VD);
      }
    }
    for (const auto &[VD, DefPair] : Src.UnmaterializedVarDefs) {
      auto It = Dst.UnmaterializedVarDefs.find(VD);
      if (It == Dst.UnmaterializedVarDefs.end() ||
          It->second.first != DefPair.first)
        Lost.emplace_back(
            VD, makeOverwrittenTrylockDef(VD, DefPair, RangeOf(Src, VD)));
    }
    // Sort the lost results by the source location of the variable that held
    // them, and keep the result of Dst before that of Src for the same
    // variable, such that the order in which these are remembered, and hence
    // the order of diagnostics, does not depend on the iteration order of a
    // map with pointer keys.
    llvm::stable_sort(Lost, [](const auto &A, const auto &B) {
      return A.first->getLocation().getRawEncoding() <
             B.first->getLocation().getRawEncoding();
    });
    // Erase the definitions first such that addOverwrittenTrylockDef() only
    // skips results that are still stored in a variable on both paths.
    for (const ValueDecl *VD : DefsToErase)
      Dst.UnmaterializedVarDefs.erase(VD);
    for (auto &Entry : Lost)
      addOverwrittenTrylockDef(Dst, std::move(Entry.second),
                               /*CheckUnmaterialized=*/true);
    for (const OverwrittenDef &Def : Src.OverwrittenTrylockDefs)
      addOverwrittenTrylockDef(Dst, Def, /*CheckUnmaterialized=*/false);
  }
  // A missing entry means that nothing is known about a value. Drop entries
  // that cover the whole domain of their type such that the state does not
  // keep growing with every branch condition, which would make the analysis
  // quadratic in the size of the function.
  auto CoversDomain = [&Ctx](const ThreadSafetyAnalyzer::IntRangeSet &R,
                             QualType Ty) {
    auto Dom = getScalarDomainForType(Ty, Ctx);
    if (!Dom || R.ranges().size() != 1)
      return false;
    const auto &[Lo, Hi] = R.ranges()[0];
    return llvm::APSInt::compareValues(Lo, Dom->Lo) <= 0 &&
           llvm::APSInt::compareValues(Hi, Dom->Hi) >= 0;
  };

  // Join the ranges of the variables or expressions in DstMap and SrcMap.
  auto JoinRanges = [&](auto &DstMap, const auto &SrcMap) {
    using KeyT = typename std::remove_reference_t<decltype(DstMap)>::key_type;
    SmallVector<KeyT, 4> ToErase;
    for (auto &[Key, R] : DstMap) {
      if (auto It = SrcMap.find(Key); It != SrcMap.end()) {
        R = R.unionWith(It->second);
        R.widen(MaxStateRangeIntervals);
        if (CoversDomain(R, Key->getType()))
          ToErase.push_back(Key);
      } else {
        ToErase.push_back(Key);
      }
    }
    for (auto Key : ToErase)
      DstMap.erase(Key);
  };
  JoinRanges(Dst.VarRanges, Src.VarRanges);
  JoinRanges(Dst.ExprRanges, Src.ExprRanges);

  SmallVector<const BinaryOperator *, 2> OpsToErase;
  for (const auto &[BO, Val] : Dst.ShortCircuitedOps) {
    auto It = Src.ShortCircuitedOps.find(BO);
    if (It == Src.ShortCircuitedOps.end() || It->second != Val)
      OpsToErase.push_back(BO);
  }
  for (const BinaryOperator *BO : OpsToErase)
    Dst.ShortCircuitedOps.erase(BO);

  llvm::set_union(Dst.ConsumedTrylockAttrs, Src.ConsumedTrylockAttrs);
  // A trylock capability is only held in the joined lockset if it was
  // acquired on both paths. Keep consumed entries so a capability that was
  // acquired and released on one path is not re-materialized after the join.
  SmallVector<ThreadSafetyAnalyzer::AcquiredTrylockKey, 2> AcquiredToErase;
  for (const auto &K : Dst.AcquiredTrylockAttrs)
    if (!Src.AcquiredTrylockAttrs.contains(K) &&
        !Dst.ConsumedTrylockAttrs.contains(K))
      AcquiredToErase.push_back(K);
  for (const auto &K : AcquiredToErase)
    Dst.AcquiredTrylockAttrs.erase(K);
  for (const auto &K : Src.AcquiredTrylockAttrs)
    if (Dst.ConsumedTrylockAttrs.contains(K))
      Dst.AcquiredTrylockAttrs.insert(K);
  Dst.DiscardedTrylockCalls.insert(Src.DiscardedTrylockCalls.begin(),
                                   Src.DiscardedTrylockCalls.end());
}

/// If \p CallExp calls a trivial inline helper that returns its only argument
/// unchanged, e.g. ERR_CAST(), return the index of that argument.
std::optional<unsigned>
ThreadSafetyAnalyzer::getIdentityInlineParamIndex(const CallExpr *CallExp) {
  if (!CallExp || CallExp->getNumArgs() != 1 ||
      !isRangeTrylockReturnType(CallExp->getType()))
    return std::nullopt;
  const TrivialInlineBody *InlineInfo = lookupTrivialInlineBody(CallExp);
  if (!InlineInfo)
    return std::nullopt;
  if (InlineInfo->IdentityParam)
    return *InlineInfo->IdentityParam;
  if (!getCachedTrivialInlineBody(CallExp))
    return std::nullopt;

  bool SavedCutoff = InlineEvalHitCutoff;
  InlineEvalHitCutoff = false;
  InlineExpansionScope Scope(*this, *InlineInfo);

  std::optional<unsigned> Res;
  const auto *CS = dyn_cast_or_null<CompoundStmt>(InlineInfo->DefFD->getBody());
  if (InlineInfo->SingleRet && CS && CS->size() == 1 &&
      InlineInfo->DefFD->getNumParams() == 1) {
    const ParmVarDecl *Param = InlineInfo->DefFD->getParamDecl(0);
    const auto *DRE = dyn_cast_or_null<DeclRefExpr>(skipValuePreservingWrappers(
        InlineInfo->SingleRet, /*C=*/nullptr, /*IgnoreSideEffects=*/false));
    if (isRangeTrylockReturnType(Param->getType()) && DRE &&
        DRE->getDecl()->getCanonicalDecl() == Param->getCanonicalDecl())
      Res = 0;
  }
  if (Res || !InlineEvalHitCutoff)
    InlineInfo->IdentityParam = Res;
  InlineEvalHitCutoff |= SavedCutoff;
  return Res;
}

/// Intersect the range of \p VD in \p State with \p Constraint, marking
/// \p State as infeasible if the intersection is empty.
void threadSafety::restrictVarRange(
    ThreadSafetyAnalyzer::TrylockValueState &State, const ValueDecl *VD,
    const ThreadSafetyAnalyzer::IntDomain &Dom,
    const ThreadSafetyAnalyzer::IntRangeSet &Constraint) {
  ThreadSafetyAnalyzer::IntRangeSet Cur =
      ThreadSafetyAnalyzer::IntRangeSet::full(Dom);
  if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
    Cur = It->second;
  ThreadSafetyAnalyzer::IntRangeSet Restricted = Cur.intersect(Constraint);
  if (Restricted.empty()) {
    State.Infeasible = true;
    return;
  }
  Restricted.widen(MaxStateRangeIntervals);
  State.VarRanges[VD] = std::move(Restricted);
}

/// Calls \p F for each return value of \p Info whose condition may hold with
/// \p Init constrained by that condition at depth \p Depth.
void ThreadSafetyAnalyzer::forEachInlineReturn(
    const TrivialInlineBody &Info, const TrylockValueState &Init,
    const RangeEvalCtx &EC, unsigned Depth,
    llvm::function_ref<void(const Expr *, const TrylockValueState &)> F) {
  if (Info.SingleRet)
    return F(Info.SingleRet, Init);
  TrylockValueState TState = Init;
  TrylockValueState FState = Init;
  RangeEvalCtx CalleeEC = EC.withEscaped(&Info.CalleeEscaped);
  constrainLeafCondition(TState, Info.CondExpr, /*WantTrue=*/true, CalleeEC,
                         Depth);
  constrainLeafCondition(FState, Info.CondExpr, /*WantTrue=*/false, CalleeEC,
                         Depth);
  if (!TState.Infeasible)
    F(Info.ThenRet, TState);
  if (!FState.Infeasible)
    F(Info.ElseRet, FState);
}

/// Applies \p F to each return value of \p Info and to \p State constrained
/// by the condition of that value at depth \p Depth, and joins the results.
void ThreadSafetyAnalyzer::constrainInlineReturns(
    TrylockValueState &State, const TrivialInlineBody &Info,
    const RangeEvalCtx &EC, unsigned Depth,
    llvm::function_ref<void(TrylockValueState &, const Expr *)> F) {
  if (Info.SingleRet)
    return F(State, Info.SingleRet);
  TrylockValueState TState = State;
  TrylockValueState FState = State;
  RangeEvalCtx CalleeEC = EC.withEscaped(&Info.CalleeEscaped);
  constrainLeafCondition(TState, Info.CondExpr, /*WantTrue=*/true, CalleeEC,
                         Depth);
  if (!TState.Infeasible)
    F(TState, Info.ThenRet);
  constrainLeafCondition(FState, Info.CondExpr, /*WantTrue=*/false, CalleeEC,
                         Depth);
  if (!FState.Infeasible)
    F(FState, Info.ElseRet);
  State.Infeasible = true;
  unionIntoValueState(State, TState, *ASTCtx);
  unionIntoValueState(State, FState, *ASTCtx);
}

/// Constrain \p State such that \p VarSide EffectiveOp \p KVal holds. Returns
/// whether \p VarSide could be related to tracked variables.
bool ThreadSafetyAnalyzer::constrainExprComparison(
    TrylockValueState &State, const Expr *VarSide,
    BinaryOperator::Opcode EffectiveOp, const llvm::APSInt &KVal,
    const RangeEvalCtx &EC, unsigned Depth) {
  assert(EC.EscapedVars && "constraining requires the escaped variables");
  const auto &EscapedVars = *EC.EscapedVars;
  if (Depth == 0 && InlineDepth == 0)
    EvalStepCount = 0;
  if (State.Infeasible || ++EvalStepCount > MaxEvalSteps ||
      Depth > MaxConstrainExprDepth) {
    if (EvalStepCount > MaxEvalSteps || Depth > MaxConstrainExprDepth)
      InlineEvalHitCutoff = true;
    return false;
  }

  const Expr *E = VarSide;
  while (E) {
    if (const ValueDecl *VD = extractTrackableVarExpr(E, EscapedVars)) {
      auto VarDom = getScalarDomain(VD->getType());
      if (!VarDom)
        return false;
      if (E->getType()->isMemberPointerType() &&
          ((EffectiveOp != BO_EQ && EffectiveOp != BO_NE) || KVal != 0))
        return false;
      restrictVarRange(State, VD, *VarDom,
                       IntRangeSet::forComparison(*VarDom, EffectiveOp, KVal));
      return true;
    }

    E = skipValuePreservingWrappers(E, /*C=*/nullptr,
                                    /*IgnoreSideEffects=*/false);
    if (!E)
      return false;

    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (isBijectiveReinterpretCast(CE, *ASTCtx)) {
        if (auto CastDom = getScalarDomain(CE->getType())) {
          SmallVector<const CastExpr *, 2> Casts{CE};
          const Expr *Cur = CE->getSubExpr();
          while (const auto *SubCE =
                     dyn_cast_or_null<CastExpr>(skipValuePreservingWrappers(
                         Cur, /*C=*/nullptr, /*IgnoreSideEffects=*/false))) {
            if (!isBijectiveReinterpretCast(SubCE, *ASTCtx))
              break;
            Casts.push_back(SubCE);
            Cur = SubCE->getSubExpr();
          }
          if (const ValueDecl *VD = extractTrackableVarExpr(Cur, EscapedVars)) {
            if (auto VarDom = getScalarDomain(VD->getType())) {
              IntRangeSet CmpSet =
                  IntRangeSet::forComparison(*CastDom, EffectiveOp, KVal);
              restrictVarRange(State, VD, *VarDom,
                               mapRangeBackwardThroughBijectiveCasts(
                                   CmpSet, Casts, *VarDom, *ASTCtx));
              return true;
            }
          }
        }
      }
      // A narrowing integral cast preserves the value if the operand fits.
      if (CE->getCastKind() == CK_IntegralCast &&
          CE->getType()->isIntegralOrEnumerationType() &&
          !CE->getType()->isBooleanType() &&
          CE->getSubExpr()->getType()->isIntegralOrEnumerationType()) {
        auto DstDom = getScalarDomain(CE->getType());
        auto SubR =
            evaluatePureExprRange(CE->getSubExpr(), State, EC, Depth + 1);
        if (DstDom && SubR && SubR->subsetOf(DstDom->Lo, DstDom->Hi)) {
          E = CE->getSubExpr();
          continue;
        }
        return false;
      }
      if ((CE->getCastKind() == CK_DerivedToBase ||
           CE->getCastKind() == CK_UncheckedDerivedToBase) &&
          CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType() &&
          (EffectiveOp == BO_EQ || EffectiveOp == BO_NE) && KVal == 0) {
        E = CE->getSubExpr();
        continue;
      }
      return false;
    }

    const auto *CallExp = dyn_cast<CallExpr>(E);
    if (!CallExp || CallExp->getNumArgs() != 1)
      return false;
    // Translate the comparison of the result of a single-argument helper
    // into a constraint on the variable passed to the helper.
    const ValueDecl *CallerVD =
        extractTrackableVarExpr(CallExp->getArg(0), EscapedVars);
    auto CallerDom =
        CallerVD ? getScalarDomain(CallerVD->getType()) : std::nullopt;
    if (!CallerDom)
      return false;
    const TrivialInlineBody *InlineInfo = getCachedTrivialInlineBody(CallExp);
    if (!InlineInfo || !InlineInfo->SingleRet)
      return false;
    const auto *PVD = InlineInfo->param(0);
    auto PDom = getScalarDomain(PVD->getType());
    if (!PDom)
      return false;
    IntRangeSet CallerCur = IntRangeSet::full(*CallerDom);
    if (auto CIt = State.VarRanges.find(CallerVD); CIt != State.VarRanges.end())
      CallerCur = CIt->second;
    TrylockValueState SubState;
    SubState.VarRanges[PVD] = reprojectRangeSet(CallerCur, *PDom);
    InlineExpansionScope Scope(*this, *InlineInfo);
    if (!constrainExprComparison(
            SubState, InlineInfo->SingleRet, EffectiveOp, KVal,
            EC.withEscaped(&InlineInfo->CalleeEscaped), Depth + 1))
      return false;
    if (SubState.Infeasible)
      State.Infeasible = true;
    else if (auto PIt = SubState.VarRanges.find(PVD);
             PIt != SubState.VarRanges.end())
      restrictVarRange(State, CallerVD, *CallerDom,
                       reprojectRangeSet(PIt->second, *CallerDom));
    return true;
  }
  return false;
}

/// Constrain \p S such that the return expression \p RetE of an inline helper
/// makes the condition that calls the helper evaluate to \p WantTrue.
void ThreadSafetyAnalyzer::constrainInlineRetExpr(
    TrylockValueState &S, const Expr *RetE, bool WantTrue,
    const std::optional<std::pair<BinaryOperator::Opcode, llvm::APSInt>>
        &OuterCmp,
    const IntDomain &RetDom, const RangeEvalCtx &CalleeEC, unsigned Depth) {
  if (S.Infeasible || !RetE)
    return;
  if (!OuterCmp) {
    constrainLeafCondition(S, RetE, WantTrue, CalleeEC, Depth + 1);
    return;
  }
  BinaryOperator::Opcode EffectiveOp =
      WantTrue ? OuterCmp->first
               : BinaryOperator::negateComparisonOp(OuterCmp->first);
  const llvm::APSInt &ConstK = OuterCmp->second;
  IntRangeSet AllowedRet =
      IntRangeSet::forComparison(RetDom, EffectiveOp, ConstK);
  if (AllowedRet.empty()) {
    S.Infeasible = true;
    return;
  }
  if (auto Cur = evaluatePureExprRange(RetE, S, CalleeEC, Depth + 1)) {
    if (reprojectRangeSet(*Cur, RetDom).intersect(AllowedRet).empty()) {
      S.Infeasible = true;
      return;
    }
  }
  if (isGuaranteedZeroOrOneExpr(RetE, LocalVarMap.getEmptyContext())) {
    llvm::APSInt Zero = llvm::APSInt::get(0);
    llvm::APSInt One = llvm::APSInt::get(1);
    bool CanBeZero = AllowedRet.intersects(Zero, Zero);
    bool CanBeOne = AllowedRet.intersects(One, One);
    if (!CanBeZero && !CanBeOne)
      S.Infeasible = true;
    else if (CanBeOne && !CanBeZero)
      constrainLeafCondition(S, RetE, /*WantTrue=*/true, CalleeEC, Depth + 1);
    else if (CanBeZero && !CanBeOne)
      constrainLeafCondition(S, RetE, /*WantTrue=*/false, CalleeEC, Depth + 1);
    return;
  }
  constrainExprComparison(S, RetE, EffectiveOp, ConstK, CalleeEC, Depth + 1);
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateInlineCallRangeCond(
    const CallExpr *InlineCall, LocalVarContext C,
    std::optional<std::pair<BinaryOperator::Opcode, llvm::APSInt>> OuterCmp) {
  if (!InlineCall)
    return {};
  auto RetDomOpt = getScalarDomain(InlineCall->getType());
  if (!RetDomOpt)
    return {};

  // Check arguments before inspecting the callee body so calls unrelated to
  // range trylocks incur negligible overhead.
  const CallExpr *TargetCall = nullptr;
  LocalVarContext TargetCtx = C;
  SmallVector<unsigned, 2> TargetParamIndices;
  for (unsigned I = 0, N = InlineCall->getNumArgs(); I < N; ++I) {
    LocalVarContext ArgCtx = C;
    if (const CallExpr *ArgTrylock =
            unwrapTrylockValueExpr(InlineCall->getArg(I), ArgCtx)) {
      if (TargetCall && TargetCall != ArgTrylock)
        return {};
      TargetCall = ArgTrylock;
      TargetCtx = ArgCtx;
      TargetParamIndices.push_back(I);
    }
  }
  if (!TargetCall)
    return {};
  const NamedDecl *TargetCallee = getTrylockCallee(TargetCall);
  if (!TargetCallee)
    return {};

  const TrivialInlineBody *InlineInfo = getCachedTrivialInlineBody(InlineCall);
  if (!InlineInfo)
    return {};

  IntDomain TargetDom = getTrylockCallDomain(TargetCall);
  const IntDomain &RetDom = *RetDomOpt;

  TrylockValueState BaseCalleeState;
  for (unsigned I = 0, N = InlineCall->getNumArgs(); I < N; ++I) {
    const auto *PVD = InlineInfo->param(I);
    auto PDom = getScalarDomain(PVD->getType());
    if (llvm::is_contained(TargetParamIndices, I)) {
      if (!PDom)
        return {};
      BaseCalleeState.VarRanges[PVD] =
          reprojectRangeSet(IntRangeSet::full(TargetDom), *PDom);
    } else if (PDom) {
      TrylockValueState EmptyState;
      LocalVarContext ArgCtx = C;
      const Expr *ArgE = skipValuePreservingWrappers(
          InlineCall->getArg(I), &ArgCtx, /*IgnoreSideEffects=*/false);
      const auto *BodyEscapedVars =
          CurrentVerifier ? &CurrentVerifier->escapedVars() : nullptr;
      if (auto ArgR = ArgE
                          ? evaluatePureExprRange(ArgE, EmptyState,
                                                  RangeEvalCtx{BodyEscapedVars})
                          : std::nullopt)
        BaseCalleeState.VarRanges[PVD] = reprojectRangeSet(*ArgR, *PDom);
    }
  }

  // The return expressions of the helper are evaluated in the context of its
  // body.
  const RangeEvalCtx CalleeEC{&InlineInfo->CalleeEscaped};
  // Return the values of the trylock result for which the helper may return
  // a value that makes the condition evaluate to WantTrue, starting from
  // the parameter ranges in Init.
  auto EvalArm = [&](const TrylockValueState &Init,
                     bool WantTrue) -> IntRangeSet {
    SmallVector<std::optional<IntRangeSet>, 4> ArgRanges;
    for (unsigned I = 0, N = InlineCall->getNumArgs(); I < N; ++I) {
      const auto *PVD = InlineInfo->param(I);
      auto PDom = getScalarDomain(PVD->getType());
      auto It = Init.VarRanges.find(PVD);
      if (PDom && It != Init.VarRanges.end() &&
          !IntRangeSet::full(*PDom).subsetOfSet(It->second))
        ArgRanges.push_back(It->second);
      else
        ArgRanges.push_back(std::nullopt);
    }
    llvm::FoldingSetNodeID CacheID;
    unsigned CacheKind = OuterCmp ? (WantTrue ? 5 : 4) : (WantTrue ? 3 : 2);
    bool CanCache = profileInlineCallCacheKey(CacheID, InlineInfo->DefFD,
                                              CacheKind, ArgRanges);
    if (CanCache && OuterCmp) {
      CacheID.AddInteger(OuterCmp->first);
      OuterCmp->second.Profile(CacheID);
    }
    auto ExtractAllowed = [&](const InlineCondResult &R) -> IntRangeSet {
      if (R.Infeasible)
        return {};
      IntRangeSet Allowed = IntRangeSet::full(TargetDom);
      for (unsigned ParamIdx : TargetParamIndices)
        if (ParamIdx < R.ParamRanges.size() && R.ParamRanges[ParamIdx])
          Allowed = Allowed.intersect(
              reprojectRangeSet(*R.ParamRanges[ParamIdx], TargetDom));
      return Allowed;
    };
    if (CanCache)
      if (auto It = InlineCondCache.find_as(CacheID);
          It != InlineCondCache.end())
        return ExtractAllowed(It->second);

    bool PrevHitCutoff = InlineEvalHitCutoff;
    InlineEvalHitCutoff = false;
    if (InlineDepth == 0)
      EvalStepCount = 0;
    TrylockValueState ArmState = Init;
    {
      InlineExpansionScope Scope(*this, *InlineInfo);
      constrainInlineReturns(ArmState, *InlineInfo, CalleeEC, /*Depth=*/1,
                             [&](TrylockValueState &S, const Expr *RetE) {
                               constrainInlineRetExpr(S, RetE, WantTrue,
                                                      OuterCmp, RetDom,
                                                      CalleeEC, /*Depth=*/1);
                             });
    }
    bool HitCutoff = InlineEvalHitCutoff;
    InlineEvalHitCutoff = PrevHitCutoff || HitCutoff;
    InlineCondResult R;
    R.Infeasible = ArmState.Infeasible;
    if (!R.Infeasible) {
      for (unsigned I = 0, N = InlineCall->getNumArgs(); I < N; ++I) {
        const auto *PVD = InlineInfo->param(I);
        auto PIt = ArmState.VarRanges.find(PVD);
        R.ParamRanges.push_back(PIt != ArmState.VarRanges.end()
                                    ? std::optional(PIt->second)
                                    : std::nullopt);
      }
    }
    IntRangeSet Res = ExtractAllowed(R);
    if (CanCache && !HitCutoff)
      InlineCondCache.try_emplace(CacheID.Intern(Bpa), std::move(R));
    return Res;
  };

  IntRangeSet TrueSet, FalseSet;
  IntRangeSet FullDom = IntRangeSet::full(TargetDom);
  if (TargetParamIndices.size() == 1) {
    TrueSet = EvalArm(BaseCalleeState, /*WantTrue=*/true);
    FalseSet = EvalArm(BaseCalleeState, /*WantTrue=*/false);
  } else {
    // All target parameters receive the same value, but the parameter
    // ranges are tracked independently. Hence a condition that combines
    // several target parameters, e.g. the disjunction in the false branch of
    // IS_ERR(a) && IS_ERR(b), constrains none of them. Evaluate the helper
    // separately for each piece of the partition of the trylock result range
    // induced by the success ranges of the trylock function such that all
    // target parameters are known to be in the same piece. Whether the
    // capability is held only depends on the piece of the result.
    SmallVector<IntRangeSet, 4> Pieces{FullDom};
    for (const Attr *A : trylockAttrs(TargetCallee)) {
      if (!trylockAttrAppliesTo(A, TargetCall->getType()))
        continue;
      auto Success = getTrylockSuccessSet(A, TargetDom);
      if (!Success)
        continue;
      IntRangeSet Failure = Success->complement(TargetDom);
      SmallVector<IntRangeSet, 4> Refined;
      for (const IntRangeSet &Piece : Pieces)
        for (const IntRangeSet *Part : {&*Success, &Failure})
          if (IntRangeSet Sub = Piece.intersect(*Part); !Sub.empty())
            Refined.push_back(std::move(Sub));
      Pieces = std::move(Refined);
    }
    for (const IntRangeSet &Piece : Pieces) {
      for (const auto &[Lo, Hi] : Piece.ranges()) {
        IntRangeSet SingleInterval =
            IntRangeSet::closedRange(TargetDom, Lo, Hi);
        TrylockValueState Init = BaseCalleeState;
        for (unsigned ParamIdx : TargetParamIndices) {
          const auto *PVD = InlineInfo->param(ParamIdx);
          Init.VarRanges[PVD] = reprojectRangeSet(
              SingleInterval, *getScalarDomain(PVD->getType()));
        }
        TrueSet = TrueSet.unionWith(EvalArm(Init, /*WantTrue=*/true));
        FalseSet = FalseSet.unionWith(EvalArm(Init, /*WantTrue=*/false));
      }
    }
  }
  if (TrueSet.subsetOfSet(FullDom) && FullDom.subsetOfSet(TrueSet) &&
      FalseSet.subsetOfSet(FullDom) && FullDom.subsetOfSet(FalseSet))
    return {};
  return {TargetCall,           TargetCallee,       TargetCtx,
          std::move(TargetDom), std::move(TrueSet), std::move(FalseSet)};
}

void ThreadSafetyAnalyzer::constrainLeafCondition(TrylockValueState &State,
                                                  const Expr *Cond,
                                                  bool WantTrue,
                                                  const RangeEvalCtx &EC,
                                                  unsigned Depth) {
  assert(EC.EscapedVars && "constraining requires the escaped variables");
  const auto &EscapedVars = *EC.EscapedVars;
  if (Depth == 0 && InlineDepth == 0)
    EvalStepCount = 0;
  if (State.Infeasible || !Cond || ++EvalStepCount > MaxEvalSteps ||
      Depth > MaxConstrainExprDepth) {
    if (Cond && (EvalStepCount > MaxEvalSteps || Depth > MaxConstrainExprDepth))
      InlineEvalHitCutoff = true;
    return;
  }

  Cond = stripNoOpExprWrappers(Cond);

  bool IsCompoundCond = isa<AbstractConditionalOperator>(Cond) ||
                        (isa<UnaryOperator>(Cond) &&
                         cast<UnaryOperator>(Cond)->getOpcode() == UO_LNot) ||
                        (isa<BinaryOperator>(Cond) &&
                         (cast<BinaryOperator>(Cond)->isLogicalOp() ||
                          cast<BinaryOperator>(Cond)->getOpcode() == BO_Comma));
  if (auto CondDom = getScalarDomain(Cond->getType())) {
    IntRangeSet Allowed = IntRangeSet::truthSet(*CondDom, WantTrue);
    if (!IsCompoundCond) {
      if (auto Cur = evaluatePureExprRange(Cond, State, EC, Depth + 1)) {
        Allowed = Allowed.intersect(*Cur);
        if (Allowed.empty()) {
          State.Infeasible = true;
          return;
        }
      }
    }
    State.ExprRanges[Cond] = std::move(Allowed);
  }

  if (const auto *CE = dyn_cast<CastExpr>(Cond))
    return constrainCastCondition(CE, State, WantTrue, EC, Depth);

  if (const auto *CallExp = dyn_cast<CallExpr>(Cond))
    return constrainCallCondition(CallExp, State, WantTrue, EC, Depth);

  if (const auto *SE = dyn_cast<StmtExpr>(Cond))
    return constrainStmtExprCondition(SE, State, WantTrue, EC, Depth);

  if (const auto *UO = dyn_cast<UnaryOperator>(Cond)) {
    if (UO->getOpcode() == UO_LNot)
      constrainLeafCondition(State, UO->getSubExpr(), !WantTrue, EC, Depth + 1);
    return;
  }

  if (const ValueDecl *VD = extractTrackableVarExpr(Cond, EscapedVars)) {
    if (auto VarDom = getScalarDomain(VD->getType()))
      restrictVarRange(State, VD, *VarDom,
                       IntRangeSet::truthSet(*VarDom, WantTrue));
    return;
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(Cond))
    return constrainBinaryCondition(BO, State, WantTrue, EC, Depth);

  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(Cond))
    return constrainBinaryConditionalCondition(BCO, State, WantTrue, EC, Depth);

  if (const auto *CO = dyn_cast<ConditionalOperator>(Cond))
    return constrainConditionalCondition(CO, State, WantTrue, EC, Depth);
}

void ThreadSafetyAnalyzer::constrainCastCondition(const CastExpr *CE,
                                                  TrylockValueState &State,
                                                  bool WantTrue,
                                                  const RangeEvalCtx &EC,
                                                  unsigned Depth) {
  switch (CE->getCastKind()) {
  case CK_IntegralToBoolean:
  case CK_PointerToBoolean:
  case CK_MemberPointerToBoolean:
  case CK_BooleanToSignedIntegral:
    break;
  case CK_DerivedToBase:
  case CK_UncheckedDerivedToBase:
    if (!CE->getType()->isAnyPointerType() ||
        !CE->getSubExpr()->getType()->isAnyPointerType())
      return;
    break;
  default:
    if (!isValuePreservingCast(CE, *ASTCtx) &&
        !isBijectiveReinterpretCast(CE, *ASTCtx))
      return;
    break;
  }
  constrainLeafCondition(State, CE->getSubExpr(), WantTrue, EC, Depth + 1);
}

void ThreadSafetyAnalyzer::constrainCallCondition(const CallExpr *CallExp,
                                                  TrylockValueState &State,
                                                  bool WantTrue,
                                                  const RangeEvalCtx &EC,
                                                  unsigned Depth) {
  const auto &EscapedVars = *EC.EscapedVars;
  if (isBuiltinExpectCall(CallExp)) {
    constrainLeafCondition(State, CallExp->getArg(0), WantTrue, EC, Depth + 1);
    return;
  }
  const TrivialInlineBody *InlineInfo = lookupTrivialInlineBody(CallExp);
  if (!InlineInfo || ActiveInlineCallees.contains(InlineInfo->DefFD))
    return;
  // Expanding the helper only yields information if an argument is a
  // tracked variable or has a known range. Check this first such that
  // conditions that are unrelated to the tracked values do not use up the
  // inline expansion budget.
  SmallVector<std::optional<IntRangeSet>, 4> ArgRanges =
      evaluateInlineArgRanges(CallExp, State, EC, Depth + 1);
  if (llvm::none_of(ArgRanges, [](const auto &R) { return R.has_value(); }) &&
      llvm::none_of(CallExp->arguments(), [&](const Expr *Arg) {
        return extractTrackableVarExpr(Arg, EscapedVars);
      }))
    return;
  // The effect of the expansion on the parameters only depends on the
  // callee, the argument ranges and WantTrue. Apply a cached effect without
  // counting it against MaxInlineExpansions.
  auto ApplyToCaller = [&](const InlineCondResult &R) {
    if (R.Infeasible) {
      State.Infeasible = true;
      return;
    }
    for (unsigned I = 0, N = CallExp->getNumArgs(); I < N; ++I) {
      if (I >= R.ParamRanges.size() || !R.ParamRanges[I])
        continue;
      const ValueDecl *CallerVD =
          extractTrackableVarExpr(CallExp->getArg(I), EscapedVars);
      if (!CallerVD)
        continue;
      auto CallerDom = getScalarDomain(CallerVD->getType());
      if (!CallerDom)
        continue;
      restrictVarRange(State, CallerVD, *CallerDom,
                       reprojectRangeSet(*R.ParamRanges[I], *CallerDom));
      if (State.Infeasible)
        return;
    }
  };
  llvm::FoldingSetNodeID CacheID;
  bool CanCache = profileInlineCallCacheKey(CacheID, InlineInfo->DefFD,
                                            WantTrue ? 3 : 2, ArgRanges);
  if (CanCache)
    if (auto It = InlineCondCache.find_as(CacheID); It != InlineCondCache.end())
      return ApplyToCaller(It->second);
  if (InlineExpansionCount >= MaxInlineExpansions) {
    InlineEvalHitCutoff = true;
    return;
  }

  bool PrevHitCutoff = InlineEvalHitCutoff;
  InlineEvalHitCutoff = false;
  TrylockValueState CalleeState = makeCalleeState(*InlineInfo, ArgRanges);
  {
    InlineExpansionScope Scope(*this, *InlineInfo);
    constrainInlineReturns(CalleeState, *InlineInfo, EC, Depth + 1,
                           [&](TrylockValueState &S, const Expr *RetE) {
                             constrainLeafCondition(
                                 S, RetE, WantTrue,
                                 EC.withEscaped(&InlineInfo->CalleeEscaped),
                                 Depth + 1);
                           });
  }
  bool HitCutoff = InlineEvalHitCutoff;
  InlineEvalHitCutoff = PrevHitCutoff || HitCutoff;
  InlineCondResult R;
  R.Infeasible = CalleeState.Infeasible;
  if (!R.Infeasible) {
    for (unsigned I = 0, N = CallExp->getNumArgs(); I < N; ++I) {
      const auto *PVD = InlineInfo->param(I);
      auto PIt = CalleeState.VarRanges.find(PVD);
      R.ParamRanges.push_back(PIt != CalleeState.VarRanges.end()
                                  ? std::optional(PIt->second)
                                  : std::nullopt);
    }
  }
  ApplyToCaller(R);
  if (CanCache && !HitCutoff)
    InlineCondCache.try_emplace(CacheID.Intern(Bpa), std::move(R));
}

void ThreadSafetyAnalyzer::constrainStmtExprCondition(const StmtExpr *SE,
                                                      TrylockValueState &State,
                                                      bool WantTrue,
                                                      const RangeEvalCtx &EC,
                                                      unsigned Depth) {
  if (const Expr *Inner = getCachedPureStmtExpr(SE))
    constrainLeafCondition(State, Inner, WantTrue, EC, Depth + 1);
  else if (const Expr *Last = getStmtExprLocalValue(SE, *ASTCtx))
    constrainLeafCondition(State, Last, WantTrue, EC, Depth + 1);
}

void ThreadSafetyAnalyzer::constrainBinaryCondition(const BinaryOperator *BO,
                                                    TrylockValueState &State,
                                                    bool WantTrue,
                                                    const RangeEvalCtx &EC,
                                                    unsigned Depth) {
  if (BO->getOpcode() == BO_Comma) {
    if (!exprReferencesModifiedVars(BO->getRHS(), BO->getLHS()))
      constrainLeafCondition(State, BO->getRHS(), WantTrue, EC, Depth + 1);
    return;
  }
  if (BO->isLogicalOp()) {
    bool CanConstrainLHS =
        !exprReferencesModifiedVars(BO->getLHS(), BO->getRHS());
    // A true && or a false || constrains both operands. Otherwise, one of
    // the operands has the value WantTrue.
    if (WantTrue == (BO->getOpcode() == BO_LAnd)) {
      if (CanConstrainLHS)
        constrainLeafCondition(State, BO->getLHS(), WantTrue, EC, Depth + 1);
      constrainLeafCondition(State, BO->getRHS(), WantTrue, EC, Depth + 1);
    } else {
      TrylockValueState LState = State;
      TrylockValueState RState = State;
      if (CanConstrainLHS)
        constrainLeafCondition(LState, BO->getLHS(), WantTrue, EC, Depth + 1);
      constrainLeafCondition(RState, BO->getRHS(), WantTrue, EC, Depth + 1);
      State.Infeasible = true;
      unionIntoValueState(State, LState, *ASTCtx);
      unionIntoValueState(State, RState, *ASTCtx);
    }
    return;
  }

  if (BO->isRelationalOp() || BO->isEqualityOp()) {
    auto EvalSingleConst =
        [&](const Expr *Side) -> std::optional<llvm::APSInt> {
      if (auto R = evaluatePureExprRange(Side, State, EC, Depth + 1)) {
        llvm::APSInt SingleK;
        if (R->isSingleValue(SingleK))
          return SingleK;
      }
      return std::nullopt;
    };
    auto TryConstrainVarCmp = [&](const Expr *VarSide,
                                  const std::optional<llvm::APSInt> &KVal,
                                  BinaryOperator::Opcode CmpOp) -> bool {
      if (!KVal)
        return false;
      BinaryOperator::Opcode EffectiveOp =
          WantTrue ? CmpOp : BinaryOperator::negateComparisonOp(CmpOp);
      return constrainExprComparison(State, VarSide, EffectiveOp, *KVal, EC,
                                     Depth + 1);
    };

    std::optional<llvm::APSInt> RConst = EvalSingleConst(BO->getRHS());
    if (TryConstrainVarCmp(BO->getLHS(), RConst, BO->getOpcode()))
      return;
    std::optional<llvm::APSInt> LConst = EvalSingleConst(BO->getLHS());
    if (TryConstrainVarCmp(
            BO->getRHS(), LConst,
            BinaryOperator::reverseComparisonOp(BO->getOpcode())))
      return;

    if (BO->getOpcode() == BO_EQ || BO->getOpcode() == BO_NE) {
      auto TryBoolOrZeroEq =
          [&](const Expr *SubSide,
              const std::optional<llvm::APSInt> &KVal) -> bool {
        if (!KVal)
          return false;
        const llvm::APSInt &K = *KVal;
        bool Eq = (BO->getOpcode() == BO_EQ) == WantTrue;
        if (K == 0) {
          constrainLeafCondition(State, SubSide, !Eq, EC, Depth + 1);
          return true;
        }
        if (!isGuaranteedZeroOrOneExpr(SubSide, LocalVarMap.getEmptyContext()))
          return false;
        if (K == 1) {
          constrainLeafCondition(State, SubSide, Eq, EC, Depth + 1);
          return true;
        }
        if (Eq)
          State.Infeasible = true;
        return true;
      };
      if (TryBoolOrZeroEq(BO->getLHS(), RConst))
        return;
      if (TryBoolOrZeroEq(BO->getRHS(), LConst))
        return;
    }
  }
}

void ThreadSafetyAnalyzer::constrainBinaryConditionalCondition(
    const BinaryConditionalOperator *BCO, TrylockValueState &State,
    bool WantTrue, const RangeEvalCtx &EC, unsigned Depth) {
  const Expr *Common = BCO->getCommon();
  const Expr *FalseE = BCO->getFalseExpr();
  bool CanConstrainCommon = !exprReferencesModifiedVars(Common, FalseE);
  if (!WantTrue) {
    if (CanConstrainCommon)
      constrainLeafCondition(State, Common, /*WantTrue=*/false, EC, Depth + 1);
    constrainLeafCondition(State, FalseE, /*WantTrue=*/false, EC, Depth + 1);
  } else {
    TrylockValueState LState = State;
    TrylockValueState RState = State;
    if (CanConstrainCommon) {
      constrainLeafCondition(LState, Common, /*WantTrue=*/true, EC, Depth + 1);
      constrainLeafCondition(RState, Common, /*WantTrue=*/false, EC, Depth + 1);
    }
    constrainLeafCondition(RState, FalseE, /*WantTrue=*/true, EC, Depth + 1);
    State.Infeasible = true;
    unionIntoValueState(State, LState, *ASTCtx);
    unionIntoValueState(State, RState, *ASTCtx);
  }
}

void ThreadSafetyAnalyzer::constrainConditionalCondition(
    const ConditionalOperator *CO, TrylockValueState &State, bool WantTrue,
    const RangeEvalCtx &EC, unsigned Depth) {
  const Expr *CondE = CO->getCond();
  const Expr *TrueE = CO->getTrueExpr();
  const Expr *FalseE = CO->getFalseExpr();
  bool CanConstrainTrue = !exprReferencesModifiedVars(CondE, TrueE);
  bool CanConstrainFalse = !exprReferencesModifiedVars(CondE, FalseE);
  TrylockValueState TState = State;
  TrylockValueState FState = State;
  if (CanConstrainTrue)
    constrainLeafCondition(TState, CondE, /*WantTrue=*/true, EC, Depth + 1);
  constrainLeafCondition(TState, TrueE, WantTrue, EC, Depth + 1);
  if (CanConstrainFalse)
    constrainLeafCondition(FState, CondE, /*WantTrue=*/false, EC, Depth + 1);
  constrainLeafCondition(FState, FalseE, WantTrue, EC, Depth + 1);
  State.Infeasible = true;
  unionIntoValueState(State, TState, *ASTCtx);
  unionIntoValueState(State, FState, *ASTCtx);
}
