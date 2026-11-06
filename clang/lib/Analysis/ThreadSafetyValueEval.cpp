//===- ThreadSafetyValueEval.cpp - Expression value evaluation ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Helpers for unwrapping value-preserving expressions and scanning
// local variables that escape or are modified.
//
//===----------------------------------------------------------------------===//

#include "ThreadSafetyInternal.h"
#include "clang/AST/IgnoreExpr.h"

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
/// full expressions, value-preserving casts, __builtin_expect(), assignments
/// and statement expressions. If \p C is not null, also look through local
/// variables to their known definitions and update \p C to the context of
/// the definition. Looking through assignments and statement expressions with
/// multiple statements is only correct if the caller does not reason about
/// the values of variables, e.g. if it only determines the call that produced
/// a value. Returns the first expression that is not such a wrapper.
const Expr *
ThreadSafetyAnalyzer::skipValuePreservingWrappers(const Expr *E,
                                                  LocalVarContext *C) {
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
      if (BOP->getOpcode() != BO_Assign || BOP->getLHS()->refersToBitField())
        return E;
      E = BOP->getRHS();
      continue;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(E)) {
      const CompoundStmt *CS = SE->getSubStmt();
      if (!CS || CS->body_empty())
        return E;
      E = dyn_cast<Expr>(CS->body_back());
      continue;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      if (isBuiltinExpectCall(CallExp)) {
        E = CallExp->getArg(0);
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

namespace {
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

/// Helper class for scanTrylockVars() that recursively visits a statement
/// and collects the escaped and the modified local variables.
class TrylockVarScanner {
public:
  TrylockVarScanner(const ASTContext &Ctx,
                    llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
                    llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars)
      : Ctx(Ctx), EscapedVars(EscapedVars), ModifiedVars(ModifiedVars) {}

  void visit(const Stmt *S, bool InNestedClosure, bool LValueIsSafe) {
    static constexpr unsigned MaxASTWalkDepth = 512;
    if (!S || Depth >= MaxASTWalkDepth)
      return;
    ++Depth;

    // Skip unevaluated operands completely.
    if (visitUnevaluatedOperand(S, InNestedClosure, LValueIsSafe)) {
      --Depth;
      return;
    }

    if (recordClosureCaptures(S))
      InNestedClosure = true;

    if (!InNestedClosure)
      recordSafeUse(S, LValueIsSafe);

    recordDeclRef(S, InNestedClosure, LValueIsSafe);

    visitChildren(S, InNestedClosure, LValueIsSafe);
    --Depth;
  }

private:
  /// Record that the variable \p VD escapes and may be modified.
  void recordEscapedVar(const ValueDecl *VD) {
    EscapedVars.insert(VD);
    ModifiedVars.insert(VD);
  }

  /// If \p S is an operand that may not be evaluated, visit only its
  /// evaluated parts and return true.
  bool visitUnevaluatedOperand(const Stmt *S, bool InNestedClosure,
                               bool LValueIsSafe) {
    if (const auto *CE = dyn_cast<CallExpr>(S);
        CE && CE->isUnevaluatedBuiltinCall(Ctx))
      return true;
    if (isa<CXXNoexceptExpr>(S))
      return true;
    if (const auto *TE = dyn_cast<UnaryExprOrTypeTraitExpr>(S)) {
      if (isEvaluatedUnaryExprOrTypeTrait(TE))
        for (const Stmt *Child : TE->children())
          visit(Child, InNestedClosure, /*LValueIsSafe=*/false);
      return true;
    }
    if (const auto *TE = dyn_cast<CXXTypeidExpr>(S)) {
      if (!TE->isTypeOperand() && TE->isPotentiallyEvaluated())
        visit(TE->getExprOperand(), InNestedClosure,
              /*LValueIsSafe=*/false);
      return true;
    }
    if (const auto *GSE = dyn_cast<GenericSelectionExpr>(S)) {
      if (!GSE->isResultDependent())
        visit(GSE->getResultExpr(), InNestedClosure, LValueIsSafe);
      return true;
    }
    return false;
  }

  /// If \p S is a closure, record the variables that it captures by
  /// reference and return true.
  bool recordClosureCaptures(const Stmt *S) {
    if (const auto *LE = dyn_cast<LambdaExpr>(S)) {
      for (const LambdaCapture &Cap : LE->captures()) {
        if (Cap.capturesVariable() && Cap.getCaptureKind() == LCK_ByRef) {
          const ValueDecl *VD =
              cast<ValueDecl>(Cap.getCapturedVar()->getCanonicalDecl());
          recordEscapedVar(VD);
        }
      }
      return true;
    }
    if (const auto *BE = dyn_cast<BlockExpr>(S)) {
      // The body of a block is not a child of the BlockExpr. Variables
      // captured by reference (__block variables) may be modified whenever
      // the block runs.
      if (const BlockDecl *BD = BE->getBlockDecl()) {
        for (const BlockDecl::Capture &Cap : BD->captures()) {
          if (Cap.isByRef()) {
            const ValueDecl *VD =
                cast<ValueDecl>(Cap.getVariable()->getCanonicalDecl());
            recordEscapedVar(VD);
          }
        }
        return true;
      }
    }
    return isa<CapturedStmt>(S);
  }

  /// Record the variable references in \p S that only read or assign the
  /// value of a variable and the variables that \p S modifies.
  void recordSafeUse(const Stmt *S, bool LValueIsSafe) {
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
          ModifiedVars.insert(
              cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
      }
    }
  }

  /// If \p S is a reference to a variable other than by reading or assigning
  /// its value, record that the variable escapes.
  void recordDeclRef(const Stmt *S, bool InNestedClosure, bool LValueIsSafe) {
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
      if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        const ValueDecl *CanonVD = cast<ValueDecl>(VD->getCanonicalDecl());
        if (InNestedClosure || (!LValueIsSafe && !SafeDREs.contains(DRE)))
          recordEscapedVar(CanonVD);
      }
    }
  }

  /// Visit the children of \p S and whether an lvalue child is used safely.
  void visitChildren(const Stmt *S, bool InNestedClosure, bool LValueIsSafe) {
    if (const auto *PE = dyn_cast<ParenExpr>(S)) {
      visit(PE->getSubExpr(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *FE = dyn_cast<FullExpr>(S)) {
      visit(FE->getSubExpr(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *CE = dyn_cast<CastExpr>(S)) {
      // The CFG does not contain the size expressions of variable length
      // array types in casts.
      if (const auto *ECE = dyn_cast<ExplicitCastExpr>(CE))
        forEachTypeVLAExpr(ECE->getTypeAsWritten(), [&](const Expr *Sz) {
          visit(Sz, InNestedClosure, /*LValueIsSafe=*/true);
        });
      bool ChildSafe = false;
      if (CE->getCastKind() == CK_LValueToRValue ||
          CE->getCastKind() == CK_ToVoid)
        ChildSafe = true;
      else if (CE->getCastKind() == CK_NoOp && CE->isGLValue())
        ChildSafe = LValueIsSafe;
      visit(CE->getSubExpr(), InNestedClosure, ChildSafe);
      return;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(S);
        BO && BO->getOpcode() == BO_Comma) {
      visit(BO->getLHS(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(BO->getRHS(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *CO = dyn_cast<ConditionalOperator>(S)) {
      visit(CO->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(CO->getTrueExpr(), InNestedClosure, LValueIsSafe);
      visit(CO->getFalseExpr(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(S)) {
      visit(BCO->getCommon(), InNestedClosure, LValueIsSafe);
      visit(BCO->getFalseExpr(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *OVE = dyn_cast<OpaqueValueExpr>(S)) {
      visit(OVE->getSourceExpr(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(S)) {
      if (const CompoundStmt *CS = SE->getSubStmt()) {
        for (const Stmt *Sub : llvm::drop_end(CS->body()))
          visit(Sub, InNestedClosure, /*LValueIsSafe=*/true);
        if (!CS->body_empty())
          visit(CS->body_back(), InNestedClosure, /*LValueIsSafe=*/false);
      }
      return;
    }
    if (const auto *CS = dyn_cast<CompoundStmt>(S)) {
      for (const Stmt *Sub : CS->body())
        visit(Sub, InNestedClosure, /*LValueIsSafe=*/true);
      return;
    }
    if (const auto *LS = dyn_cast<LabelStmt>(S)) {
      visit(LS->getSubStmt(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *AS = dyn_cast<AttributedStmt>(S)) {
      visit(AS->getSubStmt(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *DS = dyn_cast<DefaultStmt>(S)) {
      visit(DS->getSubStmt(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *CS = dyn_cast<CaseStmt>(S)) {
      visit(CS->getLHS(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(CS->getRHS(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(CS->getSubStmt(), InNestedClosure, LValueIsSafe);
      return;
    }
    if (const auto *IS = dyn_cast<IfStmt>(S)) {
      visit(IS->getInit(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(IS->getConditionVariableDeclStmt(), InNestedClosure,
            /*LValueIsSafe=*/false);
      visit(IS->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(IS->getThen(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(IS->getElse(), InNestedClosure, /*LValueIsSafe=*/true);
      return;
    }
    if (const auto *WS = dyn_cast<WhileStmt>(S)) {
      visit(WS->getConditionVariableDeclStmt(), InNestedClosure,
            /*LValueIsSafe=*/false);
      visit(WS->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(WS->getBody(), InNestedClosure, /*LValueIsSafe=*/true);
      return;
    }
    if (const auto *DS = dyn_cast<DoStmt>(S)) {
      visit(DS->getBody(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(DS->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      return;
    }
    if (const auto *FS = dyn_cast<ForStmt>(S)) {
      visit(FS->getInit(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(FS->getConditionVariableDeclStmt(), InNestedClosure,
            /*LValueIsSafe=*/false);
      visit(FS->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(FS->getInc(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(FS->getBody(), InNestedClosure, /*LValueIsSafe=*/true);
      return;
    }
    if (const auto *SS = dyn_cast<SwitchStmt>(S)) {
      visit(SS->getInit(), InNestedClosure, /*LValueIsSafe=*/true);
      visit(SS->getConditionVariableDeclStmt(), InNestedClosure,
            /*LValueIsSafe=*/false);
      visit(SS->getCond(), InNestedClosure, /*LValueIsSafe=*/false);
      visit(SS->getBody(), InNestedClosure, /*LValueIsSafe=*/true);
      return;
    }
    if (const auto *CE = dyn_cast<CallExpr>(S)) {
      visit(CE->getCallee(), InNestedClosure, /*LValueIsSafe=*/false);
      bool CanPropagateConstRef =
          LValueIsSafe || !CE->isGLValue() || CE->getType().isConstQualified();
      // A variable whose address is passed as a pointer to const cannot be
      // modified through it, unless the callee returns the pointer, e.g.
      // strchr().
      const bool ResultCannotAliasArgs = callResultCannotAliasArgs(CE);
      for (unsigned I = 0, N = CE->getNumArgs(); I < N; ++I) {
        SmallVector<const DeclRefExpr *, 2> ConstPointeeDREs;
        if (ResultCannotAliasArgs &&
            isConstPointeeParamType(getCallArgParamType(CE, I)) &&
            collectAddrOfDREs(CE->getArg(I), ConstPointeeDREs))
          SafeDREs.insert_range(ConstPointeeDREs);
        bool ArgSafe = CanPropagateConstRef && isSafeCallLValueArg(CE, I);
        visit(CE->getArg(I), InNestedClosure, ArgSafe);
      }
      return;
    }
    if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
      const CXXConstructorDecl *CD = CCE->getConstructor();
      for (unsigned I = 0, N = CCE->getNumArgs(); I < N; ++I) {
        bool ArgSafe =
            isSafeCallOrCtorLValueArg(CD, /*HasImplicitObjArg=*/false, I);
        visit(CCE->getArg(I), InNestedClosure, ArgSafe);
      }
      return;
    }

    // Note: DeclStmt::children() includes the variable initializers.
    if (const auto *DS = dyn_cast<DeclStmt>(S)) {
      visitDeclStmt(DS, InNestedClosure);
      return;
    }
    for (const Stmt *Child : S->children())
      if (Child)
        visit(Child, InNestedClosure, /*LValueIsSafe=*/false);
  }

  void visitDeclStmt(const DeclStmt *DS, bool InNestedClosure) {
    forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/true, [&](const Expr *Sz) {
      visit(Sz, InNestedClosure, /*LValueIsSafe=*/true);
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
        recordEscapedVar(cast<ValueDecl>(VD->getCanonicalDecl()));
    }
    for (const Stmt *Child : DS->children())
      if (Child)
        visit(Child, InNestedClosure,
              /*LValueIsSafe=*/ConstRefInits.contains(Child));
  }

  const ASTContext &Ctx;
  llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars;
  llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars;
  llvm::SmallPtrSet<const DeclRefExpr *, 16> SafeDREs;
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
  Scanner.visit(Root, /*InNestedClosure=*/false,
                /*LValueIsSafe=*/isa<CompoundStmt>(Root));
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
