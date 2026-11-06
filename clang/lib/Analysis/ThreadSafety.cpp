//===- ThreadSafety.cpp ---------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// A intra-procedural analysis for thread safety (e.g. deadlocks and race
// conditions), based off of an annotation system.
//
// See http://clang.llvm.org/docs/ThreadSafetyAnalysis.html
// for more information.
//
//===----------------------------------------------------------------------===//

#include "clang/Analysis/Analyses/ThreadSafety.h"
#include "ThreadSafetyInternal.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclGroup.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/IgnoreExpr.h"
#include "clang/AST/OperationKinds.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/Analysis/Analyses/ThreadSafetyCommon.h"
#include "clang/Analysis/Analyses/ThreadSafetyTIL.h"
#include "clang/Analysis/Analyses/ThreadSafetyUtil.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/OperatorKinds.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/Specifiers.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ImmutableMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SaveAndRestore.h"
#include "llvm/Support/TrailingObjects.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace clang;
using namespace threadSafety;

// Key method definition
ThreadSafetyHandler::~ThreadSafetyHandler() = default;

/// True if capability attributes on \p Param describe the function reached
/// through it rather than the argument bound to it.
///
/// Sema accepts capability attributes on a parameter for two unrelated
/// purposes: a scoped-lockable parameter, where the attributes describe the
/// locks the passed scope object holds, and a parameter naming a function to
/// call -- a function pointer or a function reference -- where they describe
/// the requirements of the function called through it.
static bool isCallbackParam(const ParmVarDecl *Param) {
  QualType T = Param->getType().getNonReferenceType();
  return T->isFunctionPointerType() || T->isFunctionType();
}

/// Issue a warning about an invalid lock expression
static void warnInvalidLock(ThreadSafetyHandler &Handler,
                            const Expr *MutexExp, const NamedDecl *D,
                            const Expr *DeclExp, StringRef Kind) {
  SourceLocation Loc;
  if (DeclExp)
    Loc = DeclExp->getExprLoc();

  // FIXME: add a note about the attribute location in MutexExp or D
  if (Loc.isValid())
    Handler.handleInvalidLockExp(Loc);
}

// This has to be defined after LocalVariableMap.
CFGBlockInfo CFGBlockInfo::getEmptyBlockInfo(LocalVariableMap &M) {
  return CFGBlockInfo(M.getEmptyContext());
}

namespace clang {
namespace threadSafety {

/// Visitor which builds a LocalVariableMap
class LLVM_LIBRARY_VISIBILITY VarMapBuilder
    : public ConstStmtVisitor<VarMapBuilder> {
public:
  LocalVariableMap* VMap;
  LocalVariableMap::Context Ctx;

  VarMapBuilder(LocalVariableMap *VM, LocalVariableMap::Context C)
      : VMap(VM), Ctx(C) {}

  // Whether Ctx has changed since the last saved context, e.g. because a
  // destructor clobbered escaped variables, such that it must be saved with
  // the next statement for which the context is looked up.
  bool PendingSave = false;

  bool clearModifiedLocalVars(const Expr *E);
  void clobberEscapedVars();

  void VisitDeclStmt(const DeclStmt *S);
  void VisitBinaryOperator(const BinaryOperator *BO);
  void VisitUnaryOperator(const UnaryOperator *UO);
  void VisitCallExpr(const CallExpr *CE);
  void VisitCXXConstructExpr(const CXXConstructExpr *CCE);
  void VisitAsmStmt(const AsmStmt *AS);
  void VisitExplicitCastExpr(const ExplicitCastExpr *CE);
};

} // namespace threadSafety
} // namespace clang

// Add new local variables to the variable map
void VarMapBuilder::VisitDeclStmt(const DeclStmt *S) {
  bool modifiedCtx = false;
  const DeclGroupRef DGrp = S->getDeclGroup();
  for (const auto *D : DGrp) {
    if (const auto *VD = dyn_cast_or_null<VarDecl>(D)) {
      const Expr *E = VD->getInit();

      // Add local variables with trivial type to the variable map
      QualType T = VD->getType();
      if (T.isTrivialType(VD->getASTContext())) {
        Ctx = VMap->addDefinition(VD, E, Ctx);
        modifiedCtx = true;
      }
    }
  }
  if (modifiedCtx)
    VMap->saveContext(S, Ctx);
}

Expr *threadSafety::ignoreNoOpCastSingleStep(Expr *E) {
  if (auto *CE = dyn_cast<CastExpr>(E); CE && CE->getCastKind() == CK_NoOp)
    return CE->getSubExpr();
  return E;
}

const DeclRefExpr *threadSafety::unwrapDirectLValueDRE(const Expr *E) {
  if (!E)
    return nullptr;
  return dyn_cast<DeclRefExpr>(
      IgnoreExprNodes(E, IgnoreParensSingleStep, ignoreNoOpCastSingleStep));
}

/// Collect the variables that the lvalue \p E may designate, i.e. the
/// variables that are modified by an assignment to or an increment of \p E.
/// Look through parentheses, no-op and lvalue bit casts, the right operand of
/// a comma, both arms of a conditional operator, assignments and prefix
/// increments and decrements, which are lvalues in C++, and dereferences of
/// the address of a variable.
void threadSafety::collectModifiedLValueDREs(
    const Expr *E, SmallVectorImpl<const DeclRefExpr *> &DREs, unsigned Depth) {
  if (!E || Depth > 32)
    return;
  E = IgnoreExprNodes(E, IgnoreParensSingleStep, ignoreNoOpCastSingleStep);
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    DREs.push_back(DRE);
  } else if (const auto *CE = dyn_cast<CastExpr>(E)) {
    // E.g. 'reinterpret_cast<void *&>(p)' designates the same variable.
    if (CE->getCastKind() == CK_LValueBitCast)
      collectModifiedLValueDREs(CE->getSubExpr(), DREs, Depth + 1);
  } else if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->getOpcode() == BO_Comma)
      collectModifiedLValueDREs(BO->getRHS(), DREs, Depth + 1);
    else if (BO->isAssignmentOp())
      collectModifiedLValueDREs(BO->getLHS(), DREs, Depth + 1);
  } else if (const auto *UO = dyn_cast<UnaryOperator>(E)) {
    if (UO->isPrefix() && UO->isIncrementDecrementOp())
      collectModifiedLValueDREs(UO->getSubExpr(), DREs, Depth + 1);
    else if (UO->getOpcode() == UO_Deref)
      // E.g. '*(void **)&p'.
      collectAddrOfDREs(UO->getSubExpr(), DREs, Depth + 1);
  } else if (const auto *CO = dyn_cast<AbstractConditionalOperator>(E)) {
    collectModifiedLValueDREs(CO->getTrueExpr(), DREs, Depth + 1);
    collectModifiedLValueDREs(CO->getFalseExpr(), DREs, Depth + 1);
  } else if (const auto *OVE = dyn_cast<OpaqueValueExpr>(E)) {
    // The common operand of a binary conditional operator.
    if (const Expr *Src = OVE->getSourceExpr())
      collectModifiedLValueDREs(Src, DREs, Depth + 1);
  }
}

/// If \p E takes the address of an lvalue, possibly through no-op and
/// pointer casts, the right operand of a comma or the arms of a conditional
/// operator, add the variables that the lvalue may designate to \p DREs.
/// Return whether \p E takes the address of an lvalue.
bool threadSafety::collectAddrOfDREs(const Expr *E,
                                     SmallVectorImpl<const DeclRefExpr *> &DREs,
                                     unsigned Depth) {
  if (Depth > 32)
    return false;
  while (E) {
    E = E->IgnoreParens();
    if (const auto *MTE = dyn_cast<MaterializeTemporaryExpr>(E)) {
      E = MTE->getSubExpr();
      continue;
    }
    if (const auto *FE = dyn_cast<FullExpr>(E)) {
      E = FE->getSubExpr();
      continue;
    }
    if (const auto *Cast = dyn_cast<CastExpr>(E)) {
      if (Cast->getCastKind() == CK_NoOp ||
          ((Cast->getCastKind() == CK_BitCast ||
            Cast->getCastKind() == CK_DerivedToBase ||
            Cast->getCastKind() == CK_UncheckedDerivedToBase) &&
           Cast->getType()->isPointerType() &&
           Cast->getSubExpr()->getType()->isPointerType())) {
        E = Cast->getSubExpr();
        continue;
      }
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(E);
        BO && BO->getOpcode() == BO_Comma) {
      E = BO->getRHS();
      continue;
    }
    if (const auto *OVE = dyn_cast<OpaqueValueExpr>(E);
        OVE && OVE->getSourceExpr()) {
      E = OVE->getSourceExpr();
      continue;
    }
    break;
  }
  if (const auto *CO = dyn_cast_or_null<AbstractConditionalOperator>(E)) {
    // E.g. 'c ? &p : &q'. Collect the variables of both arms.
    bool TrueAddr = collectAddrOfDREs(CO->getTrueExpr(), DREs, Depth + 1);
    bool FalseAddr = collectAddrOfDREs(CO->getFalseExpr(), DREs, Depth + 1);
    return TrueAddr || FalseAddr;
  }
  const auto *UO = dyn_cast_or_null<UnaryOperator>(E);
  if (!UO || UO->getOpcode() != UO_AddrOf)
    return false;
  collectModifiedLValueDREs(UO->getSubExpr(), DREs, Depth + 1);
  return true;
}

const DeclRefExpr *threadSafety::unwrapDirectModifiedDRE(const Stmt *S) {
  if (const auto *BO = dyn_cast_or_null<BinaryOperator>(S);
      BO && BO->isAssignmentOp())
    return unwrapDirectLValueDRE(BO->getLHS());
  if (const auto *UO = dyn_cast_or_null<UnaryOperator>(S);
      UO && UO->isIncrementDecrementOp())
    return unwrapDirectLValueDRE(UO->getSubExpr());
  return nullptr;
}

bool VarMapBuilder::clearModifiedLocalVars(const Expr *E) {
  SmallVector<const DeclRefExpr *, 2> DREs;
  collectModifiedLValueDREs(E, DREs);
  bool Modified = false;
  for (const DeclRefExpr *DRE : DREs) {
    const ValueDecl *VDec = DRE->getDecl();
    if (Ctx.lookup(VDec)) {
      Ctx = VMap->clearDefinition(VDec, Ctx);
      Modified = true;
    }
  }
  return Modified;
}

// Update local variable definitions in variable map
void VarMapBuilder::VisitBinaryOperator(const BinaryOperator *BO) {
  if (!BO->isAssignmentOp())
    return;

  // Update the variable map and current context.
  if (const DeclRefExpr *DRE = unwrapDirectLValueDRE(BO->getLHS())) {
    const ValueDecl *VDec = DRE->getDecl();
    if (Ctx.lookup(VDec)) {
      if (BO->getOpcode() == BO_Assign)
        Ctx = VMap->updateDefinition(VDec, BO->getRHS(), Ctx);
      else
        // FIXME -- handle compound assignment operators
        Ctx = VMap->clearDefinition(VDec, Ctx);
      VMap->saveContext(BO, Ctx);
    }
    return;
  }

  if (clearModifiedLocalVars(BO->getLHS()))
    VMap->saveContext(BO, Ctx);
}

// Invalidate the definitions of local variables that are incremented or
// decremented.
void VarMapBuilder::VisitUnaryOperator(const UnaryOperator *UO) {
  if (UO->isIncrementDecrementOp() && clearModifiedLocalVars(UO->getSubExpr()))
    VMap->saveContext(UO, Ctx);
}

/// If argument \p Idx of a call or constructor invocation passes the address
/// of or a mutable reference to an lvalue in a form that the callee may use
/// to modify it, add the variables that the lvalue may designate to \p DREs.
/// \p FPT is the prototype of the callee of an indirect call, if any.
static void collectInvalidatedCallOrCtorArgDREs(
    const FunctionDecl *FD, bool HasImplicitObjArg, ArrayRef<const Expr *> Args,
    unsigned Idx, SmallVectorImpl<const DeclRefExpr *> &DREs,
    const FunctionProtoType *FPT = nullptr) {
  const Expr *RawArg = Args[Idx];
  if (HasImplicitObjArg && Idx == 0) {
    if (!cast<CXXMethodDecl>(FD)->isConst() && RawArg->isGLValue())
      collectModifiedLValueDREs(RawArg, DREs);
    return;
  }

  unsigned ParamIdx = HasImplicitObjArg ? Idx - 1 : Idx;
  QualType ParamType;
  if (FD && ParamIdx < FD->getNumParams())
    ParamType = FD->getParamDecl(ParamIdx)->getType();
  else if (!FD && FPT && ParamIdx < FPT->getNumParams())
    ParamType = FPT->getParamType(ParamIdx);
  if (ParamType.isNull()) {
    // The parameter type is not known, e.g. for a variadic argument or an
    // indirect call without a prototype. Assume that the callee may modify
    // the lvalue.
    if (!collectAddrOfDREs(RawArg, DREs) && RawArg->isGLValue())
      collectModifiedLValueDREs(RawArg, DREs);
    return;
  }

  SmallVector<const DeclRefExpr *, 2> AddrDREs;
  if (collectAddrOfDREs(RawArg, AddrDREs)) {
    QualType NonRefTy = ParamType.getNonReferenceType();
    if (NonRefTy->isPointerType() &&
        !NonRefTy->getPointeeType().isConstQualified())
      DREs.append(AddrDREs.begin(), AddrDREs.end());
    return;
  }
  if (ParamType->isReferenceType() &&
      !ParamType->getPointeeType().isConstQualified() && RawArg->isGLValue())
    collectModifiedLValueDREs(RawArg, DREs);
}

static void
collectInvalidatedCallArgDREs(const CallExpr *CE, unsigned Idx,
                              SmallVectorImpl<const DeclRefExpr *> &DREs) {
  const FunctionDecl *FD = CE->getDirectCallee();
  ArrayRef<const Expr *> Args(CE->getArgs(), CE->getNumArgs());
  bool HasImplicitObjArg = false;
  if (const auto *MD = dyn_cast_or_null<CXXMethodDecl>(FD);
      MD && isa<CXXOperatorCallExpr>(CE)) {
    if (MD->isStatic()) {
      // The first argument of a call of a static operator is the object
      // expression, which is not passed to the operator.
      if (Idx == 0)
        return;
      return collectInvalidatedCallOrCtorArgDREs(
          FD, /*HasImplicitObjArg=*/false, Args.drop_front(), Idx - 1, DREs);
    }
    HasImplicitObjArg = MD->isImplicitObjectMemberFunction();
  }
  const FunctionProtoType *FPT = nullptr;
  if (!FD) {
    // An indirect call, e.g. through a function, block or member function
    // pointer.
    const Expr *Callee = CE->getCallee();
    QualType CalleeTy = Callee->getType();
    if (CalleeTy->isSpecificPlaceholderType(BuiltinType::BoundMember))
      CalleeTy = Expr::findBoundMemberType(Callee);
    else if (const auto *PT = CalleeTy->getAs<PointerType>())
      CalleeTy = PT->getPointeeType();
    else if (const auto *BPT = CalleeTy->getAs<BlockPointerType>())
      CalleeTy = BPT->getPointeeType();
    if (!CalleeTy.isNull())
      FPT = CalleeTy->getAs<FunctionProtoType>();
  }
  collectInvalidatedCallOrCtorArgDREs(FD, HasImplicitObjArg, Args, Idx, DREs,
                                      FPT);
}

void threadSafety::forEachInvalidatedCallOrCtorArgDRE(
    const Stmt *S, llvm::function_ref<void(const DeclRefExpr *)> Fn) {
  if (const auto *CE = dyn_cast_or_null<CallExpr>(S)) {
    const FunctionDecl *FD = CE->getDirectCallee();
    // Heuristic for likely-benign functions that pass by mutable reference.
    // This is needed to avoid a slew of false positives due to mutable
    // reference passing where the captured reference is usually passed on
    // by-value.
    if (const IdentifierInfo *II = FD ? FD->getIdentifier() : nullptr) {
      // Any kind of std::bind-like functions.
      if (II->isStr("bind") || II->isStr("bind_front"))
        return;
    }
    SmallVector<const DeclRefExpr *, 4> DREs;
    if (const auto *MCE = dyn_cast<CXXMemberCallExpr>(CE)) {
      const CXXMethodDecl *MD = MCE->getMethodDecl();
      if (!MD || (!MD->isStatic() && !MD->isConst())) {
        if (const Expr *ObjArg = MCE->getImplicitObjectArgument()) {
          if (ObjArg->getType()->isPointerType())
            collectAddrOfDREs(ObjArg, DREs);
          else if (ObjArg->isGLValue())
            collectModifiedLValueDREs(ObjArg, DREs);
        }
      }
    }
    for (unsigned Idx = 0, N = CE->getNumArgs(); Idx < N; ++Idx)
      collectInvalidatedCallArgDREs(CE, Idx, DREs);
    for (const DeclRefExpr *DRE : DREs)
      Fn(DRE);
    return;
  }
  if (const auto *CCE = dyn_cast_or_null<CXXConstructExpr>(S)) {
    const CXXConstructorDecl *CD = CCE->getConstructor();
    ArrayRef<const Expr *> Args(CCE->getArgs(), CCE->getNumArgs());
    SmallVector<const DeclRefExpr *, 4> DREs;
    for (unsigned Idx = 0, N = Args.size(); Idx < N; ++Idx)
      collectInvalidatedCallOrCtorArgDREs(CD, /*HasImplicitObjArg=*/false, Args,
                                          Idx, DREs);
    for (const DeclRefExpr *DRE : DREs)
      Fn(DRE);
  }
}

// Invalidates local variable definitions if variable escaped.
void VarMapBuilder::VisitCallExpr(const CallExpr *CE) {
  forEachInvalidatedCallOrCtorArgDRE(CE, [&](const DeclRefExpr *DRE) {
    Ctx = VMap->clearDefinition(DRE->getDecl(), Ctx);
  });
  // Save the context after the call where escaped variables' definitions (if
  // they exist) are cleared.
  VMap->saveContext(CE, Ctx);
}

void VarMapBuilder::VisitCXXConstructExpr(const CXXConstructExpr *CCE) {
  forEachInvalidatedCallOrCtorArgDRE(CCE, [&](const DeclRefExpr *DRE) {
    Ctx = VMap->clearDefinition(DRE->getDecl(), Ctx);
  });
  VMap->saveContext(CCE, Ctx);
}

void VarMapBuilder::VisitAsmStmt(const AsmStmt *AS) {
  bool Modified = false;
  for (unsigned I = 0, N = AS->getNumOutputs(); I < N; ++I)
    Modified |= clearModifiedLocalVars(AS->getOutputExpr(I));
  if (Modified)
    VMap->saveContext(AS, Ctx);
}

static void visitDeclTypeVLAExprs(QualType QT, bool IncludeTopLevelVLA,
                                  llvm::function_ref<void(const Expr *)> Fn) {
  while (!QT.isNull() && QT->isVariablyModifiedType()) {
    const Type *T = QT.getTypePtr();
    if (isa<TypedefType>(T))
      return;
    if (const auto *AT = dyn_cast<ArrayType>(T)) {
      if (IncludeTopLevelVLA)
        if (const auto *VAT = dyn_cast<VariableArrayType>(AT))
          if (const Expr *Sz = VAT->getSizeExpr())
            Fn(Sz);
      QT = AT->getElementType();
      continue;
    }
    IncludeTopLevelVLA = true;
    if (const auto *PT = dyn_cast<ParenType>(T)) {
      QT = PT->getInnerType();
      continue;
    }
    if (const auto *AT = dyn_cast<AttributedType>(T)) {
      QT = AT->getModifiedType();
      continue;
    }
    if (const auto *MQT = dyn_cast<MacroQualifiedType>(T)) {
      QT = MQT->getUnderlyingType();
      continue;
    }
    if (const auto *AdjT = dyn_cast<AdjustedType>(T)) {
      QT = AdjT->getOriginalType();
      continue;
    }
    if (const auto *PtrT = dyn_cast<PointerType>(T)) {
      QT = PtrT->getPointeeType();
      continue;
    }
    if (const auto *RefT = dyn_cast<ReferenceType>(T)) {
      QT = RefT->getPointeeType();
      continue;
    }
    if (const auto *BPtrT = dyn_cast<BlockPointerType>(T)) {
      QT = BPtrT->getPointeeType();
      continue;
    }
    if (const auto *MPtrT = dyn_cast<MemberPointerType>(T)) {
      QT = MPtrT->getPointeeType();
      continue;
    }
    if (const auto *AtomT = dyn_cast<AtomicType>(T)) {
      QT = AtomT->getValueType();
      continue;
    }
    if (const auto *FPT = dyn_cast<FunctionProtoType>(T)) {
      visitDeclTypeVLAExprs(FPT->getReturnType(), /*IncludeTopLevelVLA=*/true,
                            Fn);
      for (QualType ParamTy : FPT->getParamTypes())
        visitDeclTypeVLAExprs(ParamTy, /*IncludeTopLevelVLA=*/true, Fn);
      return;
    }
    if (const auto *FT = dyn_cast<FunctionType>(T)) {
      QT = FT->getReturnType();
      continue;
    }
    if (const auto *TOET = dyn_cast<TypeOfExprType>(T)) {
      if (const Expr *E = TOET->getUnderlyingExpr()) {
        Fn(E);
        visitDeclTypeVLAExprs(E->getType(), /*IncludeTopLevelVLA=*/true, Fn);
      }
      return;
    }
    if (const auto *TOT = dyn_cast<TypeOfType>(T)) {
      QT = TOT->getUnmodifiedType();
      continue;
    }
    break;
  }
}

/// Call \p Fn for the size expressions of the variable length array types
/// in the declarations of \p DS. If \p IncludeTopLevelVLA is false, skip the
/// size expression of the outermost array type of a declared variable or
/// typedef.
void threadSafety::forEachDeclVLAExpr(
    const DeclStmt *DS, bool IncludeTopLevelVLA,
    llvm::function_ref<void(const Expr *)> Fn) {
  if (!DS)
    return;
  for (const Decl *D : DS->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D))
      visitDeclTypeVLAExprs(VD->getType(), IncludeTopLevelVLA, Fn);
    else if (const auto *TND = dyn_cast<TypedefNameDecl>(D))
      visitDeclTypeVLAExprs(TND->getUnderlyingType(), IncludeTopLevelVLA, Fn);
  }
}

/// Call \p Fn for the size expressions of the variable length array types
/// in the type \p QT.
void threadSafety::forEachTypeVLAExpr(
    QualType QT, llvm::function_ref<void(const Expr *)> Fn) {
  visitDeclTypeVLAExprs(QT, /*IncludeTopLevelVLA=*/true, Fn);
}

// The CFG does not contain the size expressions of variable length array
// types in casts. Conservatively invalidate the definitions of the local
// variables that they reference. The context is saved with the next
// statement, since the clients of the variable map do not look up the
// context of casts.
void VarMapBuilder::VisitExplicitCastExpr(const ExplicitCastExpr *CE) {
  forEachTypeVLAExpr(CE->getTypeAsWritten(), [&](const Expr *Sz) {
    SmallVector<const Stmt *, 8> Worklist = {Sz};
    while (!Worklist.empty()) {
      const Stmt *S = Worklist.pop_back_val();
      if (!S)
        continue;
      if (const auto *DRE = dyn_cast<DeclRefExpr>(S);
          DRE && Ctx.lookup(DRE->getDecl())) {
        Ctx = VMap->clearDefinition(DRE->getDecl(), Ctx);
        PendingSave = true;
      }
      llvm::append_range(Worklist, S->children());
    }
  });
}

// Clobber the definitions of the variables that may be modified through a
// pointer or reference; see LocalVariableMap::traverseCFG().
void VarMapBuilder::clobberEscapedVars() {
  for (const ValueDecl *VD : VMap->EscapedVars) {
    LocalVariableMap::Context NewCtx = VMap->clobberDefinition(VD, Ctx);
    if (NewCtx != Ctx) {
      Ctx = NewCtx;
      PendingSave = true;
    }
  }
}

/// Whether the lvalue \p E designates a local variable that is not a
/// reference or a subobject of one, such that a modification of \p E cannot
/// modify another variable.
static bool isLocalObjectLValue(const Expr *E) {
  while (true) {
    E = E->IgnoreParens();
    if (const auto *CE = dyn_cast<CastExpr>(E);
        CE && (CE->getCastKind() == CK_NoOp ||
               CE->getCastKind() == CK_LValueBitCast)) {
      E = CE->getSubExpr();
    } else if (const auto *ME = dyn_cast<MemberExpr>(E); ME && !ME->isArrow()) {
      E = ME->getBase();
    } else if (const auto *ASE = dyn_cast<ArraySubscriptExpr>(E)) {
      // An element of a local array.
      const Expr *Base = ASE->getBase()->IgnoreParenImpCasts();
      if (!Base->getType()->isArrayType())
        break;
      E = Base;
    } else {
      break;
    }
  }
  const auto *DRE = dyn_cast<DeclRefExpr>(E);
  const auto *VD = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
  return VD && VD->hasLocalStorage() && !VD->getType()->isReferenceType();
}

/// Whether the CFG statement \p S may modify a local variable through a
/// pointer or reference, e.g. because it calls a function or assigns to the
/// object that a pointer points to.
static bool mayModifyThroughAlias(const Stmt *S) {
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    const FunctionDecl *FD = CE->getDirectCallee();
    return !FD || (!FD->hasAttr<ConstAttr>() && !FD->hasAttr<PureAttr>());
  }
  if (const auto *CCE = dyn_cast<CXXConstructExpr>(S))
    return !CCE->getConstructor()->isTrivial();
  if (const auto *BO = dyn_cast<BinaryOperator>(S))
    return BO->isAssignmentOp() && !isLocalObjectLValue(BO->getLHS());
  if (const auto *UO = dyn_cast<UnaryOperator>(S))
    return UO->isIncrementDecrementOp() &&
           !isLocalObjectLValue(UO->getSubExpr());
  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    // The CFG does not contain these size expressions.
    bool HasVLAExpr = false;
    forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/false,
                       [&](const Expr *) { HasVLAExpr = true; });
    return HasVLAExpr;
  }
  if (const auto *CE = dyn_cast<ExplicitCastExpr>(S))
    return CE->getTypeAsWritten()->isVariablyModifiedType();
  return isa<AsmStmt, AtomicExpr, CXXDeleteExpr, CXXNewExpr, ObjCMessageExpr>(
      S);
}

/// Whether the clients of LocalVariableMap look up the context after \p S;
/// see LocalVariableMap::getNextContext().
static bool hasNextContext(const Stmt *S) {
  if (const auto *BO = dyn_cast<BinaryOperator>(S))
    return BO->isAssignmentOp();
  if (const auto *UO = dyn_cast<UnaryOperator>(S))
    return UO->isIncrementDecrementOp();
  return isa<AsmStmt, CallExpr, CXXConstructExpr, DeclStmt>(S);
}

// Computes the intersection of two contexts.  The intersection is the
// set of variables which have the same definition in both contexts;
// variables with different definitions are discarded.
LocalVariableMap::Context
LocalVariableMap::intersectContexts(Context C1, Context C2) {
  Context Result = C1;
  for (const auto &P : C1) {
    const NamedDecl *Dec = P.first;
    const unsigned *I2 = C2.lookup(Dec);
    if (!I2) {
      // The variable doesn't exist on second path.
      Result = removeDefinition(Dec, Result);
    } else if (getCanonicalDefinitionID(P.second) !=
               getCanonicalDefinitionID(*I2)) {
      // If canonical definitions mismatch the underlying definitions are
      // different, invalidate.
      Result = clearDefinition(Dec, Result);
    } else if (!isClobbered(P.second) && isClobbered(*I2)) {
      // The variable may have been modified through an alias on the second
      // path.
      Result = ContextFactory.add(Result, Dec, *I2);
    }
  }
  return Result;
}

// For every variable in C, create a new variable that refers to the
// definition in C.  Return a new context that contains these new variables.
// (We use this for a naive implementation of SSA on loop back-edges.)
LocalVariableMap::Context LocalVariableMap::createReferenceContext(Context C) {
  Context Result = getEmptyContext();
  for (const auto &P : C)
    Result = addReference(P.first, P.second, Result);
  return Result;
}

// This routine also takes the intersection of C1 and C2, but it does so by
// altering the VarDefinitions.  C1 must be the result of an earlier call to
// createReferenceContext.
void LocalVariableMap::intersectBackEdge(Context C1, Context C2) {
  for (const auto &P : C1) {
    const unsigned I1 = P.second;
    VarDefinition *VDef = &VarDefinitions[I1];
    assert(VDef->isReference());

    const unsigned *I2 = C2.lookup(P.first);
    if (!I2) {
      // Variable does not exist at the end of the loop, invalidate.
      VDef->invalidateRef();
      continue;
    }

    // Compare the canonical IDs. This correctly handles chains of references
    // and determines if the variable is truly loop-invariant.
    if (VDef->CanonicalRef != getCanonicalDefinitionID(*I2))
      VDef->invalidateRef(); // Mark this variable as undefined
    else if (isClobbered(*I2))
      VDef->Clobbered = true; // Modified through an alias in the loop
  }
}

// Traverse the CFG in topological order, so all predecessors of a block
// (excluding back-edges) are visited before the block itself.  At
// each point in the code, we calculate a Context, which holds the set of
// variable definitions which are visible at that point in execution.
// Visible variables are mapped to their definitions using an array that
// contains all definitions.
//
// At join points in the CFG, the set is computed as the intersection of
// the incoming sets along each edge, E.g.
//
//                       { Context                 | VarDefinitions }
//   int x = 0;          { x -> x1                 | x1 = 0 }
//   int y = 0;          { x -> x1, y -> y1        | y1 = 0, x1 = 0 }
//   if (b) x = 1;       { x -> x2, y -> y1        | x2 = 1, y1 = 0, ... }
//   else   x = 2;       { x -> x3, y -> y1        | x3 = 2, x2 = 1, ... }
//   ...                 { y -> y1  (x is unknown) | x3 = 2, x2 = 1, ... }
//
// This is essentially a simpler and more naive version of the standard SSA
// algorithm.  Those definitions that remain in the intersection are from blocks
// that strictly dominate the current block.  We do not bother to insert proper
// phi nodes, because they are not used in our analysis; instead, wherever
// a phi node would be required, we simply remove that definition from the
// context (E.g. x above).
//
// The initial traversal does not capture back-edges, so those need to be
// handled on a separate pass.  Whenever the first pass encounters an
// incoming back edge, it duplicates the context, creating new definitions
// that refer back to the originals.  (These correspond to places where SSA
// might have to insert a phi node.)  On the second pass, these definitions are
// set to NULL if the variable has changed on the back-edge (i.e. a phi
// node was actually required.)  E.g.
//
//                       { Context           | VarDefinitions }
//   int x = 0, y = 0;   { x -> x1, y -> y1  | y1 = 0, x1 = 0 }
//   while (b)           { x -> x2, y -> y1  | [1st:] x2=x1; [2nd:] x2=NULL; }
//     x = x+1;          { x -> x3, y -> y1  | x3 = x2 + 1, ... }
//   ...                 { y -> y1           | x3 = 2, x2 = 1, ... }
void LocalVariableMap::traverseCFG(
    CFG *CFGraph, const PostOrderCFGView *SortedGraph,
    std::vector<CFGBlockInfo> &BlockInfo,
    const llvm::SmallPtrSetImpl<const Stmt *> &UnevaluatedStmts) {
  PostOrderCFGView::CFGBlockSet VisitedBlocks(CFGraph);

  for (const auto *CurrBlock : *SortedGraph) {
    unsigned CurrBlockID = CurrBlock->getBlockID();
    CFGBlockInfo *CurrBlockInfo = &BlockInfo[CurrBlockID];

    VisitedBlocks.insert(CurrBlock);

    // Calculate the entry context for the current block
    bool HasBackEdges = false;
    bool CtxInit = true;
    for (CFGBlock::const_pred_iterator PI = CurrBlock->pred_begin(),
         PE  = CurrBlock->pred_end(); PI != PE; ++PI) {
      // if *PI -> CurrBlock is a back edge, so skip it
      if (*PI == nullptr || !VisitedBlocks.alreadySet(*PI)) {
        HasBackEdges = true;
        continue;
      }

      unsigned PrevBlockID = (*PI)->getBlockID();
      CFGBlockInfo *PrevBlockInfo = &BlockInfo[PrevBlockID];

      if (CtxInit) {
        CurrBlockInfo->EntryContext = PrevBlockInfo->ExitContext;
        CtxInit = false;
      }
      else {
        CurrBlockInfo->EntryContext =
          intersectContexts(CurrBlockInfo->EntryContext,
                            PrevBlockInfo->ExitContext);
      }
    }

    // Duplicate the context if we have back-edges, so we can call
    // intersectBackEdges later.
    if (HasBackEdges)
      CurrBlockInfo->EntryContext =
        createReferenceContext(CurrBlockInfo->EntryContext);

    // Create a starting context index for the current block
    saveContext(nullptr, CurrBlockInfo->EntryContext);
    CurrBlockInfo->EntryIndex = getContextIndex();

    // Visit all the statements in the basic block.
    VarMapBuilder VMapBuilder(this, CurrBlockInfo->EntryContext);
    for (const auto &BI : *CurrBlock) {
      switch (BI.getKind()) {
      case CFGElement::Statement: {
        const Stmt *S = BI.castAs<CFGStmt>().getStmt();
        if (UnevaluatedStmts.contains(S))
          break;
        if (!EscapedVars.empty() && mayModifyThroughAlias(S))
          VMapBuilder.clobberEscapedVars();
        size_t NumSavedContexts = SavedContexts.size();
        VMapBuilder.Visit(S);
        if (VMapBuilder.PendingSave && hasNextContext(S)) {
          if (SavedContexts.size() == NumSavedContexts)
            saveContext(S, VMapBuilder.Ctx);
          VMapBuilder.PendingSave = false;
        }
        break;
      }
      case CFGElement::AutomaticObjectDtor:
      case CFGElement::BaseDtor:
      case CFGElement::CleanupFunction:
      case CFGElement::DeleteDtor:
      case CFGElement::MemberDtor:
      case CFGElement::TemporaryDtor:
        if (!EscapedVars.empty())
          VMapBuilder.clobberEscapedVars();
        break;
      default:
        break;
      }
    }
    CurrBlockInfo->ExitContext = VMapBuilder.Ctx;

    // Mark variables on back edges as "unknown" if they've been changed.
    for (CFGBlock::const_succ_iterator SI = CurrBlock->succ_begin(),
         SE  = CurrBlock->succ_end(); SI != SE; ++SI) {
      // if CurrBlock -> *SI is *not* a back edge
      if (*SI == nullptr || !VisitedBlocks.alreadySet(*SI))
        continue;

      CFGBlock *FirstLoopBlock = *SI;
      Context LoopBegin = BlockInfo[FirstLoopBlock->getBlockID()].EntryContext;
      Context LoopEnd   = CurrBlockInfo->ExitContext;
      intersectBackEdge(LoopBegin, LoopEnd);
    }
  }

  // Put an extra entry at the end of the indexed context array
  unsigned exitID = CFGraph->getExit().getBlockID();
  saveContext(nullptr, BlockInfo[exitID].ExitContext);
}

/// Find the appropriate source locations to use when producing diagnostics for
/// each block in the CFG.
static void findBlockLocations(CFG *CFGraph,
                               const PostOrderCFGView *SortedGraph,
                               std::vector<CFGBlockInfo> &BlockInfo) {
  for (const auto *CurrBlock : *SortedGraph) {
    CFGBlockInfo *CurrBlockInfo = &BlockInfo[CurrBlock->getBlockID()];

    // Find the source location of the last statement in the block, if the
    // block is not empty.
    if (const Stmt *S = CurrBlock->getTerminatorStmt()) {
      CurrBlockInfo->EntryLoc = CurrBlockInfo->ExitLoc = S->getBeginLoc();
    } else {
      for (CFGBlock::const_reverse_iterator BI = CurrBlock->rbegin(),
           BE = CurrBlock->rend(); BI != BE; ++BI) {
        // FIXME: Handle other CFGElement kinds.
        if (std::optional<CFGStmt> CS = BI->getAs<CFGStmt>()) {
          CurrBlockInfo->ExitLoc = CS->getStmt()->getBeginLoc();
          break;
        }
      }
    }

    if (CurrBlockInfo->ExitLoc.isValid()) {
      // This block contains at least one statement. Find the source location
      // of the first statement in the block.
      for (const auto &BI : *CurrBlock) {
        // FIXME: Handle other CFGElement kinds.
        if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
          CurrBlockInfo->EntryLoc = CS->getStmt()->getBeginLoc();
          break;
        }
      }
    } else if (CurrBlock->pred_size() == 1 && *CurrBlock->pred_begin() &&
               CurrBlock != &CFGraph->getExit()) {
      // The block is empty, and has a single predecessor. Use its exit
      // location.
      CurrBlockInfo->EntryLoc = CurrBlockInfo->ExitLoc =
          BlockInfo[(*CurrBlock->pred_begin())->getBlockID()].ExitLoc;
    } else if (CurrBlock->succ_size() == 1 && *CurrBlock->succ_begin()) {
      // The block is empty, and has a single successor. Use its entry
      // location.
      CurrBlockInfo->EntryLoc = CurrBlockInfo->ExitLoc =
          BlockInfo[(*CurrBlock->succ_begin())->getBlockID()].EntryLoc;
    }
  }
}

/// Process acquired_before and acquired_after attributes on Vd.
BeforeSet::BeforeInfo* BeforeSet::insertAttrExprs(const ValueDecl* Vd,
    ThreadSafetyAnalyzer& Analyzer) {
  // Create a new entry for Vd.
  BeforeInfo *Info = nullptr;
  {
    // Keep InfoPtr in its own scope in case BMap is modified later and the
    // reference becomes invalid.
    std::unique_ptr<BeforeInfo> &InfoPtr = BMap[Vd];
    if (!InfoPtr)
      InfoPtr.reset(new BeforeInfo());
    Info = InfoPtr.get();
  }

  for (const auto *At : Vd->attrs()) {
    switch (At->getKind()) {
      case attr::AcquiredBefore: {
        const auto *A = cast<AcquiredBeforeAttr>(At);

        // Read exprs from the attribute, and add them to BeforeVect.
        for (const auto *Arg : A->args()) {
          CapabilityExpr Cp =
            Analyzer.SxBuilder.translateAttrExpr(Arg, nullptr);
          if (const ValueDecl *Cpvd = Cp.valueDecl()) {
            Info->Vect.push_back(Cpvd);
            const auto It = BMap.find(Cpvd);
            if (It == BMap.end())
              insertAttrExprs(Cpvd, Analyzer);
          }
        }
        break;
      }
      case attr::AcquiredAfter: {
        const auto *A = cast<AcquiredAfterAttr>(At);

        // Read exprs from the attribute, and add them to BeforeVect.
        for (const auto *Arg : A->args()) {
          CapabilityExpr Cp =
            Analyzer.SxBuilder.translateAttrExpr(Arg, nullptr);
          if (const ValueDecl *ArgVd = Cp.valueDecl()) {
            // Get entry for mutex listed in attribute
            BeforeInfo *ArgInfo = getBeforeInfoForDecl(ArgVd, Analyzer);
            ArgInfo->Vect.push_back(Vd);
          }
        }
        break;
      }
      default:
        break;
    }
  }

  return Info;
}

BeforeSet::BeforeInfo *
BeforeSet::getBeforeInfoForDecl(const ValueDecl *Vd,
                                ThreadSafetyAnalyzer &Analyzer) {
  auto It = BMap.find(Vd);
  BeforeInfo *Info = nullptr;
  if (It == BMap.end())
    Info = insertAttrExprs(Vd, Analyzer);
  else
    Info = It->second.get();
  assert(Info && "BMap contained nullptr?");
  return Info;
}

/// Return true if any mutexes in FSet are in the acquired_before set of Vd.
void BeforeSet::checkBeforeAfter(const ValueDecl* StartVd,
                                 const FactSet& FSet,
                                 ThreadSafetyAnalyzer& Analyzer,
                                 SourceLocation Loc, StringRef CapKind) {
  SmallVector<BeforeInfo*, 8> InfoVect;

  // Do a depth-first traversal of Vd.
  // Return true if there are cycles.
  std::function<bool (const ValueDecl*)> traverse = [&](const ValueDecl* Vd) {
    if (!Vd)
      return false;

    BeforeSet::BeforeInfo *Info = getBeforeInfoForDecl(Vd, Analyzer);

    if (Info->Visited == 1)
      return true;

    if (Info->Visited == 2)
      return false;

    if (Info->Vect.empty())
      return false;

    InfoVect.push_back(Info);
    Info->Visited = 1;
    for (const auto *Vdb : Info->Vect) {
      // Exclude mutexes in our immediate before set.
      if (FSet.containsMutexDecl(Analyzer.FactMan, Vdb)) {
        StringRef L1 = StartVd->getName();
        StringRef L2 = Vdb->getName();
        Analyzer.Handler.handleLockAcquiredBefore(CapKind, L1, L2, Loc);
      }
      // Transitively search other before sets, and warn on cycles.
      if (traverse(Vdb)) {
        if (CycMap.try_emplace(Vd, true).second) {
          StringRef L1 = Vd->getName();
          Analyzer.Handler.handleBeforeAfterCycle(L1, Vd->getLocation());
        }
      }
    }
    Info->Visited = 2;
    return false;
  };

  traverse(StartVd);

  for (auto *Info : InfoVect)
    Info->Visited = 0;
}

/// Gets the value decl pointer from DeclRefExprs or MemberExprs.
static const ValueDecl *getValueDecl(const Expr *Exp) {
  if (const auto *CE = dyn_cast<ImplicitCastExpr>(Exp))
    return getValueDecl(CE->getSubExpr());

  if (const auto *DR = dyn_cast<DeclRefExpr>(Exp))
    return DR->getDecl();

  if (const auto *ME = dyn_cast<MemberExpr>(Exp))
    return ME->getMemberDecl();

  return nullptr;
}

bool ThreadSafetyAnalyzer::inCurrentScope(const CapabilityExpr &CapE) {
  const threadSafety::til::SExpr *SExp = CapE.sexpr();
  assert(SExp && "Null expressions should be ignored");

  if (const auto *LP = dyn_cast<til::LiteralPtr>(SExp)) {
    const ValueDecl *VD = LP->clangDecl();
    // Variables defined in a function are always inaccessible.
    if (!VD || !VD->isDefinedOutsideFunctionOrMethod())
      return false;
    // For now we consider static class members to be inaccessible.
    if (isa<CXXRecordDecl>(VD->getDeclContext()))
      return false;
    // Global variables are always in scope.
    return true;
  }

  // Members are in scope from methods of the same class.
  if (const auto *P = dyn_cast<til::Project>(SExp)) {
    if (!isa_and_nonnull<CXXMethodDecl>(CurrentFunction))
      return false;
    const ValueDecl *VD = P->clangDecl();
    return VD->getDeclContext() == CurrentFunction->getDeclContext();
  }

  return false;
}

/// Add a new lock to the lockset, warning if the lock is already there.
/// \param ReqAttr -- true if this is part of an initial Requires attribute.
void ThreadSafetyAnalyzer::addLock(FactSet &FSet, const FactEntry *Entry,
                                   bool ReqAttr) {
  if (Entry->shouldIgnore())
    return;

  if (!ReqAttr && !Entry->negative()) {
    // look for the negative capability, and remove it from the fact set.
    CapabilityExpr NegC = !*Entry;
    const FactEntry *Nen = FSet.findLock(FactMan, NegC);
    if (Nen) {
      FSet.removeLock(FactMan, NegC);
    } else {
      if (inCurrentScope(*Entry) && !Entry->asserted() && !Entry->reentrant())
        Handler.handleNegativeNotHeld(Entry->getKind(), Entry->toString(),
                                      NegC.toString(), Entry->loc());
    }
  }

  // Check before/after constraints
  if (!Entry->asserted() && !Entry->declared()) {
    GlobalBeforeSet->checkBeforeAfter(Entry->valueDecl(), FSet, *this,
                                      Entry->loc(), Entry->getKind());
  }

  if (const FactEntry *Cp = FSet.findLock(FactMan, *Entry)) {
    if (!Entry->asserted())
      Cp->handleLock(FSet, FactMan, *Entry, Handler);
  } else {
    FSet.addLock(FactMan, Entry);
  }
}

/// Remove a lock from the lockset, warning if the lock is not there.
/// \param UnlockLoc The source location of the unlock (only used in error msg)
void ThreadSafetyAnalyzer::removeLock(FactSet &FSet, const CapabilityExpr &Cp,
                                      SourceLocation UnlockLoc,
                                      bool FullyRemove, LockKind ReceivedKind) {
  if (Cp.shouldIgnore())
    return;

  const FactEntry *LDat = FSet.findLock(FactMan, Cp);
  if (!LDat) {
    SourceLocation PrevLoc;
    if (const FactEntry *Neg = FSet.findLock(FactMan, !Cp))
      PrevLoc = Neg->loc();
    Handler.handleUnmatchedUnlock(Cp.getKind(), Cp.toString(), UnlockLoc,
                                  PrevLoc);
    return;
  }

  // Generic lock removal doesn't care about lock kind mismatches, but
  // otherwise diagnose when the lock kinds are mismatched.
  if (ReceivedKind != LK_Generic && LDat->kind() != ReceivedKind) {
    Handler.handleIncorrectUnlockKind(Cp.getKind(), Cp.toString(), LDat->kind(),
                                      ReceivedKind, LDat->loc(), UnlockLoc);
  }

  LDat->handleUnlock(FSet, FactMan, Cp, UnlockLoc, FullyRemove, Handler);
}

/// Extract the list of mutexIDs from the attribute on an expression,
/// and push them onto Mtxs, discarding any duplicates.
template <typename AttrType>
void ThreadSafetyAnalyzer::getMutexIDs(CapExprSet &Mtxs, AttrType *Attr,
                                       const Expr *Exp, const NamedDecl *D,
                                       til::SExpr *Self) {
  if (Attr->args_size() == 0) {
    // A constructor of a scoped_lockable class does not acquire the object
    // that it constructs.
    if (const auto *CD = dyn_cast_or_null<CXXConstructorDecl>(D))
      if (CD->getParent()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>())
        return;
    // The mutex held is the "this" object.
    CapabilityExpr Cp = SxBuilder.translateAttrExpr(nullptr, D, Exp, Self);
    if (Cp.isInvalid()) {
      warnInvalidLock(Handler, nullptr, D, Exp, Cp.getKind());
      return;
    }
    // else
    if (!Cp.shouldIgnore())
      Mtxs.push_back_nodup(Cp);
    return;
  }

  for (const auto *Arg : Attr->args()) {
    CapabilityExpr Cp = SxBuilder.translateAttrExpr(Arg, D, Exp, Self);
    if (Cp.isInvalid()) {
      warnInvalidLock(Handler, nullptr, D, Exp, Cp.getKind());
      continue;
    }
    // else
    if (!Cp.shouldIgnore())
      Mtxs.push_back_nodup(Cp);
  }
}

std::optional<llvm::APSInt>
threadSafety::getIntegralOrEnumConstantExpr(const Expr *E,
                                            const ASTContext &Ctx) {
  if (!E || E->isValueDependent() || E->isTypeDependent() ||
      !E->getType()->isIntegralOrEnumerationType())
    return std::nullopt;
  if (!Ctx.getLangOpts().CPlusPlus11 && !E->isIntegerConstantExpr(Ctx))
    return std::nullopt;
  // Attribute arguments are parsed in an unevaluated context without an
  // enclosing ExprWithCleanups, which makes isCXX11ConstantExpr() reject
  // temporaries with constexpr destructors. Evaluate as an integer constant
  // while rejecting any notes or UB, matching
  // Sema::VerifyIntegerConstantExpression().
  Expr::EvalResult EvalResult;
  SmallVector<PartialDiagnosticAt, 4> Notes;
  EvalResult.Diag = &Notes;
  if (E->EvaluateAsInt(EvalResult, Ctx, Expr::SE_NoSideEffects,
                       /*InConstantContext=*/true) &&
      !EvalResult.HasUndefinedBehavior && Notes.empty())
    return EvalResult.Val.getInt();
  return std::nullopt;
}

std::optional<llvm::APSInt>
threadSafety::evaluateRuntimeIntConstant(const Expr *E, const ASTContext &Ctx) {
  if (!E || E->isValueDependent() || E->isTypeDependent() ||
      !E->getType()->isIntegralOrEnumerationType())
    return std::nullopt;
  Expr::EvalResult EvalResult;
  SmallVector<PartialDiagnosticAt, 4> Notes;
  EvalResult.Diag = &Notes;
  if (E->EvaluateAsInt(EvalResult, Ctx, Expr::SE_NoSideEffects,
                       /*InConstantContext=*/false) &&
      !EvalResult.HasUndefinedBehavior && Notes.empty())
    return EvalResult.Val.getInt();
  return std::nullopt;
}

std::optional<std::pair<llvm::APSInt, llvm::APSInt>>
threadSafety::getTrylockSuccessRange(const TryAcquireCapabilityRangeAttr *A,
                                     const ASTContext &Ctx) {
  const Expr *FirstE = A->getFirstSuccessValue();
  const Expr *LastE = A->getLastSuccessValue();
  if (!FirstE || !LastE || FirstE->isTypeDependent() ||
      LastE->isTypeDependent() || FirstE->getType()->isBooleanType() ||
      LastE->getType()->isBooleanType() ||
      !FirstE->getType()->isIntegralOrUnscopedEnumerationType() ||
      !LastE->getType()->isIntegralOrUnscopedEnumerationType())
    return std::nullopt;
  auto First = getIntegralOrEnumConstantExpr(FirstE, Ctx);
  auto Last = getIntegralOrEnumConstantExpr(LastE, Ctx);
  if (!First || !Last)
    return std::nullopt;
  return std::make_pair(std::move(*First), std::move(*Last));
}

bool threadSafety::isRangeTrylockReturnType(QualType Ty) {
  return !Ty.isNull() && !Ty->isDependentType() &&
         ((!Ty->isBooleanType() && Ty->isIntegralOrUnscopedEnumerationType()) ||
          Ty->isAnyPointerType());
}

bool threadSafety::getStaticBooleanValue(const Expr *E, const ASTContext &Ctx,
                                         bool &TCond) {
  if (!E || E->isValueDependent() || E->isTypeDependent())
    return false;
  E = E->IgnoreParens();
  if (isa<CXXNullPtrLiteralExpr, GNUNullExpr>(E)) {
    TCond = false;
    return true;
  }
  if (const auto *BLE = dyn_cast<CXXBoolLiteralExpr>(E)) {
    TCond = BLE->getValue();
    return true;
  }
  if (const auto *ILE = dyn_cast<IntegerLiteral>(E)) {
    TCond = ILE->getValue().getBoolValue();
    return true;
  }
  if (E->getType()->isIntegralOrEnumerationType()) {
    if (auto ICE = evaluateRuntimeIntConstant(E, Ctx)) {
      TCond = ICE->getBoolValue();
      return true;
    }
  }
  if (const auto *CE = dyn_cast<CastExpr>(E)) {
    if (CE->getCastKind() == CK_NullToPointer ||
        CE->getCastKind() == CK_NullToMemberPointer) {
      TCond = false;
      return true;
    }
    if (CE->getCastKind() == CK_NoOp ||
        CE->getCastKind() == CK_LValueToRValue ||
        CE->getCastKind() == CK_IntegralToBoolean ||
        CE->getCastKind() == CK_PointerToBoolean ||
        CE->getCastKind() == CK_MemberPointerToBoolean ||
        isa<ImplicitCastExpr>(CE))
      return getStaticBooleanValue(CE->getSubExpr(), Ctx, TCond);
  }
  return false;
}

/// Whether \p A is a try_acquire_capability or try_acquire_capability_range
/// attribute.
bool threadSafety::isTrylockAttr(const Attr *A) {
  return isa<TryAcquireCapabilityAttr, TryAcquireCapabilityRangeAttr>(A);
}

/// The trylock attributes of \p D in declaration order.
static auto trylockAttrs(const Decl *D) {
  return llvm::make_filter_range(D->attrs(), isTrylockAttr);
}

/// Call \p F with trylock attribute \p A cast to its attribute class.
template <typename Fn> static auto visitTrylockAttr(const Attr *A, Fn &&F) {
  if (const auto *TA = dyn_cast<TryAcquireCapabilityAttr>(A))
    return F(TA);
  return F(cast<TryAcquireCapabilityRangeAttr>(A));
}

bool threadSafety::isSharedTrylockAttr(const Attr *A) {
  return visitTrylockAttr(A, [](const auto *TA) { return TA->isShared(); });
}

void ThreadSafetyAnalyzer::getTrylockMutexIDs(CapExprSet &Mtxs, const Attr *A,
                                              const Expr *Exp,
                                              const NamedDecl *D) {
  visitTrylockAttr(A, [&](const auto *TA) { getMutexIDs(Mtxs, TA, Exp, D); });
}

/// Add the capabilities that the trylock attribute \p A of \p Callee names to
/// \p ExclusiveCaps or \p SharedCaps. Returns whether \p A names any
/// capability.
bool ThreadSafetyAnalyzer::collectTrylockCaps(const Attr *A,
                                              const Expr *CallExp,
                                              const NamedDecl *Callee,
                                              CapExprSet &ExclusiveCaps,
                                              CapExprSet &SharedCaps) {
  CapExprSet AttrLocks;
  getTrylockMutexIDs(AttrLocks, A, CallExp, Callee);
  CapExprSet &Dest = isSharedTrylockAttr(A) ? SharedCaps : ExclusiveCaps;
  for (const auto &Cap : AttrLocks)
    Dest.push_back_nodup(Cap);
  return !AttrLocks.empty();
}

/// Add the capabilities acquired by a successful trylock call at \p Loc to
/// \p FSet.
void ThreadSafetyAnalyzer::addTrylockFacts(FactSet &FSet,
                                           const CapExprSet &ExclusiveCaps,
                                           const CapExprSet &SharedCaps,
                                           SourceLocation Loc) {
  auto AddTrylockFact = [&](const CapabilityExpr &Cap, LockKind LK) {
    const FactEntry *Existing = FSet.findLock(FactMan, Cap);
    if (Existing && Existing->loc() == Loc && !Existing->asserted()) {
      // The fact comes from the same trylock call, e.g. because a join kept
      // the shared fact of a call that acquires the capability exclusively
      // for other return values, or because the call has both an exclusive
      // and a shared trylock attribute for the capability. Upgrade a shared
      // fact to an exclusive fact instead of reporting a double acquisition.
      if (Existing->kind() == LK_Shared && LK == LK_Exclusive)
        FSet.replaceLock(FactMan, Cap,
                         FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
      return;
    }
    addLock(FSet, FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
  };
  for (const auto &Cap : ExclusiveCaps)
    AddTrylockFact(Cap, LK_Exclusive);
  for (const auto &Cap : SharedCaps)
    AddTrylockFact(Cap, LK_Shared);
}

/// Returns the set of return values in \p Dom for which a call of a function
/// with the trylock attribute \p A acquires the capabilities named by \p A, or
/// std::nullopt if the success value(s) of \p A cannot be evaluated.
std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::getTrylockSuccessSet(const Attr *A,
                                           const IntDomain &Dom) const {
  if (const auto *TA = dyn_cast<TryAcquireCapabilityAttr>(A)) {
    auto SuccessVal =
        getIntegralOrEnumConstantExpr(TA->getSuccessValue(), *ASTCtx);
    if (!SuccessVal)
      return std::nullopt;
    return IntRangeSet::truthSet(Dom, SuccessVal->getBoolValue());
  }
  auto Range =
      getTrylockSuccessRange(cast<TryAcquireCapabilityRangeAttr>(A), *ASTCtx);
  if (!Range)
    return std::nullopt;
  return IntRangeSet::closedRange(Dom, Range->first, Range->second);
}

static bool isTrylockReturnType(QualType Ty) {
  return !Ty.isNull() && !Ty->isDependentType() &&
         (Ty->isIntegralOrEnumerationType() || Ty->isAnyPointerType() ||
          Ty->isMemberPointerType() || Ty->isRealFloatingType() ||
          Ty->isAnyComplexType());
}

/// Whether the trylock attribute \p A applies to a call that returns \p RetTy.
/// try_acquire_capability_range only applies to non-boolean integer, unscoped
/// enumeration and pointer return types; try_acquire_capability applies to
/// boolean, integer, enumeration, pointer, floating-point and complex return
/// types. Floating-point and complex results are only modeled as zero or
/// non-zero.
bool threadSafety::trylockAttrAppliesTo(const Attr *A, QualType RetTy) {
  if (isa<TryAcquireCapabilityRangeAttr>(A))
    return isRangeTrylockReturnType(RetTy);
  return isTrylockReturnType(RetTy);
}

/// Returns the union of the success sets of \p A and of any other trylock
/// attributes of \p Callee that acquire the same capabilities with the same
/// lock kind.
std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::getCombinedTrylockSuccessSet(const Attr *A,
                                                   const Expr *CallExp,
                                                   const NamedDecl *Callee,
                                                   const IntDomain &Dom,
                                                   bool ExactInt) {
  auto SuccSet = getTrylockSuccessSet(A, Dom);
  if (!SuccSet)
    return std::nullopt;
  const bool Shared = isSharedTrylockAttr(A);
  std::optional<CapExprSet> CapsA;
  for (const Attr *Other : trylockAttrs(Callee)) {
    if (Other == A || isSharedTrylockAttr(Other) != Shared ||
        !trylockAttrAppliesTo(Other, CallExp->getType()) ||
        (isa<TryAcquireCapabilityRangeAttr>(Other) && !ExactInt))
      continue;
    if (!CapsA) {
      CapsA.emplace();
      getTrylockMutexIDs(*CapsA, A, CallExp, Callee);
      if (CapsA->empty())
        break;
    }
    CapExprSet CapsOther;
    getTrylockMutexIDs(CapsOther, Other, CallExp, Callee);
    if (!llvm::all_of(*CapsA, [&](const CapabilityExpr &CA) {
          return llvm::any_of(CapsOther, [&](const CapabilityExpr &CO) {
            return CO.equals(CA);
          });
        }))
      continue;
    if (auto OtherSuccSet = getTrylockSuccessSet(Other, Dom))
      *SuccSet = SuccSet->unionWith(*OtherSuccSet);
  }
  return SuccSet;
}

/// If \p CallExp calls a function with a trylock attribute that applies to the
/// result of the call, return the callee.
const NamedDecl *threadSafety::getTrylockCallee(const CallExpr *CallExp) {
  if (!CallExp)
    return nullptr;
  QualType Ty = CallExp->getType();
  if (!isTrylockReturnType(Ty))
    return nullptr;
  const auto *FunDecl = dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl());
  if (!FunDecl || llvm::none_of(trylockAttrs(FunDecl), [&](const Attr *A) {
        return trylockAttrAppliesTo(A, Ty);
      }))
    return nullptr;
  return FunDecl;
}

/// The integer domain of the result of the trylock call \p CallExp. Results of
/// a floating-point or complex type, and of an unsupported return type during
/// error recovery, are modeled as zero (0) or non-zero (1).
ThreadSafetyAnalyzer::IntDomain
ThreadSafetyAnalyzer::getTrylockCallDomain(const CallExpr *CallExp) const {
  if (auto Dom = getScalarDomain(CallExp->getType()))
    return *Dom;
  return IntDomain::forType(ASTCtx->BoolTy, *ASTCtx);
}

/// Find the lockset that holds on the edge between PredBlock
/// and CurrBlock.  The edge set is the exit set of PredBlock (passed
/// as the ExitSet parameter) plus any trylocks, which are conditionally held.
/// The capabilities of a trylock call are only added if every value that the
/// call may return on the edge indicates success. If \p Pending is non-null,
/// narrow the return values of the call using any entry for it in \p Pending
/// and update \p Pending with the return values and attributes on the edge.
void ThreadSafetyAnalyzer::getEdgeLockset(FactSet &Result,
                                          const FactSet &ExitSet,
                                          const CFGBlock *PredBlock,
                                          const CFGBlock *CurrBlock,
                                          PendingTrylockRanges *Pending) {
  Result = ExitSet;

  TrylockRangeCondResult Cond;
  const SwitchCaseTable *Table;
  SmallVector<const CastExpr *, 2> SwitchCasts;
  if (!getTerminatorTrylockCond(PredBlock, Cond, Table, SwitchCasts))
    return;
  IntRangeSet EdgeSet;
  bool IsShortCircuitConfluence = false;
  if (Table) {
    EdgeSet = mapRangeBackwardThroughBijectiveCasts(
        getSwitchEdgeSet(*Table, CurrBlock), SwitchCasts, Cond.Dom, *ASTCtx);
  } else {
    auto [IsTrue, IsFalse] = getBranchEdgeKinds(PredBlock, CurrBlock);
    if (IsTrue)
      EdgeSet = EdgeSet.unionWith(Cond.TrueSet);
    if (IsFalse)
      EdgeSet = EdgeSet.unionWith(Cond.FalseSet);
    const auto *TermBO =
        dyn_cast_or_null<BinaryOperator>(PredBlock->getTerminatorStmt());
    if (!TermBO)
      TermBO = dyn_cast_or_null<BinaryOperator>(stripNoOpExprWrappers(
          dyn_cast_or_null<Expr>(PredBlock->getTerminatorCondition(
              /*StripParens=*/false))));
    if (TermBO && TermBO->isLogicalOp())
      IsShortCircuitConfluence =
          (TermBO->getOpcode() == BO_LAnd && IsFalse && !IsTrue) ||
          (TermBO->getOpcode() == BO_LOr && IsTrue && !IsFalse);
  }

  // Restrict the values to those that the call may have returned according
  // to the branch conditions on the path to this edge.
  IntRangeSet Narrowed = EdgeSet;
  PendingTrylockRange::AttrValueMap PendingAcquired;
  PendingTrylockRange::AttrValueMap PendingConsumed;
  if (Pending) {
    auto It = llvm::find_if(*Pending, [&](const PendingTrylockRange &P) {
      return P.Call == Cond.Call;
    });
    if (It != Pending->end()) {
      if (It->Dom == Cond.Dom) {
        Narrowed = EdgeSet.intersect(It->Values);
        if (!Narrowed.empty() || !IsShortCircuitConfluence)
          EdgeSet = Narrowed;
        for (const auto &[A, V] : It->AcquiredAttrs)
          PendingAcquired[A] = V.intersect(EdgeSet);
        for (const auto &[A, V] : It->ConsumedValues)
          if (IntRangeSet S = V.intersect(EdgeSet); !S.empty())
            PendingConsumed[A] = std::move(S);
      } else if (!EdgeSet.empty()) {
        // The result of the call has been tested in another domain. Assume
        // that the capabilities have been acquired or released for all
        // values of this domain.
        for (const auto &[A, V] : It->AcquiredAttrs)
          PendingAcquired[A] = EdgeSet;
        for (const auto &[A, V] : It->ConsumedValues)
          PendingConsumed[A] = EdgeSet;
      }
      Pending->erase(It);
    }
  }
  const bool KeepPending =
      Pending && LastTrylockCondBlock.lookup(Cond.Call) != PredBlock;
  if (!EdgeSet.empty()) {
    LocalVarLookupScope Lookup(*this, Cond.CallCtx);
    CapExprSet ExclusiveLocksToAdd, SharedLocksToAdd;
    for (const Attr *A : trylockAttrs(Cond.Callee)) {
      if (!trylockAttrAppliesTo(A, Cond.Call->getType()) ||
          PendingAcquired.contains(A) || PendingConsumed.contains(A))
        continue;
      auto SuccSet =
          getCombinedTrylockSuccessSet(A, Cond.Call, Cond.Callee, Cond.Dom);
      if (!SuccSet || !EdgeSet.subsetOfSet(*SuccSet))
        continue;
      // If the left-hand side of a logical operator may short-circuit to the
      // successor of this edge whether or not the call succeeded, e.g. if
      // 'other' is false in 'if (p && other && is_err(p))', the capabilities
      // are not acquired on that edge and the successor cannot tell whether
      // they are held. Leave it to a later branch on the result of the call
      // to add them.
      if (Pending && IsShortCircuitConfluence &&
          Cond.ShortCircuitSet.intersectsSet(*SuccSet) &&
          !Cond.ShortCircuitSet.subsetOfSet(*SuccSet))
        continue;
      if (collectTrylockCaps(A, Cond.Call, Cond.Callee, ExclusiveLocksToAdd,
                             SharedLocksToAdd))
        PendingAcquired[A] = EdgeSet;
    }
    addTrylockFacts(Result, ExclusiveLocksToAdd, SharedLocksToAdd,
                    Cond.Call->getExprLoc());
  }
  // Remember the values that the call may have returned on this edge and the
  // attributes that have been acquired or consumed, such that a later branch
  // on the same result can combine the checks, e.g.
  // 'if (!p) return; if (IS_ERR(p)) return;'.
  if (KeepPending)
    Pending->push_back({Cond.Call, Cond.CallCtx, Cond.Dom, std::move(Narrowed),
                        std::move(PendingAcquired),
                        std::move(PendingConsumed)});
}

/// If the terminator of \p Block branches on the result of a try-lock call
/// (possibly stored in a local variable), add the capabilities acquired by
/// that call to \p Caps.
void ThreadSafetyAnalyzer::getTerminatorTrylockCaps(
    const CFGBlock *Block, CapExprSet &Caps,
    const PendingTrylockRanges *Pending) {
  TrylockRangeCondResult Cond;
  const SwitchCaseTable *Table;
  SmallVector<const CastExpr *, 2> SwitchCasts;
  if (!getTerminatorTrylockCond(Block, Cond, Table, SwitchCasts))
    return;
  SmallVector<IntRangeSet, 4> BranchSets;
  if (Table) {
    for (const auto &[CS, CaseSet] : Table->CaseSets)
      BranchSets.push_back(mapRangeBackwardThroughBijectiveCasts(
          CaseSet, SwitchCasts, Cond.Dom, *ASTCtx));
    BranchSets.push_back(mapRangeBackwardThroughBijectiveCasts(
        Table->DefaultSet, SwitchCasts, Cond.Dom, *ASTCtx));
  } else {
    BranchSets.push_back(std::move(Cond.TrueSet));
    BranchSets.push_back(std::move(Cond.FalseSet));
  }
  const PendingTrylockRange *PendingEntry = nullptr;
  if (Pending) {
    auto It = llvm::find_if(*Pending, [&](const PendingTrylockRange &P) {
      return P.Call == Cond.Call && P.Dom == Cond.Dom;
    });
    if (It != Pending->end()) {
      PendingEntry = &*It;
      for (IntRangeSet &S : BranchSets)
        S = S.intersect(It->Values);
    }
  }

  LocalVarLookupScope Lookup(*this, Cond.CallCtx);
  for (const Attr *A : trylockAttrs(Cond.Callee)) {
    if (!trylockAttrAppliesTo(A, Cond.Call->getType()))
      continue;
    auto SuccSet =
        getCombinedTrylockSuccessSet(A, Cond.Call, Cond.Callee, Cond.Dom);
    if (!SuccSet)
      continue;
    // A branch is consistent with the lockset of its successor if branching
    // acquires the capabilities on it, i.e. if all its values indicate
    // success and the capabilities have not been released for any of them,
    // or if the capabilities are not held on any path into it, i.e. if none
    // of its values indicates success or, if the call has been tested
    // before, if the capabilities have not been acquired for any of them.
    IntRangeSet AcquirableSet = *SuccSet;
    const IntRangeSet *HeldSet = nullptr;
    if (PendingEntry) {
      if (auto It = PendingEntry->ConsumedValues.find(A);
          It != PendingEntry->ConsumedValues.end())
        AcquirableSet =
            AcquirableSet.intersect(It->second.complement(Cond.Dom));
      if (auto It = PendingEntry->AcquiredAttrs.find(A);
          It != PendingEntry->AcquiredAttrs.end())
        HeldSet = &It->second;
    }
    bool CleanPartition = llvm::all_of(BranchSets, [&](const IntRangeSet &S) {
      return S.empty() || S.subsetOfSet(AcquirableSet) ||
             !S.intersectsSet(*SuccSet) ||
             (HeldSet && !S.intersectsSet(*HeldSet));
    });
    if (CleanPartition)
      getTrylockMutexIDs(Caps, A, Cond.Call, Cond.Callee);
  }
}

bool threadSafety::isEvaluatedUnaryExprOrTypeTrait(
    const UnaryExprOrTypeTraitExpr *TE) {
  if (TE->getKind() != UETT_SizeOf && TE->getKind() != UETT_CountOf)
    return false;
  return TE->getTypeOfArgument()->isVariableArrayType();
}

namespace clang {
namespace threadSafety {

/// We use this class to visit different types of expressions in
/// CFGBlocks, and build up the lockset.
/// An expression may cause us to add or remove locks from the lockset, or else
/// output error messages related to missing locks.
/// FIXME: In future, we may be able to not inherit from a visitor.
class LLVM_LIBRARY_VISIBILITY BuildLockset
    : public ConstStmtVisitor<BuildLockset> {
  friend class ThreadSafetyAnalyzer;

  ThreadSafetyAnalyzer *Analyzer;
  FactSet FSet;
  // The fact set for the function on exit.
  const FactSet &FunctionExitFSet;

  /// A `LocalVariableMap::Context` wrapper that groups a context 'Q' with its
  /// immediate predecessor 'P' for a program point.  If the program point is
  /// right after a Stmt 'S', 'P' is the pre-context of 'S' and 'Q' is the
  /// post-context of 'S'.  Otherwise, 'P' == 'Q'.
  ///
  /// A DualLocalVarContext sets the global context for VarDefinition lookup to
  /// the post-context 'Q',  once CREATED or UPDATED to the next program
  /// point.  One can temporarily switch the global context to either 'P' or 'Q'
  /// using `switchToContextForScope`. The lifetime of the global context
  /// switching is bound to the enclosing scope. The global context will be set
  /// back to the prior state by the end of the scope.  This is done by the
  /// returned ContextSwitchScope object.
  ///
  /// Note: The pre- and post-context of a Stmt are distinct only in Beta mode
  /// (i.e., `Analyzer.Handler.issueBetaWarnings()`) because of the
  /// out-parameter validation.  If not in Beta mode, the global context for
  /// VarDefinition lookup is invisible, thus this wrapper has no impact on the
  /// analysis.
  class DualLocalVarContext {
  public:
    enum Point : char { Pre = 0, Post = 1 };

    class ContextSwitchScope {
      DualLocalVarContext &DC;
      Point LastPoint;

    public:
      ContextSwitchScope(DualLocalVarContext &DC, Point LastPoint)
          : DC(DC), LastPoint(LastPoint) {}
      ContextSwitchScope(const ContextSwitchScope &) = delete;
      ContextSwitchScope &operator=(const ContextSwitchScope &) = delete;
      ~ContextSwitchScope() { DC.switchContextTo(LastPoint); }
    };

    /// Temporarily switch context to \p P as long as the returned object lives.
    [[nodiscard]] ContextSwitchScope switchToContextForScope(Point P) {
      Point PriorPoint = CurrPoint;
      switchContextTo(P);
      return ContextSwitchScope(*this, PriorPoint);
    }

    /// Update the pre- and post-contexts to be associated with the next Stmt \p
    /// S. Set the global context to the post-context of \p S upon returning.
    ///
    /// If \p S is null, the behavior is as if the Stmt is a no-op--the
    /// post-context will shift to be the pre-context and the new post-context
    /// is the same as the old one, resulting in identical pre- and
    /// post-contexts.
    void moveToNextContext(const Stmt *S) {
      PrePost[Pre] = PrePost[Post];

      const LocalVariableMap::Context &NewPostCtx =
          S ? Analyzer.LocalVarMap.getNextContext(CtxIndex, S, *PrePost[Post])
            : *PrePost[Pre];

      PrePost[Post] = &NewPostCtx;
      switchContextTo(Post);
    }

    /// Constructs a DualLocalVarContext for the entry program point, where pre-
    /// and post-contexts are both equal to the \p EntryContext.
    DualLocalVarContext(ThreadSafetyAnalyzer &Analyzer, unsigned EntryIdx,
                        const LocalVariableMap::Context *EntryContext)
        : Analyzer(Analyzer), PrePost{EntryContext, EntryContext},
          CurrPoint(Post), CtxIndex(EntryIdx) {
      assert(EntryContext);
      switchContextTo(Post);
    }

  private:
    ThreadSafetyAnalyzer &Analyzer;
    // PrePost[0] points to the pre-context and
    // PrePost[1] points to the post-context:
    std::array<const LocalVariableMap::Context *, 2> PrePost;
    Point CurrPoint;
    unsigned CtxIndex;

    void switchContextTo(Point P) {
      if (!Analyzer.Handler.issueBetaWarnings())
        return;
      Analyzer.SxBuilder.setLookupLocalVarExpr(
          [Ctx = *PrePost[P],
           Analyzer = &Analyzer](const NamedDecl *D) mutable -> const Expr * {
            return Analyzer->LocalVarMap.lookupExpr(D, Ctx);
          });
      CurrPoint = P;
    }
  };

  DualLocalVarContext LVarCtx;

  // To update the context used in attr-expr translation.  If `S` is non-null,
  // the context is updated to the program point right after 'S'.
  void updateLocalVarMapCtx(const Stmt *S) { LVarCtx.moveToNextContext(S); }

  // helper functions

  void checkAccess(const Expr *Exp, AccessKind AK,
                   ProtectedOperationKind POK = POK_VarAccess) {
    Analyzer->checkAccess(FSet, Exp, AK, POK);
  }
  void checkPtAccess(const Expr *Exp, AccessKind AK,
                     ProtectedOperationKind POK = POK_VarAccess) {
    Analyzer->checkPtAccess(FSet, Exp, AK, POK);
  }

  void handleCall(const Expr *Exp, const NamedDecl *D,
                  til::SExpr *Self = nullptr,
                  SourceLocation Loc = SourceLocation());
  void examineArguments(const FunctionDecl *FD,
                        CallExpr::const_arg_iterator ArgBegin,
                        CallExpr::const_arg_iterator ArgEnd,
                        bool SkipFirstParam = false);

public:
  BuildLockset(ThreadSafetyAnalyzer *Anlzr, CFGBlockInfo &Info,
               const FactSet &FunctionExitFSet)
      : ConstStmtVisitor<BuildLockset>(), Analyzer(Anlzr), FSet(Info.EntrySet),
        FunctionExitFSet(FunctionExitFSet),
        LVarCtx(*Analyzer, Info.EntryIndex, &Info.EntryContext) {
    updateLocalVarMapCtx(nullptr);
  }

  ~BuildLockset() { Analyzer->SxBuilder.setLookupLocalVarExpr(nullptr); }
  BuildLockset(const BuildLockset &) = delete;
  BuildLockset &operator=(const BuildLockset &) = delete;

  void VisitUnaryOperator(const UnaryOperator *UO);
  void VisitBinaryOperator(const BinaryOperator *BO);
  void VisitCastExpr(const CastExpr *CE);
  void VisitCallExpr(const CallExpr *Exp);
  void VisitCXXConstructExpr(const CXXConstructExpr *Exp);
  void VisitDeclStmt(const DeclStmt *S);
  void VisitAsmStmt(const AsmStmt *S) { updateLocalVarMapCtx(S); }
  void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *Exp);
  void VisitReturnStmt(const ReturnStmt *S);
};

} // namespace threadSafety
} // namespace clang

/// Warn if the LSet does not contain a lock sufficient to protect access
/// of at least the passed in AccessKind.
void ThreadSafetyAnalyzer::warnIfMutexNotHeld(
    const FactSet &FSet, const NamedDecl *D, const Expr *Exp, AccessKind AK,
    Expr *MutexExp, ProtectedOperationKind POK, til::SExpr *Self,
    SourceLocation Loc) {
  LockKind LK = getLockKindFromAccessKind(AK);
  CapabilityExpr Cp = SxBuilder.translateAttrExpr(MutexExp, D, Exp, Self);
  if (Cp.isInvalid()) {
    warnInvalidLock(Handler, MutexExp, D, Exp, Cp.getKind());
    return;
  } else if (Cp.shouldIgnore()) {
    return;
  }

  if (Cp.negative()) {
    // Negative capabilities act like locks excluded
    const FactEntry *LDat = FSet.findLock(FactMan, !Cp);
    if (LDat) {
      Handler.handleFunExcludesLock(Cp.getKind(), D->getNameAsString(),
                                    (!Cp).toString(), Loc);
      return;
    }

    // If this does not refer to a negative capability in the same class,
    // then stop here.
    if (!inCurrentScope(Cp))
      return;

    // Otherwise the negative requirement must be propagated to the caller.
    LDat = FSet.findLock(FactMan, Cp);
    if (!LDat) {
      Handler.handleNegativeNotHeld(D, Cp.toString(), Loc);
    }
    return;
  }

  const FactEntry *LDat = FSet.findLockUniv(FactMan, Cp);
  bool NoError = true;
  if (!LDat) {
    // No exact match found.  Look for a partial match.
    LDat = FSet.findPartialMatch(FactMan, Cp);
    if (LDat) {
      // Warn that there's no precise match.
      std::string PartMatchStr = LDat->toString();
      StringRef   PartMatchName(PartMatchStr);
      Handler.handleMutexNotHeld(Cp.getKind(), D, POK, Cp.toString(), LK, Loc,
                                 &PartMatchName);
    } else {
      // Warn that there's no match at all.
      Handler.handleMutexNotHeld(Cp.getKind(), D, POK, Cp.toString(), LK, Loc);
    }
    NoError = false;
  }
  // Make sure the mutex we found is the right kind.
  if (NoError && LDat && !LDat->isAtLeast(LK)) {
    Handler.handleMutexNotHeld(Cp.getKind(), D, POK, Cp.toString(), LK, Loc);
  }
}

void ThreadSafetyAnalyzer::warnIfAnyMutexNotHeldForRead(
    const FactSet &FSet, const NamedDecl *D, const Expr *Exp,
    llvm::ArrayRef<Expr *> Args, ProtectedOperationKind POK,
    SourceLocation Loc) {
  SmallVector<CapabilityExpr, 2> Caps;
  for (auto *Arg : Args) {
    CapabilityExpr Cp = SxBuilder.translateAttrExpr(Arg, D, Exp, nullptr);
    if (Cp.isInvalid()) {
      warnInvalidLock(Handler, Arg, D, Exp, Cp.getKind());
      continue;
    }
    if (Cp.shouldIgnore())
      continue;
    const FactEntry *LDat = FSet.findLockUniv(FactMan, Cp);
    if (LDat && LDat->isAtLeast(LK_Shared))
      return; // At least one held — read access is safe.
    // FIXME: try findPartialMatch as a fallback to support
    //        -Wno-thread-safety-precise, as warnIfMutexNotHeld does.
    Caps.push_back(Cp);
  }
  if (Caps.empty())
    return;
  // Materialize names only now that we know we are going to warn.
  SmallVector<std::string, 2> NameStorage;
  SmallVector<StringRef, 2> Names;
  for (const auto &Cp : Caps) {
    NameStorage.push_back(Cp.toString());
    Names.push_back(NameStorage.back());
  }
  Handler.handleGuardedByAnyReadNotHeld(D, POK, Names, Loc);
}

/// Warn if the LSet contains the given lock.
void ThreadSafetyAnalyzer::warnIfMutexHeld(const FactSet &FSet,
                                           const NamedDecl *D, const Expr *Exp,
                                           Expr *MutexExp, til::SExpr *Self,
                                           SourceLocation Loc) {
  CapabilityExpr Cp = SxBuilder.translateAttrExpr(MutexExp, D, Exp, Self);
  if (Cp.isInvalid()) {
    warnInvalidLock(Handler, MutexExp, D, Exp, Cp.getKind());
    return;
  } else if (Cp.shouldIgnore()) {
    return;
  }

  const FactEntry *LDat = FSet.findLock(FactMan, Cp);
  if (LDat) {
    Handler.handleFunExcludesLock(Cp.getKind(), D->getNameAsString(),
                                  Cp.toString(), Loc);
  }
}

/// Checks guarded_by and pt_guarded_by attributes.
/// Whenever we identify an access (read or write) to a DeclRefExpr that is
/// marked with guarded_by, we must ensure the appropriate mutexes are held.
/// Similarly, we check if the access is to an expression that dereferences
/// a pointer marked with pt_guarded_by.
void ThreadSafetyAnalyzer::checkAccess(const FactSet &FSet, const Expr *Exp,
                                       AccessKind AK,
                                       ProtectedOperationKind POK) {
  Exp = Exp->IgnoreImplicit()->IgnoreParenCasts();

  SourceLocation Loc = Exp->getExprLoc();

  // Local variables of reference type cannot be re-assigned;
  // map them to their initializer.
  while (const auto *DRE = dyn_cast<DeclRefExpr>(Exp)) {
    const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()->getCanonicalDecl());
    if (VD && VD->isLocalVarDecl() && VD->getType()->isReferenceType()) {
      if (const auto *E = VD->getInit()) {
        // Guard against self-initialization. e.g., int &i = i;
        if (E == Exp)
          break;
        Exp = E->IgnoreImplicit()->IgnoreParenCasts();
        continue;
      }
    }
    break;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(Exp)) {
    // For dereferences
    if (UO->getOpcode() == UO_Deref)
      checkPtAccess(FSet, UO->getSubExpr(), AK, POK);
    return;
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(Exp)) {
    switch (BO->getOpcode()) {
    case BO_PtrMemD: // .*
      return checkAccess(FSet, BO->getLHS(), AK, POK);
    case BO_PtrMemI: // ->*
      return checkPtAccess(FSet, BO->getLHS(), AK, POK);
    default:
      return;
    }
  }

  if (const auto *AE = dyn_cast<ArraySubscriptExpr>(Exp)) {
    checkPtAccess(FSet, AE->getLHS(), AK, POK);
    return;
  }

  if (const auto *ME = dyn_cast<MemberExpr>(Exp)) {
    if (ME->isArrow())
      checkPtAccess(FSet, ME->getBase(), AK, POK);
    else
      checkAccess(FSet, ME->getBase(), AK, POK);
  }

  const ValueDecl *D = getValueDecl(Exp);
  if (!D || !D->hasAttrs())
    return;

  if (D->hasAttr<GuardedVarAttr>() && FSet.isEmpty(FactMan)) {
    Handler.handleNoMutexHeld(D, POK, AK, Loc);
  }

  for (const auto *I : D->specific_attrs<GuardedByAttr>()) {
    if (AK == AK_Written || I->args_size() == 1) {
      // Write requires all capabilities; single-arg read uses the normal
      // per-lock warning path.
      for (auto *Arg : I->args())
        warnIfMutexNotHeld(FSet, D, Exp, AK, Arg, POK, nullptr, Loc);
    } else {
      // Multi-arg read: holding any one of the listed capabilities is
      // sufficient (a writer must hold all, so any one prevents writes).
      warnIfAnyMutexNotHeldForRead(FSet, D, Exp, I->args(), POK, Loc);
    }
  }
}

/// Checks pt_guarded_by and pt_guarded_var attributes.
/// POK is the same  operationKind that was passed to checkAccess.
void ThreadSafetyAnalyzer::checkPtAccess(const FactSet &FSet, const Expr *Exp,
                                         AccessKind AK,
                                         ProtectedOperationKind POK) {
  // Strip off paren- and cast-expressions, checking if we encounter any other
  // operator that should be delegated to checkAccess() instead.
  while (true) {
    if (const auto *PE = dyn_cast<ParenExpr>(Exp)) {
      Exp = PE->getSubExpr();
      continue;
    }
    if (const auto *CE = dyn_cast<CastExpr>(Exp)) {
      if (CE->getCastKind() == CK_ArrayToPointerDecay) {
        // If it's an actual array, and not a pointer, then it's elements
        // are protected by GUARDED_BY, not PT_GUARDED_BY;
        checkAccess(FSet, CE->getSubExpr(), AK, POK);
        return;
      }
      Exp = CE->getSubExpr();
      continue;
    }
    break;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(Exp)) {
    if (UO->getOpcode() == UO_AddrOf) {
      // Pointer access via pointer taken of variable, so the dereferenced
      // variable is not actually a pointer.
      checkAccess(FSet, UO->getSubExpr(), AK, POK);
      return;
    }
  }

  // Pass by reference/pointer warnings are under a different flag.
  ProtectedOperationKind PtPOK = POK_VarDereference;
  switch (POK) {
  case POK_PassByRef:
    PtPOK = POK_PtPassByRef;
    break;
  case POK_ReturnByRef:
    PtPOK = POK_PtReturnByRef;
    break;
  case POK_PassPointer:
    PtPOK = POK_PtPassPointer;
    break;
  case POK_ReturnPointer:
    PtPOK = POK_PtReturnPointer;
    break;
  default:
    break;
  }

  const ValueDecl *D = getValueDecl(Exp);
  if (!D || !D->hasAttrs())
    return;

  if (D->hasAttr<PtGuardedVarAttr>() && FSet.isEmpty(FactMan))
    Handler.handleNoMutexHeld(D, PtPOK, AK, Exp->getExprLoc());

  for (auto const *I : D->specific_attrs<PtGuardedByAttr>()) {
    if (AK == AK_Written || I->args_size() == 1) {
      // Write requires all capabilities; single-arg read uses the normal
      // per-lock warning path.
      for (auto *Arg : I->args())
        warnIfMutexNotHeld(FSet, D, Exp, AK, Arg, PtPOK, nullptr,
                           Exp->getExprLoc());
    } else {
      // Multi-arg read: holding any one of the listed capabilities is
      // sufficient (a writer must hold all, so any one prevents writes).
      warnIfAnyMutexNotHeldForRead(FSet, D, Exp, I->args(), PtPOK,
                                   Exp->getExprLoc());
    }
  }
}

/// Process a function call, method call, constructor call,
/// or destructor call.  This involves looking at the attributes on the
/// corresponding function/method/constructor/destructor, issuing warnings,
/// and updating the locksets accordingly.
///
/// FIXME: For classes annotated with one of the guarded annotations, we need
/// to treat const method calls as reads and non-const method calls as writes,
/// and check that the appropriate locks are held. Non-const method calls with
/// the same signature as const method calls can be also treated as reads.
///
/// \param Exp   The call expression.
/// \param D     The callee declaration.
/// \param Self  If \p Exp = nullptr, the implicit this argument or the argument
///              of an implicitly called cleanup function.
/// \param Loc   If \p Exp = nullptr, the location.
void BuildLockset::handleCall(const Expr *Exp, const NamedDecl *D,
                              til::SExpr *Self, SourceLocation Loc) {
  // Move to the call Stmt so that both pre- and post-context are available.
  updateLocalVarMapCtx(Exp);

  // Most function attributes are associated with the pre-context. Exceptions
  // are AcquireCapability and AssertCapability, which ensure some locks are
  // held after the call, and thus are associated with the post-context. They
  // will require a temporary switch to the post-context during handling.
  //
  // Parameter attributes are restricted to scoped objects, and thus are NOT
  // context-sensitive.
  auto PreContextForThisScope =
      LVarCtx.switchToContextForScope(DualLocalVarContext::Pre);
  CapExprSet ExclusiveLocksToAdd, SharedLocksToAdd;
  CapExprSet ExclusiveLocksToRemove, SharedLocksToRemove, GenericLocksToRemove;
  CapExprSet ScopedReqsAndExcludes;

  // Figure out if we're constructing an object of scoped lockable class
  CapabilityExpr Scp;
  if (Exp) {
    assert(!Self);
    const auto *TagT = Exp->getType()->getAs<TagType>();
    if (D->hasAttrs() && TagT && Exp->isPRValue()) {
      til::LiteralPtr *Placeholder =
          Analyzer->SxBuilder.createThisPlaceholder();
      [[maybe_unused]] auto inserted =
          Analyzer->ConstructedObjects.insert({Exp, Placeholder});
      assert(inserted.second && "Are we visiting the same expression again?");
      if (isa<CXXConstructExpr>(Exp))
        Self = Placeholder;
      if (TagT->getDecl()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>())
        Scp = CapabilityExpr(Placeholder, Exp->getType(), /*Neg=*/false);
    }

    assert(Loc.isInvalid());
    Loc = Exp->getExprLoc();
  }

  for(const Attr *At : D->attrs()) {
    switch (At->getKind()) {
      // When we encounter a lock function, we need to add the lock to our
      // lockset.
      case attr::AcquireCapability: {
        auto PostContextForThisScope =
            LVarCtx.switchToContextForScope(DualLocalVarContext::Post);
        const auto *A = cast<AcquireCapabilityAttr>(At);
        Analyzer->getMutexIDs(A->isShared() ? SharedLocksToAdd
                                            : ExclusiveLocksToAdd,
                              A, Exp, D, Self);
        break;
      }

      // An assert will add a lock to the lockset, but will not generate
      // a warning if it is already there, and will not generate a warning
      // if it is not removed.
      case attr::AssertCapability: {
        auto PostContextForThisScope =
            LVarCtx.switchToContextForScope(DualLocalVarContext::Post);
        const auto *A = cast<AssertCapabilityAttr>(At);
        CapExprSet AssertLocks;
        Analyzer->getMutexIDs(AssertLocks, A, Exp, D, Self);
        for (const auto &AssertLock : AssertLocks)
          Analyzer->addLock(
              FSet, Analyzer->FactMan.createFact<LockableFactEntry>(
                        AssertLock, A->isShared() ? LK_Shared : LK_Exclusive,
                        Loc, FactEntry::Asserted));
        break;
      }

      // When we encounter an unlock function, we need to remove unlocked
      // mutexes from the lockset, and flag a warning if they are not there.
      case attr::ReleaseCapability: {
        const auto *A = cast<ReleaseCapabilityAttr>(At);
        if (A->isGeneric())
          Analyzer->getMutexIDs(GenericLocksToRemove, A, Exp, D, Self);
        else if (A->isShared())
          Analyzer->getMutexIDs(SharedLocksToRemove, A, Exp, D, Self);
        else
          Analyzer->getMutexIDs(ExclusiveLocksToRemove, A, Exp, D, Self);
        break;
      }

      case attr::RequiresCapability: {
        const auto *A = cast<RequiresCapabilityAttr>(At);
        for (auto *Arg : A->args()) {
          Analyzer->warnIfMutexNotHeld(FSet, D, Exp,
                                       A->isShared() ? AK_Read : AK_Written,
                                       Arg, POK_FunctionCall, Self, Loc);
          // use for adopting a lock
          if (!Scp.shouldIgnore())
            Analyzer->getMutexIDs(ScopedReqsAndExcludes, A, Exp, D, Self);
        }
        break;
      }

      case attr::LocksExcluded: {
        const auto *A = cast<LocksExcludedAttr>(At);
        for (auto *Arg : A->args()) {
          Analyzer->warnIfMutexHeld(FSet, D, Exp, Arg, Self, Loc);
          // use for deferring a lock
          if (!Scp.shouldIgnore())
            Analyzer->getMutexIDs(ScopedReqsAndExcludes, A, Exp, D, Self);
        }
        break;
      }

      // Ignore attributes unrelated to thread-safety
      default:
        break;
    }
  }

  std::optional<CallExpr::const_arg_range> Args;
  if (Exp) {
    if (const auto *CE = dyn_cast<CallExpr>(Exp))
      Args = CE->arguments();
    else if (const auto *CE = dyn_cast<CXXConstructExpr>(Exp))
      Args = CE->arguments();
    else
      llvm_unreachable("Unknown call kind");
  }
  const auto *CalledFunction = dyn_cast<FunctionDecl>(D);
  if (CalledFunction && Args.has_value()) {
    for (auto [Param, Arg] : zip(CalledFunction->parameters(), *Args)) {
      if (isCallbackParam(Param))
        continue;
      CapExprSet DeclaredLocks;
      for (const Attr *At : Param->attrs()) {
        switch (At->getKind()) {
        case attr::AcquireCapability: {
          const auto *A = cast<AcquireCapabilityAttr>(At);
          Analyzer->getMutexIDs(A->isShared() ? SharedLocksToAdd
                                              : ExclusiveLocksToAdd,
                                A, Exp, D, Self);
          Analyzer->getMutexIDs(DeclaredLocks, A, Exp, D, Self);
          break;
        }

        case attr::ReleaseCapability: {
          const auto *A = cast<ReleaseCapabilityAttr>(At);
          if (A->isGeneric())
            Analyzer->getMutexIDs(GenericLocksToRemove, A, Exp, D, Self);
          else if (A->isShared())
            Analyzer->getMutexIDs(SharedLocksToRemove, A, Exp, D, Self);
          else
            Analyzer->getMutexIDs(ExclusiveLocksToRemove, A, Exp, D, Self);
          Analyzer->getMutexIDs(DeclaredLocks, A, Exp, D, Self);
          break;
        }

        case attr::RequiresCapability: {
          const auto *A = cast<RequiresCapabilityAttr>(At);
          for (auto *Arg : A->args())
            Analyzer->warnIfMutexNotHeld(FSet, D, Exp,
                                         A->isShared() ? AK_Read : AK_Written,
                                         Arg, POK_FunctionCall, Self, Loc);
          Analyzer->getMutexIDs(DeclaredLocks, A, Exp, D, Self);
          break;
        }

        case attr::LocksExcluded: {
          const auto *A = cast<LocksExcludedAttr>(At);
          for (auto *Arg : A->args())
            Analyzer->warnIfMutexHeld(FSet, D, Exp, Arg, Self, Loc);
          Analyzer->getMutexIDs(DeclaredLocks, A, Exp, D, Self);
          break;
        }

        default:
          break;
        }
      }
      if (DeclaredLocks.empty())
        continue;
      CapabilityExpr Cp(Analyzer->SxBuilder.translate(Arg, nullptr),
                        StringRef("mutex"), /*Neg=*/false, /*Reentrant=*/false);
      if (const auto *CBTE = dyn_cast<CXXBindTemporaryExpr>(Arg->IgnoreCasts());
          Cp.isInvalid() && CBTE) {
        if (auto Object = Analyzer->ConstructedObjects.find(CBTE->getSubExpr());
            Object != Analyzer->ConstructedObjects.end())
          Cp = CapabilityExpr(Object->second, StringRef("mutex"), /*Neg=*/false,
                              /*Reentrant=*/false);
      }
      const FactEntry *Fact = FSet.findLock(Analyzer->FactMan, Cp);
      if (!Fact) {
        Analyzer->Handler.handleMutexNotHeld(Cp.getKind(), D, POK_FunctionCall,
                                             Cp.toString(), LK_Exclusive,
                                             Exp->getExprLoc());
        continue;
      }
      // The argument may be a capability that is not a scoped object, e.g. if
      // its class is both scoped_lockable and a capability or if its class is
      // derived from a scoped_lockable class. There are no underlying mutexes
      // to compare with in that case.
      const auto *Scope = dyn_cast<ScopedLockableFactEntry>(Fact);
      if (!Scope)
        continue;
      for (const auto &[a, b] :
           zip_longest(DeclaredLocks, Scope->getUnderlyingMutexes())) {
        if (!a.has_value()) {
          Analyzer->Handler.handleExpectFewerUnderlyingMutexes(
              Exp->getExprLoc(), D->getLocation(), Scope->toString(),
              b.value().getKind(), b.value().toString());
        } else if (!b.has_value()) {
          Analyzer->Handler.handleExpectMoreUnderlyingMutexes(
              Exp->getExprLoc(), D->getLocation(), Scope->toString(),
              a.value().getKind(), a.value().toString());
        } else if (!a.value().equals(b.value())) {
          Analyzer->Handler.handleUnmatchedUnderlyingMutexes(
              Exp->getExprLoc(), D->getLocation(), Scope->toString(),
              a.value().getKind(), a.value().toString(), b.value().toString());
          break;
        }
      }
    }
  }
  // Remove locks first to allow lock upgrading/downgrading.
  // FIXME -- should only fully remove if the attribute refers to 'this'.
  bool Dtor = isa<CXXDestructorDecl>(D);
  for (const auto &M : ExclusiveLocksToRemove)
    Analyzer->removeLock(FSet, M, Loc, Dtor, LK_Exclusive);
  for (const auto &M : SharedLocksToRemove)
    Analyzer->removeLock(FSet, M, Loc, Dtor, LK_Shared);
  for (const auto &M : GenericLocksToRemove)
    Analyzer->removeLock(FSet, M, Loc, Dtor, LK_Generic);

  // Add locks.
  FactEntry::SourceKind Source =
      !Scp.shouldIgnore() ? FactEntry::Managed : FactEntry::Acquired;
  for (const auto &M : ExclusiveLocksToAdd)
    Analyzer->addLock(FSet, Analyzer->FactMan.createFact<LockableFactEntry>(
                                M, LK_Exclusive, Loc, Source));
  for (const auto &M : SharedLocksToAdd)
    Analyzer->addLock(FSet, Analyzer->FactMan.createFact<LockableFactEntry>(
                                M, LK_Shared, Loc, Source));

  if (!Scp.shouldIgnore()) {
    // Add the managing object as a dummy mutex, mapped to the underlying mutex.
    auto *ScopedEntry = Analyzer->FactMan.createFact<ScopedLockableFactEntry>(
        Scp, Loc, FactEntry::Acquired,
        ExclusiveLocksToAdd.size() + SharedLocksToAdd.size() +
            ScopedReqsAndExcludes.size() + ExclusiveLocksToRemove.size() +
            SharedLocksToRemove.size());
    for (const auto &M : ExclusiveLocksToAdd)
      ScopedEntry->addLock(M);
    for (const auto &M : SharedLocksToAdd)
      ScopedEntry->addLock(M);
    for (const auto &M : ScopedReqsAndExcludes)
      ScopedEntry->addLock(M);
    for (const auto &M : ExclusiveLocksToRemove)
      ScopedEntry->addExclusiveUnlock(M);
    for (const auto &M : SharedLocksToRemove)
      ScopedEntry->addSharedUnlock(M);
    Analyzer->addLock(FSet, ScopedEntry);
  }
}

/// For unary operations which read and write a variable, we need to
/// check whether we hold any required mutexes. Reads are checked in
/// VisitCastExpr.
void BuildLockset::VisitUnaryOperator(const UnaryOperator *UO) {
  switch (UO->getOpcode()) {
    case UO_PostDec:
    case UO_PostInc:
    case UO_PreDec:
    case UO_PreInc:
      checkAccess(UO->getSubExpr(), AK_Written);
      updateLocalVarMapCtx(UO);
      break;
    default:
      break;
  }
}

/// For binary operations which assign to a variable (writes), we need to check
/// whether we hold any required mutexes.
/// FIXME: Deal with non-primitive types.
void BuildLockset::VisitBinaryOperator(const BinaryOperator *BO) {
  if (!BO->isAssignmentOp())
    return;
  checkAccess(BO->getLHS(), AK_Written);
  updateLocalVarMapCtx(BO);
}

/// Whenever we do an LValue to Rvalue cast, we are reading a variable and
/// need to ensure we hold any required mutexes.
/// FIXME: Deal with non-primitive types.
void BuildLockset::VisitCastExpr(const CastExpr *CE) {
  if (CE->getCastKind() != CK_LValueToRValue)
    return;
  checkAccess(CE->getSubExpr(), AK_Read);
}

void BuildLockset::examineArguments(const FunctionDecl *FD,
                                    CallExpr::const_arg_iterator ArgBegin,
                                    CallExpr::const_arg_iterator ArgEnd,
                                    bool SkipFirstParam) {
  // Currently we can't do anything if we don't know the function declaration.
  if (!FD)
    return;

  // NO_THREAD_SAFETY_ANALYSIS does double duty here.  Normally it
  // only turns off checking within the body of a function, but we also
  // use it to turn off checking in arguments to the function.  This
  // could result in some false negatives, but the alternative is to
  // create yet another attribute.
  if (FD->hasAttr<NoThreadSafetyAnalysisAttr>())
    return;

  const ArrayRef<ParmVarDecl *> Params = FD->parameters();
  auto Param = Params.begin();
  if (SkipFirstParam)
    ++Param;

  // There can be default arguments, so we stop when one iterator is at end().
  for (auto Arg = ArgBegin; Param != Params.end() && Arg != ArgEnd;
       ++Param, ++Arg) {
    QualType Qt = (*Param)->getType();
    if (Qt->isReferenceType())
      checkAccess(*Arg, AK_Read, POK_PassByRef);
    else if (Qt->isPointerType())
      checkPtAccess(*Arg, AK_Read, POK_PassPointer);
  }
}

void BuildLockset::VisitCallExpr(const CallExpr *Exp) {
  if (const auto *CE = dyn_cast<CXXMemberCallExpr>(Exp)) {
    const auto *ME = dyn_cast<MemberExpr>(CE->getCallee());
    // ME can be null when calling a method pointer
    const CXXMethodDecl *MD = CE->getMethodDecl();

    if (ME && MD) {
      if (ME->isArrow()) {
        // Should perhaps be AK_Written if !MD->isConst().
        checkPtAccess(CE->getImplicitObjectArgument(), AK_Read);
      } else {
        // Should perhaps be AK_Written if !MD->isConst().
        checkAccess(CE->getImplicitObjectArgument(), AK_Read);
      }
    }

    examineArguments(CE->getDirectCallee(), CE->arg_begin(), CE->arg_end());
  } else if (const auto *OE = dyn_cast<CXXOperatorCallExpr>(Exp)) {
    OverloadedOperatorKind OEop = OE->getOperator();
    switch (OEop) {
      case OO_Equal:
      case OO_PlusEqual:
      case OO_MinusEqual:
      case OO_StarEqual:
      case OO_SlashEqual:
      case OO_PercentEqual:
      case OO_CaretEqual:
      case OO_AmpEqual:
      case OO_PipeEqual:
      case OO_LessLessEqual:
      case OO_GreaterGreaterEqual:
        checkAccess(OE->getArg(1), AK_Read);
        [[fallthrough]];
      case OO_PlusPlus:
      case OO_MinusMinus:
        checkAccess(OE->getArg(0), AK_Written);
        break;
      case OO_Star:
      case OO_ArrowStar:
      case OO_Arrow:
      case OO_Subscript:
        if (!(OEop == OO_Star && OE->getNumArgs() > 1)) {
          // Grrr.  operator* can be multiplication...
          checkPtAccess(OE->getArg(0), AK_Read);
        }
        [[fallthrough]];
      default: {
        // TODO: get rid of this, and rely on pass-by-ref instead.
        const Expr *Obj = OE->getArg(0);
        checkAccess(Obj, AK_Read);
        // Check the remaining arguments. For method operators, the first
        // argument is the implicit self argument, and doesn't appear in the
        // FunctionDecl, but for non-methods it does.
        const FunctionDecl *FD = OE->getDirectCallee();
        examineArguments(FD, std::next(OE->arg_begin()), OE->arg_end(),
                         /*SkipFirstParam*/ !isa<CXXMethodDecl>(FD));
        break;
      }
    }
  } else {
    examineArguments(Exp->getDirectCallee(), Exp->arg_begin(), Exp->arg_end());
  }

  auto *D = dyn_cast_or_null<NamedDecl>(Exp->getCalleeDecl());

  if (D)
    handleCall(Exp, D);
  else
    // Even if we cannot handle the call, we need to update the context for the
    // Stmt:
    updateLocalVarMapCtx(Exp);
}

void BuildLockset::VisitCXXConstructExpr(const CXXConstructExpr *Exp) {
  const CXXConstructorDecl *D = Exp->getConstructor();
  if (D && D->isCopyConstructor()) {
    const Expr* Source = Exp->getArg(0);
    checkAccess(Source, AK_Read);
  } else {
    examineArguments(D, Exp->arg_begin(), Exp->arg_end());
  }
  if (D && D->hasAttrs())
    handleCall(Exp, D);
  else
    updateLocalVarMapCtx(Exp);
}

const Expr *threadSafety::unpackConstruction(const Expr *E) {
  if (auto *CE = dyn_cast<CastExpr>(E))
    if (CE->getCastKind() == CK_NoOp)
      E = CE->getSubExpr()->IgnoreParens();
  if (auto *CE = dyn_cast<CastExpr>(E))
    if (CE->getCastKind() == CK_ConstructorConversion ||
        CE->getCastKind() == CK_UserDefinedConversion)
      E = CE->getSubExpr();
  if (auto *BTE = dyn_cast<CXXBindTemporaryExpr>(E))
    E = BTE->getSubExpr();
  return E;
}

void BuildLockset::VisitDeclStmt(const DeclStmt *S) {
  for (auto *D : S->getDeclGroup()) {
    if (auto *VD = dyn_cast_or_null<VarDecl>(D)) {
      const Expr *E = VD->getInit();
      if (!E)
        continue;
      E = E->IgnoreParens();

      // handle constructors that involve temporaries
      if (auto *EWC = dyn_cast<ExprWithCleanups>(E))
        E = EWC->getSubExpr()->IgnoreParens();
      E = unpackConstruction(E);

      if (auto Object = Analyzer->ConstructedObjects.find(E);
          Object != Analyzer->ConstructedObjects.end()) {
        Object->second->setClangDecl(VD);
        Analyzer->ConstructedObjects.erase(Object);
      }
    }
  }
  updateLocalVarMapCtx(S);
}

void BuildLockset::VisitMaterializeTemporaryExpr(
    const MaterializeTemporaryExpr *Exp) {
  if (const ValueDecl *ExtD = Exp->getExtendingDecl()) {
    if (auto Object = Analyzer->ConstructedObjects.find(
            unpackConstruction(Exp->getSubExpr()));
        Object != Analyzer->ConstructedObjects.end()) {
      Object->second->setClangDecl(ExtD);
      Analyzer->ConstructedObjects.erase(Object);
    }
  }
}

void BuildLockset::VisitReturnStmt(const ReturnStmt *S) {
  if (Analyzer->CurrentFunction == nullptr)
    return;
  const Expr *RetVal = S->getRetValue();
  if (!RetVal)
    return;

  // If returning by reference or pointer, check that the function requires the
  // appropriate capabilities.
  const QualType ReturnType =
      Analyzer->CurrentFunction->getReturnType().getCanonicalType();
  if (ReturnType->isLValueReferenceType()) {
    Analyzer->checkAccess(
        FunctionExitFSet, RetVal,
        ReturnType->getPointeeType().isConstQualified() ? AK_Read : AK_Written,
        POK_ReturnByRef);
  } else if (ReturnType->isPointerType()) {
    Analyzer->checkPtAccess(
        FunctionExitFSet, RetVal,
        ReturnType->getPointeeType().isConstQualified() ? AK_Read : AK_Written,
        POK_ReturnPointer);
  }
}

/// Given two facts merging on a join point, possibly warn and decide whether to
/// keep or replace.
///
/// \return  false if we should keep \p A, true if we should take \p B.
bool ThreadSafetyAnalyzer::join(const FactEntry &A, const FactEntry &B,
                                SourceLocation JoinLoc,
                                LockErrorKind EntryLEK) {
  // Whether we can replace \p A by \p B.
  const bool CanModify = EntryLEK != LEK_LockedSomeLoopIterations;
  unsigned int ReentrancyDepthA = 0;
  unsigned int ReentrancyDepthB = 0;

  if (const auto *LFE = dyn_cast<LockableFactEntry>(&A))
    ReentrancyDepthA = LFE->getReentrancyDepth();
  if (const auto *LFE = dyn_cast<LockableFactEntry>(&B))
    ReentrancyDepthB = LFE->getReentrancyDepth();

  if (ReentrancyDepthA != ReentrancyDepthB) {
    Handler.handleMutexHeldEndOfScope(B.getKind(), B.toString(), B.loc(),
                                      JoinLoc, EntryLEK,
                                      /*ReentrancyMismatch=*/true);
    // Pick the FactEntry with the greater reentrancy depth as the "good"
    // fact to reduce potential later warnings.
    return CanModify && ReentrancyDepthA < ReentrancyDepthB;
  } else if (A.kind() != B.kind()) {
    // For managed capabilities, the destructor should unlock in the right mode
    // anyway. For asserted capabilities no unlocking is needed.
    if ((A.managed() || A.asserted()) && (B.managed() || B.asserted())) {
      // The shared capability subsumes the exclusive capability, if possible.
      bool ShouldTakeB = B.kind() == LK_Shared;
      if (CanModify || !ShouldTakeB)
        return ShouldTakeB;
    }
    Handler.handleExclusiveAndShared(B.getKind(), B.toString(), B.loc(),
                                     A.loc());
    // Take the exclusive capability to reduce further warnings.
    return CanModify && B.kind() == LK_Exclusive;
  } else {
    // The non-asserted capability is the one we want to track.
    return CanModify && A.asserted() && !B.asserted();
  }
}

/// Compute the intersection of two locksets and issue warnings for any
/// locks in the symmetric difference.
///
/// This function is used at a merge point in the CFG when comparing the lockset
/// of each branch being merged. For example, given the following sequence:
/// A; if () then B; else C; D; we need to check that the lockset after B and C
/// are the same. In the event of a difference, we use the intersection of these
/// two locksets at the start of D.
///
/// \param EntrySet A lockset for entry into a (possibly new) block.
/// \param ExitSet The lockset on exiting a preceding block.
/// \param JoinLoc The location of the join point for error reporting
/// \param EntryLEK The warning if a mutex is missing from \p EntrySet.
/// \param ExitLEK The warning if a mutex is missing from \p ExitSet.
/// \param TrylockRebranchCaps Capabilities acquired by a try-lock whose result
/// the joining block's terminator branches on; differences in these are not
/// diagnosed because the paths re-diverge at the terminator (but they are
/// still removed from the intersection, and conditionally re-added on the
/// outgoing edges by getEdgeLockset()).
void ThreadSafetyAnalyzer::intersectAndWarn(
    FactSet &EntrySet, const FactSet &ExitSet, SourceLocation JoinLoc,
    LockErrorKind EntryLEK, LockErrorKind ExitLEK,
    const CapExprSet *TrylockRebranchCaps) {
  FactSet EntrySetOrig = EntrySet;

  auto IsTrylockRebranched = [TrylockRebranchCaps](const FactEntry &FE) {
    return TrylockRebranchCaps &&
           llvm::any_of(*TrylockRebranchCaps, [&FE](const CapabilityExpr &CE) {
             return !CE.shouldIgnore() && FE.matches(CE);
           });
  };

  // Find locks in ExitSet that conflict or are not in EntrySet, and warn.
  for (const auto &Fact : ExitSet) {
    const FactEntry &ExitFact = FactMan[Fact];

    FactSet::iterator EntryIt = EntrySet.findLockIter(FactMan, ExitFact);
    if (EntryIt != EntrySet.end()) {
      const FactEntry &EntryFact = FactMan[*EntryIt];
      if (IsTrylockRebranched(ExitFact) &&
          EntryLEK == LEK_LockedSomePredecessors &&
          EntryFact.loc() == ExitFact.loc() && !EntryFact.managed() &&
          !ExitFact.managed() &&
          getFactReentrancyDepth(EntryFact) ==
              getFactReentrancyDepth(ExitFact)) {
        // Both facts have been created by the same trylock call, whose result
        // is checked again by the terminator of this block. The lock kind may
        // differ if the trylock function has range attributes for different
        // lock kinds. Keep the shared fact; the edges out of this block
        // refine the lock kind.
        if (preferJoinedFact(EntryFact, ExitFact))
          *EntryIt = Fact;
      } else if (join(EntryFact, ExitFact, JoinLoc, EntryLEK)) {
        *EntryIt = Fact;
      }
    } else if ((!ExitFact.managed() || EntryLEK == LEK_LockedAtEndOfFunction) &&
               !IsTrylockRebranched(ExitFact)) {
      ExitFact.handleRemovalFromIntersection(ExitSet, FactMan, JoinLoc,
                                             EntryLEK, Handler);
    }
  }

  // Find locks in EntrySet that are not in ExitSet, and remove them.
  for (const auto &Fact : EntrySetOrig) {
    const FactEntry *EntryFact = &FactMan[Fact];
    const FactEntry *ExitFact = ExitSet.findLock(FactMan, *EntryFact);

    if (!ExitFact) {
      if ((!EntryFact->managed() || ExitLEK == LEK_LockedSomeLoopIterations ||
           ExitLEK == LEK_NotLockedAtEndOfFunction) &&
          !IsTrylockRebranched(*EntryFact))
        EntryFact->handleRemovalFromIntersection(EntrySetOrig, FactMan, JoinLoc,
                                                 ExitLEK, Handler);
      if (ExitLEK == LEK_LockedSomePredecessors)
        EntrySet.removeLock(FactMan, *EntryFact);
    }
  }
}

// Return true if block B never continues to its successors.
bool threadSafety::neverReturns(const CFGBlock *B) {
  if (B->hasNoReturnElement())
    return true;
  if (B->empty())
    return false;

  CFGElement Last = B->back();
  if (std::optional<CFGStmt> S = Last.getAs<CFGStmt>()) {
    if (isa<CXXThrowExpr>(S->getStmt()))
      return true;
  }

  // If B constructed a temporary whose destructor is noreturn, control entering
  // the decision block will always branch to the non-returning destructor.
  if (B->succ_size() == 1) {
    if (const CFGBlock *Succ = *B->succ_begin()) {
      if (Succ->getTerminator().isTemporaryDtorsBranch() &&
          Succ->succ_size() == 2) {
        // The decision block's terminator is the CXXBindTemporaryExpr; if B
        // bound this temporary, entering Succ from B takes the true (dtor)
        // edge; otherwise it takes the false (alternative dtor / continuation)
        // edge.
        const Stmt *Term = Succ->getTerminatorStmt();
        bool Bound = llvm::any_of(*B, [Term](const CFGElement &CE) {
          auto CS = CE.getAs<CFGStmt>();
          return CS && CS->getStmt() == Term;
        });
        if (const auto *Next =
                (Bound ? *Succ->succ_begin() : *(Succ->succ_begin() + 1))
                    .getReachableBlock())
          return neverReturns(Next);
      }
    }
  }

  return false;
}

/// Collect the subtrees of unevaluated expressions of \p CFGraph in
/// UnevaluatedStmts and set HasTrylockCall.
void ThreadSafetyAnalyzer::collectUnevaluatedStmts(CFG *CFGraph) {
  auto AddUnevaluatedSubtree = [&](const Stmt *Root) {
    if (!Root)
      return;
    SmallVector<const Stmt *, 16> Worklist = {Root};
    while (!Worklist.empty()) {
      const Stmt *S = Worklist.pop_back_val();
      if (!S || !UnevaluatedStmts.insert(S).second)
        continue;
      if (const auto *DS = dyn_cast<DeclStmt>(S)) {
        for (const Decl *D : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(D))
            UnevaluatedVarDecls.insert(VD);
        forEachDeclVLAExpr(DS, /*IncludeTopLevelVLA=*/true,
                           [&](const Expr *Sz) { Worklist.push_back(Sz); });
      }
      llvm::append_range(Worklist, S->children());
    }
  };
  SmallVector<const CallExpr *, 4> TrylockCalls;
  for (const CFGBlock *B : *CFGraph) {
    for (const CFGElement &BI : *B) {
      std::optional<CFGStmt> CS = BI.getAs<CFGStmt>();
      if (!CS)
        continue;
      const Stmt *S = CS->getStmt();
      if (UnevaluatedStmts.contains(S))
        continue;
      if (const auto *CE = dyn_cast<CallExpr>(S)) {
        if (CE->isUnevaluatedBuiltinCall(*ASTCtx)) {
          for (const Expr *Arg : CE->arguments())
            AddUnevaluatedSubtree(Arg);
        } else if (getTrylockCallee(CE)) {
          TrylockCalls.push_back(CE);
        }
        continue;
      }
      // Neither assignments nor dereferences in unevaluated operands have
      // any effect at runtime.
      if (const auto *NE = dyn_cast<CXXNoexceptExpr>(S)) {
        AddUnevaluatedSubtree(NE->getOperand());
      } else if (const auto *GSE = dyn_cast<GenericSelectionExpr>(S)) {
        if (GSE->isExprPredicate())
          AddUnevaluatedSubtree(GSE->getControllingExpr());
        if (!GSE->isResultDependent()) {
          const Expr *ResultE = GSE->getResultExpr();
          for (const Expr *AssocE : GSE->getAssocExprs())
            if (AssocE != ResultE)
              AddUnevaluatedSubtree(AssocE);
        }
      } else if (const auto *TE = dyn_cast<UnaryExprOrTypeTraitExpr>(S)) {
        if (!isEvaluatedUnaryExprOrTypeTrait(TE))
          for (const Stmt *Child : TE->children())
            AddUnevaluatedSubtree(Child);
      } else if (const auto *TE = dyn_cast<CXXTypeidExpr>(S)) {
        if (!TE->isTypeOperand() && !TE->isPotentiallyEvaluated())
          AddUnevaluatedSubtree(TE->getExprOperand());
      }
    }
  }
  // The CFG contains a synthetic DeclStmt for each variable of a DeclStmt
  // that declares more than one variable. Treat these like their source.
  for (const auto &[Synthetic, Source] : CFGraph->synthetic_stmts())
    if (UnevaluatedStmts.contains(Source))
      UnevaluatedStmts.insert(Synthetic);
  HasTrylockCall = llvm::any_of(TrylockCalls, [&](const CallExpr *CE) {
    return !UnevaluatedStmts.contains(CE);
  });
}

/// Record the local variables that may be modified through an alias in
/// LocalVarMap.
void ThreadSafetyAnalyzer::markEscapedLocalVars(AnalysisDeclContext &AC) {
  llvm::SmallPtrSet<const ValueDecl *, 16> EscapedVars;
  llvm::SmallPtrSet<const ValueDecl *, 16> ModifiedVars;
  scanTrylockVars(AC.getBody(), *ASTCtx, EscapedVars, ModifiedVars);
  for (const ValueDecl *VD : EscapedVars)
    LocalVarMap.addEscapedVar(VD);
}

/// Join the pending trylock ranges on the edges into a block, one element of
/// \p PredEdgePendings per edge, into \p EntryPending, the pending trylock
/// ranges at the entry of the block. \p HasUnvisitedPred is whether the block
/// has a predecessor that has not been visited yet. An edge without an entry
/// for a call that has an entry on another edge is treated as an edge on
/// which the call may have returned any value and on which no capabilities
/// have been acquired or released by branching on its result.
void ThreadSafetyAnalyzer::joinPendingTrylockRanges(
    ArrayRef<PendingTrylockRanges> PredEdgePendings, bool HasUnvisitedPred,
    PendingTrylockRanges &EntryPending) {
  using AttrValueMap = PendingTrylockRange::AttrValueMap;
  auto MergeAttrMap = [](AttrValueMap &Dst, const AttrValueMap &Src,
                         std::optional<IntRangeSet> Full) {
    for (const auto &[A, Values] : Src) {
      if (Full)
        Dst[A] = *Full;
      else if (auto [It, Ins] = Dst.try_emplace(A, Values); !Ins)
        It->second = It->second.unionWith(Values);
    }
  };
  for (const PendingTrylockRanges &Edge : PredEdgePendings) {
    for (const PendingTrylockRange &Q : Edge) {
      if (llvm::any_of(EntryPending, [&](const PendingTrylockRange &P) {
            return P.Call == Q.Call;
          }))
        continue;
      IntRangeSet FullDom = IntRangeSet::full(Q.Dom);
      IntRangeSet JoinedValues = HasUnvisitedPred ? FullDom : IntRangeSet{};
      AttrValueMap JoinedAcquired, JoinedConsumed;
      for (const PendingTrylockRanges &OtherEdge : PredEdgePendings) {
        auto It =
            llvm::find_if(OtherEdge, [&](const PendingTrylockRange &OtherQ) {
              return OtherQ.Call == Q.Call;
            });
        if (It == OtherEdge.end()) {
          JoinedValues = FullDom;
          continue;
        }
        bool SameDom = It->Dom == Q.Dom;
        JoinedValues = SameDom ? JoinedValues.unionWith(It->Values) : FullDom;
        MergeAttrMap(JoinedAcquired, It->AcquiredAttrs,
                     (!SameDom || HasUnvisitedPred)
                         ? std::optional<IntRangeSet>(FullDom)
                         : std::nullopt);
        MergeAttrMap(JoinedConsumed, It->ConsumedValues,
                     !SameDom ? std::optional<IntRangeSet>(FullDom)
                              : std::nullopt);
      }
      JoinedValues.widen(MaxStateRangeIntervals);
      for (auto *Map : {&JoinedAcquired, &JoinedConsumed})
        for (auto &[A, Values] : *Map)
          Values.widen(MaxStateRangeIntervals);
      if (JoinedAcquired.empty() && JoinedConsumed.empty() &&
          JoinedValues.complement(Q.Dom).empty())
        continue;
      EntryPending.push_back({Q.Call, Q.CallCtx, Q.Dom, std::move(JoinedValues),
                              std::move(JoinedAcquired),
                              std::move(JoinedConsumed)});
    }
  }
}

/// Remove the attributes whose capabilities are not held at the entry of the
/// block \p CurrBlockInfo from the acquired attributes of \p EntryPending.
/// The capabilities of the remaining attributes are held on every path into
/// the block, whatever value the call returned.
void ThreadSafetyAnalyzer::dropUnheldPendingAcquires(
    PendingTrylockRanges &EntryPending, const CFGBlockInfo *CurrBlockInfo) {
  for (PendingTrylockRange &P : EntryPending) {
    const auto *Callee = dyn_cast_or_null<NamedDecl>(P.Call->getCalleeDecl());
    if (!Callee) {
      P.AcquiredAttrs.clear();
      continue;
    }
    LocalVarLookupScope Lookup(*this, P.CallCtx);
    P.AcquiredAttrs.remove_if([&](const auto &KV) {
      const Attr *A = KV.getFirst();
      CapExprSet Caps;
      getTrylockMutexIDs(Caps, A, P.Call, Callee);
      bool Shared = isSharedTrylockAttr(A);
      return !llvm::all_of(Caps, [&](const CapabilityExpr &Cap) {
        if (Cap.shouldIgnore())
          return true;
        const FactEntry *FE = CurrBlockInfo->EntrySet.findLock(FactMan, Cap);
        return FE && !FE->negative() && (Shared || FE->kind() == LK_Exclusive);
      });
    });
    for (auto &[A, Values] : P.AcquiredAttrs)
      Values = Values.unionWith(P.Values);
  }
}

/// Update the pending trylock ranges \p EntryPending at the entry of
/// \p CurrBlock with the effects of the block, such that these become the
/// pending trylock ranges at its exit.
void ThreadSafetyAnalyzer::updatePendingTrylockRanges(
    PendingTrylockRanges &EntryPending, const CFGBlock *CurrBlock,
    const CFGBlockInfo *CurrBlockInfo) {
  // A call that is executed again in this block returns a new value.
  for (const CFGElement &BI : *CurrBlock) {
    if (EntryPending.empty())
      return;
    if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>())
      llvm::erase_if(EntryPending, [&](const PendingTrylockRange &P) {
        return P.Call == CS->getStmt();
      });
  }
  bool AnyLockRemoved = llvm::any_of(CurrBlockInfo->EntrySet, [&](FactID ID) {
    const FactEntry &FE = FactMan[ID];
    return !FE.negative() && !CurrBlockInfo->ExitSet.findLock(FactMan, FE);
  });
  if (!AnyLockRemoved)
    return;
  for (PendingTrylockRange &P : EntryPending) {
    const auto *Callee = dyn_cast_or_null<NamedDecl>(P.Call->getCalleeDecl());
    if (!Callee)
      continue;
    LocalVarLookupScope Lookup(*this, P.CallCtx);
    // Record the values for which the capabilities of an attribute have
    // been released, such that branching on the result of the call again
    // does not acquire them again for these values.
    P.AcquiredAttrs.remove_if([&](const auto &KV) {
      const Attr *A = KV.getFirst();
      CapExprSet Caps;
      getTrylockMutexIDs(Caps, A, P.Call, Callee);
      if (llvm::none_of(Caps, [&](const CapabilityExpr &Cap) {
            return CurrBlockInfo->EntrySet.findLock(FactMan, Cap) &&
                   !CurrBlockInfo->ExitSet.findLock(FactMan, Cap);
          }))
        return false;
      IntRangeSet &Consumed = P.ConsumedValues[A];
      Consumed = Consumed.unionWith(KV.getSecond());
      return true;
    });
  }
}

/// Check a function's CFG for thread-safety violations.
///
/// We traverse the blocks in the CFG, compute the set of mutexes that are held
/// at the end of each block, and issue warnings for thread safety violations.
/// Each block in the CFG is traversed exactly once.
void ThreadSafetyAnalyzer::runAnalysis(AnalysisDeclContext &AC) {
  // TODO: this whole function needs be rewritten as a visitor for CFGWalker.
  // For now, we just use the walker to set things up.
  threadSafety::CFGWalker walker;
  if (!walker.init(AC))
    return;

  // AC.dumpCFG(true);
  // threadSafety::printSCFG(walker);

  CFG *CFGraph = walker.getGraph();
  const NamedDecl *D = walker.getDecl();
  ASTCtx = &AC.getASTContext();
  CurrentFunction = dyn_cast<FunctionDecl>(D);

  if (D->hasAttr<NoThreadSafetyAnalysisAttr>())
    return;

  // FIXME: Do something a bit more intelligent inside constructor and
  // destructor code.  Constructors and destructors must assume unique access
  // to 'this', so checks on member variable access is disabled, but we should
  // still enable checks on other objects.
  if (isa<CXXConstructorDecl>(D))
    return;  // Don't check inside constructors.
  if (isa<CXXDestructorDecl>(D))
    return;  // Don't check inside destructors.

  Handler.enterFunction(CurrentFunction);
  llvm::scope_exit LeaveFunc([&]() { Handler.leaveFunction(CurrentFunction); });

  BlockInfo.resize(CFGraph->getNumBlockIDs(),
    CFGBlockInfo::getEmptyBlockInfo(LocalVarMap));

  // We need to explore the CFG via a "topological" ordering.
  // That way, we will be guaranteed to have information about required
  // predecessor locksets when exploring a new block.
  const PostOrderCFGView *SortedGraph = walker.getSortedGraph();
  PostOrderCFGView::CFGBlockSet VisitedBlocks(CFGraph);

  CFGBlockInfo &Initial = BlockInfo[CFGraph->getEntry().getBlockID()];
  CFGBlockInfo &Final   = BlockInfo[CFGraph->getExit().getBlockID()];

  // Mark entry block as reachable
  Initial.Reachable = true;

  // Identify subtrees of unevaluated expressions (which CFGBuilder may still
  // emit as CFG elements when AlwaysAdd is set) and check whether any
  // evaluated call targets a trylock function.
  collectUnevaluatedStmts(CFGraph);

  // Compute SSA names for local variables. When trylocks are involved, record
  // which variables may be modified through an alias, since the analysis would
  // not see the update.
  if (HasTrylockCall)
    markEscapedLocalVars(AC);
  LocalVarMap.traverseCFG(CFGraph, SortedGraph, BlockInfo, UnevaluatedStmts);
  CurrentSortedGraph = SortedGraph;

  // Fill in source locations for all CFGBlocks.
  findBlockLocations(CFGraph, SortedGraph, BlockInfo);

  CapExprSet ExclusiveLocksAcquired;
  CapExprSet SharedLocksAcquired;
  CapExprSet LocksReleased;

  // Add locks from exclusive_locks_required and shared_locks_required
  // to initial lockset. Also turn off checking for lock and unlock functions.
  // FIXME: is there a more intelligent way to check lock/unlock functions?
  if (!SortedGraph->empty()) {
    assert(*SortedGraph->begin() == &CFGraph->getEntry());
    FactSet &InitialLockset = Initial.EntrySet;

    CapExprSet ExclusiveLocksToAdd;
    CapExprSet SharedLocksToAdd;

    SourceLocation Loc = D->getLocation();
    for (const auto *Attr : D->attrs()) {
      Loc = Attr->getLocation();
      if (const auto *A = dyn_cast<RequiresCapabilityAttr>(Attr)) {
        getMutexIDs(A->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd, A,
                    nullptr, D);
      } else if (const auto *A = dyn_cast<ReleaseCapabilityAttr>(Attr)) {
        // UNLOCK_FUNCTION() is used to hide the underlying lock implementation.
        // We must ignore such methods.
        if (A->args_size() == 0)
          return;
        getMutexIDs(A->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd, A,
                    nullptr, D);
        getMutexIDs(LocksReleased, A, nullptr, D);
      } else if (const auto *A = dyn_cast<AcquireCapabilityAttr>(Attr)) {
        if (A->args_size() == 0)
          return;
        getMutexIDs(A->isShared() ? SharedLocksAcquired
                                  : ExclusiveLocksAcquired,
                    A, nullptr, D);
      } else if (isTrylockAttr(Attr)) {
        // Don't try to check trylock functions for now.
        return;
      }
    }
    ArrayRef<ParmVarDecl *> Params;
    if (CurrentFunction)
      Params = CurrentFunction->getCanonicalDecl()->parameters();
    else if (auto CurrentMethod = dyn_cast<ObjCMethodDecl>(D))
      Params = CurrentMethod->getCanonicalDecl()->parameters();
    else
      llvm_unreachable("Unknown function kind");
    for (const ParmVarDecl *Param : Params) {
      if (isCallbackParam(Param))
        continue;
      CapExprSet UnderlyingLocks;
      for (const auto *Attr : Param->attrs()) {
        Loc = Attr->getLocation();
        if (const auto *A = dyn_cast<ReleaseCapabilityAttr>(Attr)) {
          getMutexIDs(A->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd, A,
                      nullptr, Param);
          getMutexIDs(LocksReleased, A, nullptr, Param);
          getMutexIDs(UnderlyingLocks, A, nullptr, Param);
        } else if (const auto *A = dyn_cast<RequiresCapabilityAttr>(Attr)) {
          getMutexIDs(A->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd, A,
                      nullptr, Param);
          getMutexIDs(UnderlyingLocks, A, nullptr, Param);
        } else if (const auto *A = dyn_cast<AcquireCapabilityAttr>(Attr)) {
          getMutexIDs(A->isShared() ? SharedLocksAcquired
                                    : ExclusiveLocksAcquired,
                      A, nullptr, Param);
          getMutexIDs(UnderlyingLocks, A, nullptr, Param);
        } else if (const auto *A = dyn_cast<LocksExcludedAttr>(Attr)) {
          getMutexIDs(UnderlyingLocks, A, nullptr, Param);
        }
      }
      if (UnderlyingLocks.empty())
        continue;
      CapabilityExpr Cp(SxBuilder.translateVariable(Param, nullptr),
                        StringRef(),
                        /*Neg=*/false, /*Reentrant=*/false);
      auto *ScopedEntry = FactMan.createFact<ScopedLockableFactEntry>(
          Cp, Param->getLocation(), FactEntry::Declared,
          UnderlyingLocks.size());
      for (const CapabilityExpr &M : UnderlyingLocks)
        ScopedEntry->addLock(M);
      addLock(InitialLockset, ScopedEntry, true);
    }

    // FIXME -- Loc can be wrong here.
    for (const auto &Mu : ExclusiveLocksToAdd) {
      const auto *Entry = FactMan.createFact<LockableFactEntry>(
          Mu, LK_Exclusive, Loc, FactEntry::Declared);
      addLock(InitialLockset, Entry, true);
    }
    for (const auto &Mu : SharedLocksToAdd) {
      const auto *Entry = FactMan.createFact<LockableFactEntry>(
          Mu, LK_Shared, Loc, FactEntry::Declared);
      addLock(InitialLockset, Entry, true);
    }
  }

  // Compute the expected exit set.
  // By default, we expect all locks held on entry to be held on exit.
  FactSet ExpectedFunctionExitSet = Initial.EntrySet;

  // Adjust the expected exit set by adding or removing locks, as declared
  // by *-LOCK_FUNCTION and UNLOCK_FUNCTION.  The intersect below will then
  // issue the appropriate warning.
  // FIXME: the location here is not quite right.
  for (const auto &Lock : ExclusiveLocksAcquired)
    ExpectedFunctionExitSet.addLock(
        FactMan, FactMan.createFact<LockableFactEntry>(Lock, LK_Exclusive,
                                                       D->getLocation()));
  for (const auto &Lock : SharedLocksAcquired)
    ExpectedFunctionExitSet.addLock(
        FactMan, FactMan.createFact<LockableFactEntry>(Lock, LK_Shared,
                                                       D->getLocation()));
  for (const auto &Lock : LocksReleased)
    ExpectedFunctionExitSet.removeLock(FactMan, Lock);

  if (HasTrylockCall) {
    for (const CFGBlock *B : *SortedGraph) {
      TrylockRangeCondResult Cond;
      const SwitchCaseTable *Table;
      SmallVector<const CastExpr *, 2> SwitchCasts;
      if (getTerminatorTrylockCond(B, Cond, Table, SwitchCasts))
        LastTrylockCondBlock[Cond.Call] = B;
    }
  }

  // The pending trylock ranges at the exit of each block.
  std::vector<PendingTrylockRanges> BlockExitPending(CFGraph->getNumBlockIDs());

  for (const auto *CurrBlock : *SortedGraph) {
    unsigned CurrBlockID = CurrBlock->getBlockID();
    CFGBlockInfo *CurrBlockInfo = &BlockInfo[CurrBlockID];
    PendingTrylockRanges EntryPending;

    // Use the default initial lockset in case there are no predecessors.
    VisitedBlocks.insert(CurrBlock);

    // Iterate through the predecessor blocks and warn if the lockset for all
    // predecessors is not the same. We take the entry lockset of the current
    // block to be the intersection of all previous locksets.
    // FIXME: By keeping the intersection, we may output more errors in future
    // for a lock which is not in the intersection, but was in the union. We
    // may want to also keep the union in future. As an example, let's say
    // the intersection contains Mutex L, and the union contains L and M.
    // Later we unlock M. At this point, we would output an error because we
    // never locked M; although the real error is probably that we forgot to
    // lock M on all code paths. Conversely, let's say that later we lock M.
    // In this case, we should compare against the intersection instead of the
    // union because the real error is probably that we forgot to unlock M on
    // all code paths.
    bool LocksetInitialized = false;
    // Capabilities acquired by a try-lock whose result this block's
    // terminator branches on. Computed lazily on the first join.
    CapExprSet TerminatorTrylockCaps;
    bool TerminatorTrylockCapsComputed = false;
    const bool HasUnvisitedPred =
        llvm::any_of(CurrBlock->preds(), [&](const CFGBlock *Pred) {
          return Pred && !VisitedBlocks.alreadySet(Pred);
        });
    SmallVector<std::pair<const CFGBlock *, FactSet>, 4> PredEdgeLocksets;
    SmallVector<PendingTrylockRanges, 4> PredEdgePendings;
    for (CFGBlock::const_pred_iterator PI = CurrBlock->pred_begin(),
         PE  = CurrBlock->pred_end(); PI != PE; ++PI) {
      // if *PI -> CurrBlock is a back edge
      if (*PI == nullptr || !VisitedBlocks.alreadySet(*PI))
        continue;

      unsigned PrevBlockID = (*PI)->getBlockID();
      CFGBlockInfo *PrevBlockInfo = &BlockInfo[PrevBlockID];

      // Ignore edges from blocks that can't return.
      if (neverReturns(*PI) || !PrevBlockInfo->Reachable)
        continue;

      // Okay, we can reach this block from the entry.
      CurrBlockInfo->Reachable = true;

      FactSet PrevLockset;
      PendingTrylockRanges EdgePending = BlockExitPending[PrevBlockID];
      getEdgeLockset(PrevLockset, PrevBlockInfo->ExitSet, *PI, CurrBlock,
                     &EdgePending);
      PredEdgePendings.push_back(std::move(EdgePending));
      PredEdgeLocksets.emplace_back(*PI, std::move(PrevLockset));
    }

    if (!PredEdgePendings.empty())
      joinPendingTrylockRanges(PredEdgePendings, HasUnvisitedPred,
                               EntryPending);

    for (auto &[PredBlock, PrevLockset] : PredEdgeLocksets) {
      if (!LocksetInitialized) {
        CurrBlockInfo->EntrySet = PrevLockset;
        LocksetInitialized = true;
      } else {
        // Surprisingly 'continue' doesn't always produce back edges, because
        // the CFG has empty "transition" blocks where they meet with the end
        // of the regular loop body. We still want to diagnose them as loop.
        if (isa_and_nonnull<ContinueStmt>(PredBlock->getTerminatorStmt())) {
          // Loop join: warn on locks held for only some iterations.
          intersectAndWarn(CurrBlockInfo->EntrySet, PrevLockset,
                           CurrBlockInfo->EntryLoc,
                           LEK_LockedSomeLoopIterations,
                           LEK_LockedSomeLoopIterations, nullptr);
        } else {
          // Branch join: a lockset difference is harmless if the terminator
          // re-branches on the try-lock result.
          if (!TerminatorTrylockCapsComputed) {
            // Compute once; the result depends only on CurrBlock, not on *PI.
            getTerminatorTrylockCaps(CurrBlock, TerminatorTrylockCaps,
                                     &EntryPending);
            TerminatorTrylockCapsComputed = true;
          }
          intersectAndWarn(CurrBlockInfo->EntrySet, PrevLockset,
                           CurrBlockInfo->EntryLoc, LEK_LockedSomePredecessors,
                           LEK_LockedSomePredecessors, &TerminatorTrylockCaps);
        }
      }
    }

    if (!EntryPending.empty() && PredEdgeLocksets.size() > 1)
      dropUnheldPendingAcquires(EntryPending, CurrBlockInfo);

    // Skip rest of block if it's not reachable.
    if (!CurrBlockInfo->Reachable)
      continue;

    BuildLockset LocksetBuilder(this, *CurrBlockInfo, ExpectedFunctionExitSet);

    // Visit all the statements in the basic block.
    for (const auto &BI : *CurrBlock) {
      switch (BI.getKind()) {
        case CFGElement::Statement: {
          CFGStmt CS = BI.castAs<CFGStmt>();
          const Stmt *S = CS.getStmt();
          if (UnevaluatedStmts.contains(S))
            break;
          LocksetBuilder.Visit(S);
          break;
        }
        // Ignore BaseDtor and MemberDtor for now.
        case CFGElement::AutomaticObjectDtor: {
          CFGAutomaticObjDtor AD = BI.castAs<CFGAutomaticObjDtor>();
          const auto *DD = AD.getDestructorDecl(AC.getASTContext());
          // Function parameters as they are constructed in caller's context and
          // the CFG does not contain the ctors. Ignore them as their
          // capabilities cannot be analysed because of this missing
          // information.
          if (isa_and_nonnull<ParmVarDecl>(AD.getVarDecl()) ||
              UnevaluatedVarDecls.contains(AD.getVarDecl()))
            break;
          if (!DD || !DD->hasAttrs())
            break;

          LocksetBuilder.handleCall(
              nullptr, DD,
              SxBuilder.translateVariable(AD.getVarDecl(), nullptr),
              AD.getTriggerStmt()->getEndLoc());
          break;
        }

        case CFGElement::CleanupFunction: {
          const CFGCleanupFunction &CF = BI.castAs<CFGCleanupFunction>();
          if (UnevaluatedVarDecls.contains(CF.getVarDecl()))
            break;
          LocksetBuilder.handleCall(
              /*Exp=*/nullptr, CF.getFunctionDecl(),
              SxBuilder.translateVariable(CF.getVarDecl(), nullptr),
              CF.getVarDecl()->getLocation());
          break;
        }

        case CFGElement::TemporaryDtor: {
          auto TD = BI.castAs<CFGTemporaryDtor>();

          // Clean up constructed object even if there are no attributes to
          // keep the number of objects in limbo as small as possible.
          if (auto Object = ConstructedObjects.find(
                  TD.getBindTemporaryExpr()->getSubExpr());
              Object != ConstructedObjects.end()) {
            const auto *DD = TD.getDestructorDecl(AC.getASTContext());
            if (DD->hasAttrs())
              // TODO: the location here isn't quite correct.
              LocksetBuilder.handleCall(nullptr, DD, Object->second,
                                        TD.getBindTemporaryExpr()->getEndLoc());
            ConstructedObjects.erase(Object);
          }
          break;
        }
        default:
          break;
      }
    }
    CurrBlockInfo->ExitSet = LocksetBuilder.FSet;
    if (!EntryPending.empty()) {
      updatePendingTrylockRanges(EntryPending, CurrBlock, CurrBlockInfo);
      BlockExitPending[CurrBlockID] = std::move(EntryPending);
    }

    // For every back edge from CurrBlock (the end of the loop) to another block
    // (FirstLoopBlock) we need to check that the Lockset of Block is equal to
    // the one held at the beginning of FirstLoopBlock. We can look up the
    // Lockset held at the beginning of FirstLoopBlock in the EntryLockSets map.
    for (CFGBlock::const_succ_iterator SI = CurrBlock->succ_begin(),
         SE  = CurrBlock->succ_end(); SI != SE; ++SI) {
      // if CurrBlock -> *SI is *not* a back edge
      if (*SI == nullptr || !VisitedBlocks.alreadySet(*SI))
        continue;

      CFGBlock *FirstLoopBlock = *SI;
      CFGBlockInfo *PreLoop = &BlockInfo[FirstLoopBlock->getBlockID()];
      CFGBlockInfo *LoopEnd = &BlockInfo[CurrBlockID];
      intersectAndWarn(PreLoop->EntrySet, LoopEnd->ExitSet, PreLoop->EntryLoc,
                       LEK_LockedSomeLoopIterations);
    }
  }

  // Skip the final check if the exit block is unreachable.
  if (!Final.Reachable)
    return;

  // FIXME: Should we call this function for all blocks which exit the function?
  intersectAndWarn(ExpectedFunctionExitSet, Final.ExitSet, Final.ExitLoc,
                   LEK_LockedAtEndOfFunction, LEK_NotLockedAtEndOfFunction);
}

/// Check a function's CFG for thread-safety violations.
///
/// We traverse the blocks in the CFG, compute the set of mutexes that are held
/// at the end of each block, and issue warnings for thread safety violations.
/// Each block in the CFG is traversed exactly once.
void threadSafety::runThreadSafetyAnalysis(AnalysisDeclContext &AC,
                                           ThreadSafetyHandler &Handler,
                                           BeforeSet **BSet) {
  if (!*BSet)
    *BSet = new BeforeSet;
  ThreadSafetyAnalyzer Analyzer(Handler, *BSet);
  Analyzer.runAnalysis(AC);
}

void threadSafety::threadSafetyCleanup(BeforeSet *Cache) { delete Cache; }

/// Helper function that returns a LockKind required for the given level
/// of access.
LockKind threadSafety::getLockKindFromAccessKind(AccessKind AK) {
  switch (AK) {
    case AK_Read :
      return LK_Shared;
    case AK_Written :
      return LK_Exclusive;
  }
  llvm_unreachable("Unknown AccessKind");
}
