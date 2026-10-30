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
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclGroup.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/OperationKinds.h"
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
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/TrailingObjects.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
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

namespace {

/// A set of CapabilityExpr objects, which are compiled from thread safety
/// attributes on a function.
class CapExprSet : public SmallVector<CapabilityExpr, 4> {
public:
  /// Push M onto list, but discard duplicates.
  void push_back_nodup(const CapabilityExpr &CapE) {
    if (llvm::none_of(*this, [=](const CapabilityExpr &CapE2) {
          return CapE.equals(CapE2);
        }))
      push_back(CapE);
  }
};

class FactManager;
class FactSet;

/// This is a helper class that stores a fact that is known at a
/// particular point in program execution.  Currently, a fact is a capability,
/// along with additional information, such as where it was acquired, whether
/// it is exclusive or shared, etc.
class FactEntry : public CapabilityExpr {
public:
  enum FactEntryKind { Lockable, ScopedLockable };

  /// Where a fact comes from.
  enum SourceKind {
    Acquired, ///< The fact has been directly acquired.
    Asserted, ///< The fact has been asserted to be held.
    Declared, ///< The fact is assumed to be held by callers.
    Managed,  ///< The fact has been acquired through a scoped capability.
  };

private:
  const FactEntryKind Kind : 8;

  /// Exclusive or shared.
  LockKind LKind : 8;

  /// How it was acquired.
  SourceKind Source : 8;

  /// Where it was acquired.
  SourceLocation AcquireLoc;

protected:
  ~FactEntry() = default;

public:
  FactEntry(FactEntryKind FK, const CapabilityExpr &CE, LockKind LK,
            SourceLocation Loc, SourceKind Src)
      : CapabilityExpr(CE), Kind(FK), LKind(LK), Source(Src), AcquireLoc(Loc) {}

  LockKind kind() const { return LKind;      }
  SourceLocation loc() const { return AcquireLoc; }
  FactEntryKind getFactEntryKind() const { return Kind; }

  bool asserted() const { return Source == Asserted; }
  bool declared() const { return Source == Declared; }
  bool managed() const { return Source == Managed; }

  virtual void
  handleRemovalFromIntersection(const FactSet &FSet, FactManager &FactMan,
                                SourceLocation JoinLoc, LockErrorKind LEK,
                                ThreadSafetyHandler &Handler) const = 0;
  virtual void handleLock(FactSet &FSet, FactManager &FactMan,
                          const FactEntry &entry,
                          ThreadSafetyHandler &Handler) const = 0;
  virtual void handleUnlock(FactSet &FSet, FactManager &FactMan,
                            const CapabilityExpr &Cp, SourceLocation UnlockLoc,
                            bool FullyRemove,
                            ThreadSafetyHandler &Handler) const = 0;

  // Return true if LKind >= LK, where exclusive > shared
  bool isAtLeast(LockKind LK) const {
    return  (LKind == LK_Exclusive) || (LK == LK_Shared);
  }
};

using FactID = unsigned short;

/// FactManager manages the memory for all facts that are created during
/// the analysis of a single routine.
class FactManager {
private:
  llvm::BumpPtrAllocator &Alloc;
  std::vector<const FactEntry *> Facts;

public:
  FactManager(llvm::BumpPtrAllocator &Alloc) : Alloc(Alloc) {}

  template <typename T, typename... ArgTypes>
  T *createFact(ArgTypes &&...Args) {
    static_assert(std::is_trivially_destructible_v<T>);
    return T::create(Alloc, std::forward<ArgTypes>(Args)...);
  }

  FactID newFact(const FactEntry *Entry) {
    Facts.push_back(Entry);
    assert(Facts.size() - 1 <= std::numeric_limits<FactID>::max() &&
           "FactID space exhausted");
    return static_cast<unsigned short>(Facts.size() - 1);
  }

  const FactEntry &operator[](FactID F) const { return *Facts[F]; }
};

/// A FactSet is the set of facts that are known to be true at a
/// particular program point.  FactSets must be small, because they are
/// frequently copied, and are thus implemented as a set of indices into a
/// table maintained by a FactManager.  A typical FactSet only holds 1 or 2
/// locks, so we can get away with doing a linear search for lookup.  Note
/// that a hashtable or map is inappropriate in this case, because lookups
/// may involve partial pattern matches, rather than exact matches.
class FactSet {
private:
  using FactVec = SmallVector<FactID, 4>;

  FactVec FactIDs;

public:
  using iterator = FactVec::iterator;
  using const_iterator = FactVec::const_iterator;

  iterator begin() { return FactIDs.begin(); }
  const_iterator begin() const { return FactIDs.begin(); }

  iterator end() { return FactIDs.end(); }
  const_iterator end() const { return FactIDs.end(); }

  bool isEmpty() const { return FactIDs.size() == 0; }

  // Return true if the set contains only negative facts
  bool isEmpty(FactManager &FactMan) const {
    for (const auto FID : *this) {
      if (!FactMan[FID].negative())
        return false;
    }
    return true;
  }

  void addLockByID(FactID ID) { FactIDs.push_back(ID); }

  FactID addLock(FactManager &FM, const FactEntry *Entry) {
    FactID F = FM.newFact(Entry);
    FactIDs.push_back(F);
    return F;
  }

  bool removeLock(FactManager& FM, const CapabilityExpr &CapE) {
    unsigned n = FactIDs.size();
    if (n == 0)
      return false;

    for (unsigned i = 0; i < n-1; ++i) {
      if (FM[FactIDs[i]].matches(CapE)) {
        FactIDs[i] = FactIDs[n-1];
        FactIDs.pop_back();
        return true;
      }
    }
    if (FM[FactIDs[n-1]].matches(CapE)) {
      FactIDs.pop_back();
      return true;
    }
    return false;
  }

  std::optional<FactID> replaceLock(FactManager &FM, iterator It,
                                    const FactEntry *Entry) {
    if (It == end())
      return std::nullopt;
    FactID F = FM.newFact(Entry);
    *It = F;
    return F;
  }

  std::optional<FactID> replaceLock(FactManager &FM, const CapabilityExpr &CapE,
                                    const FactEntry *Entry) {
    return replaceLock(FM, findLockIter(FM, CapE), Entry);
  }

  iterator findLockIter(FactManager &FM, const CapabilityExpr &CapE) {
    return llvm::find_if(*this,
                         [&](FactID ID) { return FM[ID].matches(CapE); });
  }

  const FactEntry *findLock(FactManager &FM, const CapabilityExpr &CapE) const {
    auto I =
        llvm::find_if(*this, [&](FactID ID) { return FM[ID].matches(CapE); });
    return I != end() ? &FM[*I] : nullptr;
  }

  const FactEntry *findLockUniv(FactManager &FM,
                                const CapabilityExpr &CapE) const {
    auto I = llvm::find_if(
        *this, [&](FactID ID) -> bool { return FM[ID].matchesUniv(CapE); });
    return I != end() ? &FM[*I] : nullptr;
  }

  const FactEntry *findPartialMatch(FactManager &FM,
                                    const CapabilityExpr &CapE) const {
    auto I = llvm::find_if(*this, [&](FactID ID) -> bool {
      return FM[ID].partiallyMatches(CapE);
    });
    return I != end() ? &FM[*I] : nullptr;
  }

  bool containsMutexDecl(FactManager &FM, const ValueDecl* Vd) const {
    auto I = llvm::find_if(
        *this, [&](FactID ID) -> bool { return FM[ID].valueDecl() == Vd; });
    return I != end();
  }
};

class ThreadSafetyAnalyzer;

} // namespace

namespace clang {
namespace threadSafety {

class BeforeSet {
private:
  using BeforeVect = SmallVector<const ValueDecl *, 4>;

  struct BeforeInfo {
    BeforeVect Vect;
    int Visited = 0;

    BeforeInfo() = default;
    BeforeInfo(BeforeInfo &&) = default;
  };

  using BeforeMap =
      llvm::DenseMap<const ValueDecl *, std::unique_ptr<BeforeInfo>>;
  using CycleMap = llvm::DenseMap<const ValueDecl *, bool>;

public:
  BeforeSet() = default;

  BeforeInfo* insertAttrExprs(const ValueDecl* Vd,
                              ThreadSafetyAnalyzer& Analyzer);

  BeforeInfo *getBeforeInfoForDecl(const ValueDecl *Vd,
                                   ThreadSafetyAnalyzer &Analyzer);

  void checkBeforeAfter(const ValueDecl *Vd, const FactSet &FSet,
                        ThreadSafetyAnalyzer &Analyzer, SourceLocation Loc,
                        StringRef CapKind,
                        ThreadSafetyHandler *DiagHandler = nullptr);

private:
  BeforeMap BMap;
  CycleMap CycMap;
};

} // namespace threadSafety
} // namespace clang

namespace {

class LocalVariableMap;

using LocalVarContext = llvm::ImmutableMap<const NamedDecl *, unsigned>;

/// A side (entry or exit) of a CFG node.
enum CFGBlockSide { CBS_Entry, CBS_Exit };

/// CFGBlockInfo is a struct which contains all the information that is
/// maintained for each block in the CFG.  See LocalVariableMap for more
/// information about the contexts.
struct CFGBlockInfo {
  // Lockset held at entry to block
  FactSet EntrySet;

  // Lockset held at exit from block
  FactSet ExitSet;

  // Context held at entry to block
  LocalVarContext EntryContext;

  // Context held at exit from block
  LocalVarContext ExitContext;

  // Location of first statement in block
  SourceLocation EntryLoc;

  // Location of last statement in block.
  SourceLocation ExitLoc;

  // Used to replay contexts later
  unsigned EntryIndex;

  // Is this block reachable?
  bool Reachable = false;

  const FactSet &getSet(CFGBlockSide Side) const {
    return Side == CBS_Entry ? EntrySet : ExitSet;
  }

  SourceLocation getLocation(CFGBlockSide Side) const {
    return Side == CBS_Entry ? EntryLoc : ExitLoc;
  }

private:
  CFGBlockInfo(LocalVarContext EmptyCtx)
      : EntryContext(EmptyCtx), ExitContext(EmptyCtx) {}

public:
  static CFGBlockInfo getEmptyBlockInfo(LocalVariableMap &M);
};

// A LocalVariableMap maintains a map from local variables to their currently
// valid definitions.  It provides SSA-like functionality when traversing the
// CFG.  Like SSA, each definition or assignment to a variable is assigned a
// unique name (an integer), which acts as the SSA name for that definition.
// The total set of names is shared among all CFG basic blocks.
// Unlike SSA, we do not rewrite expressions to replace local variables declrefs
// with their SSA-names.  Instead, we compute a Context for each point in the
// code, which maps local variables to the appropriate SSA-name.  This map
// changes with each assignment.
//
// The map is computed in a single pass over the CFG.  Subsequent analyses can
// then query the map to find the appropriate Context for a statement, and use
// that Context to look up the definitions of variables.
class LocalVariableMap {
public:
  using Context = LocalVarContext;

  /// A VarDefinition consists of an expression, representing the value of the
  /// variable, along with the context in which that expression should be
  /// interpreted.  A reference VarDefinition does not itself contain this
  /// information, but instead contains a pointer to a previous VarDefinition.
  struct VarDefinition {
  public:
    friend class LocalVariableMap;

    // The original declaration for this variable.
    const NamedDecl *Dec;

    // The expression for this variable, OR
    const Expr *Exp = nullptr;

    // Direct reference to another VarDefinition
    unsigned DirectRef = 0;

    // Reference to underlying canonical non-reference VarDefinition.
    unsigned CanonicalRef = 0;

    // The map with which Exp should be interpreted.
    Context Ctx;

    bool isReference() const { return !Exp; }

    void invalidateRef() { DirectRef = CanonicalRef = 0; }

  private:
    // Create ordinary variable definition
    VarDefinition(const NamedDecl *D, const Expr *E, Context C)
        : Dec(D), Exp(E), Ctx(C) {}

    // Create reference to previous definition
    VarDefinition(const NamedDecl *D, unsigned DirectRef, unsigned CanonicalRef,
                  Context C)
        : Dec(D), DirectRef(DirectRef), CanonicalRef(CanonicalRef), Ctx(C) {}
  };

private:
  Context::Factory ContextFactory;
  std::vector<VarDefinition> VarDefinitions;
  std::vector<std::pair<const Stmt *, Context>> SavedContexts;

public:
  LocalVariableMap() {
    // index 0 is a placeholder for undefined variables (aka phi-nodes).
    VarDefinitions.push_back(VarDefinition(nullptr, 0, 0, getEmptyContext()));
  }

  /// Look up a definition, within the given context.
  const VarDefinition* lookup(const NamedDecl *D, Context Ctx) {
    const unsigned *i = Ctx.lookup(D);
    if (!i)
      return nullptr;
    assert(*i < VarDefinitions.size());
    return &VarDefinitions[*i];
  }

  /// Look up the definition for D within the given context.  Returns
  /// NULL if the expression is not statically known.  If successful, also
  /// modifies Ctx to hold the context of the return Expr.
  const Expr* lookupExpr(const NamedDecl *D, Context &Ctx) {
    const unsigned *P = Ctx.lookup(D);
    if (!P)
      return nullptr;

    unsigned i = *P;
    while (i > 0) {
      if (VarDefinitions[i].Exp) {
        Ctx = VarDefinitions[i].Ctx;
        return VarDefinitions[i].Exp;
      }
      i = VarDefinitions[i].DirectRef;
    }
    return nullptr;
  }

  Context getEmptyContext() { return ContextFactory.getEmptyMap(); }

  /// Return the next context after processing S.  This function is used by
  /// clients of the class to get the appropriate context when traversing the
  /// CFG.  It must be called for every assignment, increment/decrement,
  /// CallExpr, or DeclStmt.
  const Context &getNextContext(unsigned &CtxIndex, const Stmt *S,
                                const Context &C) {
    if (SavedContexts[CtxIndex + 1].first == S) {
      CtxIndex++;
      const Context &Result = SavedContexts[CtxIndex].second;
      return Result;
    }
    return C;
  }

  void dumpVarDefinitionName(unsigned i) {
    if (i == 0) {
      llvm::errs() << "Undefined";
      return;
    }
    const NamedDecl *Dec = VarDefinitions[i].Dec;
    if (!Dec) {
      llvm::errs() << "<<NULL>>";
      return;
    }
    Dec->printName(llvm::errs());
    llvm::errs() << "." << i << " " << ((const void*) Dec);
  }

  /// Dumps an ASCII representation of the variable map to llvm::errs()
  void dump() {
    for (unsigned i = 1, e = VarDefinitions.size(); i < e; ++i) {
      const Expr *Exp = VarDefinitions[i].Exp;
      unsigned Ref = VarDefinitions[i].DirectRef;

      dumpVarDefinitionName(i);
      llvm::errs() << " = ";
      if (Exp) Exp->dump();
      else {
        dumpVarDefinitionName(Ref);
        llvm::errs() << "\n";
      }
    }
  }

  /// Dumps an ASCII representation of a Context to llvm::errs()
  void dumpContext(Context C) {
    for (Context::iterator I = C.begin(), E = C.end(); I != E; ++I) {
      const NamedDecl *D = I.getKey();
      D->printName(llvm::errs());
      llvm::errs() << " -> ";
      dumpVarDefinitionName(I.getData());
      llvm::errs() << "\n";
    }
  }

  /// Builds the variable map.
  void traverseCFG(CFG *CFGraph, const PostOrderCFGView *SortedGraph,
                   std::vector<CFGBlockInfo> &BlockInfo);

protected:
  friend class VarMapBuilder;

  // Resolve any definition ID down to its non-reference base ID.
  unsigned getCanonicalDefinitionID(unsigned ID) const {
    while (ID > 0 && VarDefinitions[ID].isReference())
      ID = VarDefinitions[ID].CanonicalRef;
    return ID;
  }

  // Get the current context index
  unsigned getContextIndex() { return SavedContexts.size()-1; }

  // Save the current context for later replay
  void saveContext(const Stmt *S, Context C) {
    SavedContexts.push_back(std::make_pair(S, C));
  }

  // Adds a new definition to the given context, and returns a new context.
  // This method should be called when declaring a new variable.
  Context addDefinition(const NamedDecl *D, const Expr *Exp, Context Ctx) {
    assert(!Ctx.contains(D));
    unsigned newID = VarDefinitions.size();
    Context NewCtx = ContextFactory.add(Ctx, D, newID);
    VarDefinitions.push_back(VarDefinition(D, Exp, Ctx));
    return NewCtx;
  }

  // Add a new reference to an existing definition.
  Context addReference(const NamedDecl *D, unsigned Ref, Context Ctx) {
    unsigned newID = VarDefinitions.size();
    Context NewCtx = ContextFactory.add(Ctx, D, newID);
    VarDefinitions.push_back(
        VarDefinition(D, Ref, getCanonicalDefinitionID(Ref), Ctx));
    return NewCtx;
  }

  // Updates a definition only if that definition is already in the map.
  // This method should be called when assigning to an existing variable.
  Context updateDefinition(const NamedDecl *D, Expr *Exp, Context Ctx) {
    if (Ctx.contains(D)) {
      unsigned newID = VarDefinitions.size();
      Context NewCtx = ContextFactory.remove(Ctx, D);
      NewCtx = ContextFactory.add(NewCtx, D, newID);
      VarDefinitions.push_back(VarDefinition(D, Exp, Ctx));
      return NewCtx;
    }
    return Ctx;
  }

  // Removes a definition from the context, but keeps the variable name
  // as a valid variable.  The index 0 is a placeholder for cleared definitions.
  Context clearDefinition(const NamedDecl *D, Context Ctx) {
    Context NewCtx = Ctx;
    if (NewCtx.contains(D)) {
      NewCtx = ContextFactory.remove(NewCtx, D);
      NewCtx = ContextFactory.add(NewCtx, D, 0);
    }
    return NewCtx;
  }

  // Remove a definition entirely frmo the context.
  Context removeDefinition(const NamedDecl *D, Context Ctx) {
    Context NewCtx = Ctx;
    if (NewCtx.contains(D)) {
      NewCtx = ContextFactory.remove(NewCtx, D);
    }
    return NewCtx;
  }

  Context intersectContexts(Context C1, Context C2);
  Context createReferenceContext(Context C);
  void intersectBackEdge(Context C1, Context C2);
};

} // namespace

// This has to be defined after LocalVariableMap.
CFGBlockInfo CFGBlockInfo::getEmptyBlockInfo(LocalVariableMap &M) {
  return CFGBlockInfo(M.getEmptyContext());
}

namespace {

/// Visitor which builds a LocalVariableMap
class VarMapBuilder : public ConstStmtVisitor<VarMapBuilder> {
public:
  LocalVariableMap* VMap;
  LocalVariableMap::Context Ctx;

  VarMapBuilder(LocalVariableMap *VM, LocalVariableMap::Context C)
      : VMap(VM), Ctx(C) {}

  void VisitDeclStmt(const DeclStmt *S);
  void VisitBinaryOperator(const BinaryOperator *BO);
  void VisitUnaryOperator(const UnaryOperator *UO);
  void VisitCallExpr(const CallExpr *CE);
};

} // namespace

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

// Update local variable definitions in variable map
void VarMapBuilder::VisitBinaryOperator(const BinaryOperator *BO) {
  if (!BO->isAssignmentOp())
    return;

  Expr *LHSExp = BO->getLHS()->IgnoreParenCasts();

  // Update the variable map and current context.
  if (const auto *DRE = dyn_cast<DeclRefExpr>(LHSExp)) {
    const ValueDecl *VDec = DRE->getDecl();
    if (Ctx.lookup(VDec)) {
      if (BO->getOpcode() == BO_Assign)
        Ctx = VMap->updateDefinition(VDec, BO->getRHS(), Ctx);
      else
        // FIXME -- handle compound assignment operators
        Ctx = VMap->clearDefinition(VDec, Ctx);
      VMap->saveContext(BO, Ctx);
    }
  }
}

// Invalidate the definitions of local variables that are incremented or
// decremented.
void VarMapBuilder::VisitUnaryOperator(const UnaryOperator *UO) {
  if (!UO->isIncrementDecrementOp())
    return;
  if (const auto *DRE =
          dyn_cast<DeclRefExpr>(UO->getSubExpr()->IgnoreParenCasts())) {
    const ValueDecl *VDec = DRE->getDecl();
    if (Ctx.lookup(VDec)) {
      Ctx = VMap->clearDefinition(VDec, Ctx);
      VMap->saveContext(UO, Ctx);
    }
  }
}

// Invalidates local variable definitions if variable escaped.
void VarMapBuilder::VisitCallExpr(const CallExpr *CE) {
  const FunctionDecl *FD = CE->getDirectCallee();
  if (!FD)
    return;

  // Heuristic for likely-benign functions that pass by mutable reference. This
  // is needed to avoid a slew of false positives due to mutable reference
  // passing where the captured reference is usually passed on by-value.
  if (const IdentifierInfo *II = FD->getIdentifier()) {
    // Any kind of std::bind-like functions.
    if (II->isStr("bind") || II->isStr("bind_front"))
      return;
  }

  // Invalidate local variable definitions that are passed by non-const
  // reference or non-const pointer.
  for (unsigned Idx = 0; Idx < CE->getNumArgs(); ++Idx) {
    if (Idx >= FD->getNumParams())
      break;

    const Expr *Arg = CE->getArg(Idx)->IgnoreParenImpCasts();
    const ParmVarDecl *PVD = FD->getParamDecl(Idx);
    QualType ParamType = PVD->getType();

    // Potential reassignment if passed by non-const reference / pointer.
    const ValueDecl *VDec = nullptr;
    if (ParamType->isReferenceType() &&
        !ParamType->getPointeeType().isConstQualified()) {
      if (const auto *DRE = dyn_cast<DeclRefExpr>(Arg))
        VDec = DRE->getDecl();
    } else if (ParamType->isPointerType() &&
               !ParamType->getPointeeType().isConstQualified()) {
      Arg = Arg->IgnoreParenCasts();
      if (const auto *UO = dyn_cast<UnaryOperator>(Arg)) {
        if (UO->getOpcode() == UO_AddrOf) {
          const Expr *SubE = UO->getSubExpr()->IgnoreParenCasts();
          if (const auto *DRE = dyn_cast<DeclRefExpr>(SubE))
            VDec = DRE->getDecl();
        }
      }
    }

    if (VDec)
      Ctx = VMap->clearDefinition(VDec, Ctx);
  }
  // Save the context after the call where escaped variables' definitions (if
  // they exist) are cleared.
  VMap->saveContext(CE, Ctx);
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
void LocalVariableMap::traverseCFG(CFG *CFGraph,
                                   const PostOrderCFGView *SortedGraph,
                                   std::vector<CFGBlockInfo> &BlockInfo) {
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
          CFGStmt CS = BI.castAs<CFGStmt>();
          VMapBuilder.Visit(CS.getStmt());
          break;
        }
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

namespace {

class LockableFactEntry final : public FactEntry {
private:
  /// Reentrancy depth: incremented when a capability has been acquired
  /// reentrantly (after initial acquisition). Always 0 for non-reentrant
  /// capabilities.
  unsigned int ReentrancyDepth = 0;

  LockableFactEntry(const CapabilityExpr &CE, LockKind LK, SourceLocation Loc,
                    SourceKind Src)
      : FactEntry(Lockable, CE, LK, Loc, Src) {}

public:
  static LockableFactEntry *create(llvm::BumpPtrAllocator &Alloc,
                                   const LockableFactEntry &Other) {
    return new (Alloc) LockableFactEntry(Other);
  }

  static LockableFactEntry *create(llvm::BumpPtrAllocator &Alloc,
                                   const CapabilityExpr &CE, LockKind LK,
                                   SourceLocation Loc,
                                   SourceKind Src = Acquired) {
    return new (Alloc) LockableFactEntry(CE, LK, Loc, Src);
  }

  unsigned int getReentrancyDepth() const { return ReentrancyDepth; }

  void
  handleRemovalFromIntersection(const FactSet &FSet, FactManager &FactMan,
                                SourceLocation JoinLoc, LockErrorKind LEK,
                                ThreadSafetyHandler &Handler) const override {
    if (!asserted() && !negative() && !isUniversal()) {
      Handler.handleMutexHeldEndOfScope(getKind(), toString(), loc(), JoinLoc,
                                        LEK);
    }
  }

  void handleLock(FactSet &FSet, FactManager &FactMan, const FactEntry &entry,
                  ThreadSafetyHandler &Handler) const override {
    if (const FactEntry *RFact = tryReenter(FactMan, entry.kind())) {
      // This capability has been reentrantly acquired.
      FSet.replaceLock(FactMan, entry, RFact);
    } else {
      Handler.handleDoubleLock(entry.getKind(), entry.toString(), loc(),
                               entry.loc());
    }
  }

  void handleUnlock(FactSet &FSet, FactManager &FactMan,
                    const CapabilityExpr &Cp, SourceLocation UnlockLoc,
                    bool FullyRemove,
                    ThreadSafetyHandler &Handler) const override {
    FSet.removeLock(FactMan, Cp);

    if (const FactEntry *RFact = leaveReentrant(FactMan)) {
      // This capability remains reentrantly acquired.
      FSet.addLock(FactMan, RFact);
    } else if (!Cp.negative()) {
      FSet.addLock(FactMan, FactMan.createFact<LockableFactEntry>(
                                !Cp, LK_Exclusive, UnlockLoc));
    }
  }

  // Return an updated FactEntry if we can acquire this capability reentrant,
  // nullptr otherwise.
  const FactEntry *tryReenter(FactManager &FactMan,
                              LockKind ReenterKind) const {
    if (!reentrant())
      return nullptr;
    if (kind() != ReenterKind)
      return nullptr;
    auto *NewFact = FactMan.createFact<LockableFactEntry>(*this);
    NewFact->ReentrancyDepth++;
    return NewFact;
  }

  // Return an updated FactEntry if we are releasing a capability previously
  // acquired reentrant, nullptr otherwise.
  const FactEntry *leaveReentrant(FactManager &FactMan) const {
    if (!ReentrancyDepth)
      return nullptr;
    assert(reentrant());
    auto *NewFact = FactMan.createFact<LockableFactEntry>(*this);
    NewFact->ReentrancyDepth--;
    return NewFact;
  }

  static bool classof(const FactEntry *A) {
    return A->getFactEntryKind() == Lockable;
  }
};

enum UnderlyingCapabilityKind {
  UCK_Acquired,          ///< Any kind of acquired capability.
  UCK_ReleasedShared,    ///< Shared capability that was released.
  UCK_ReleasedExclusive, ///< Exclusive capability that was released.
};

struct UnderlyingCapability {
  CapabilityExpr Cap;
  UnderlyingCapabilityKind Kind;
};

class ScopedLockableFactEntry final
    : public FactEntry,
      private llvm::TrailingObjects<ScopedLockableFactEntry,
                                    UnderlyingCapability> {
  friend TrailingObjects;

private:
  const unsigned ManagedCapacity;
  unsigned ManagedSize = 0;

  ScopedLockableFactEntry(const CapabilityExpr &CE, SourceLocation Loc,
                          SourceKind Src, unsigned ManagedCapacity)
      : FactEntry(ScopedLockable, CE, LK_Exclusive, Loc, Src),
        ManagedCapacity(ManagedCapacity) {}

  void addManaged(const CapabilityExpr &M, UnderlyingCapabilityKind UCK) {
    assert(ManagedSize < ManagedCapacity);
    new (getTrailingObjects() + ManagedSize) UnderlyingCapability{M, UCK};
    ++ManagedSize;
  }

  ArrayRef<UnderlyingCapability> getManaged() const {
    return getTrailingObjects(ManagedSize);
  }

public:
  static ScopedLockableFactEntry *create(llvm::BumpPtrAllocator &Alloc,
                                         const CapabilityExpr &CE,
                                         SourceLocation Loc, SourceKind Src,
                                         unsigned ManagedCapacity) {
    void *Storage =
        Alloc.Allocate(totalSizeToAlloc<UnderlyingCapability>(ManagedCapacity),
                       alignof(ScopedLockableFactEntry));
    return new (Storage) ScopedLockableFactEntry(CE, Loc, Src, ManagedCapacity);
  }

  CapExprSet getUnderlyingMutexes() const {
    CapExprSet UnderlyingMutexesSet;
    for (const UnderlyingCapability &UnderlyingMutex : getManaged())
      UnderlyingMutexesSet.push_back(UnderlyingMutex.Cap);
    return UnderlyingMutexesSet;
  }

  /// \name Adding managed locks
  /// Capacity for managed locks must have been allocated via \ref create.
  /// There is no reallocation in case the capacity is exceeded!
  /// \{
  void addLock(const CapabilityExpr &M) { addManaged(M, UCK_Acquired); }

  void addExclusiveUnlock(const CapabilityExpr &M) {
    addManaged(M, UCK_ReleasedExclusive);
  }

  void addSharedUnlock(const CapabilityExpr &M) {
    addManaged(M, UCK_ReleasedShared);
  }
  /// \}

  void
  handleRemovalFromIntersection(const FactSet &FSet, FactManager &FactMan,
                                SourceLocation JoinLoc, LockErrorKind LEK,
                                ThreadSafetyHandler &Handler) const override {
    if (LEK == LEK_LockedAtEndOfFunction || LEK == LEK_NotLockedAtEndOfFunction)
      return;

    for (const auto &UnderlyingMutex : getManaged()) {
      const auto *Entry = FSet.findLock(FactMan, UnderlyingMutex.Cap);
      if ((UnderlyingMutex.Kind == UCK_Acquired && Entry) ||
          (UnderlyingMutex.Kind != UCK_Acquired && !Entry)) {
        // If this scoped lock manages another mutex, and if the underlying
        // mutex is still/not held, then warn about the underlying mutex.
        Handler.handleMutexHeldEndOfScope(UnderlyingMutex.Cap.getKind(),
                                          UnderlyingMutex.Cap.toString(), loc(),
                                          JoinLoc, LEK);
      }
    }
  }

  void handleLock(FactSet &FSet, FactManager &FactMan, const FactEntry &entry,
                  ThreadSafetyHandler &Handler) const override {
    for (const auto &UnderlyingMutex : getManaged()) {
      if (UnderlyingMutex.Kind == UCK_Acquired)
        lock(FSet, FactMan, UnderlyingMutex.Cap, entry.kind(), entry.loc(),
             &Handler);
      else
        unlock(FSet, FactMan, UnderlyingMutex.Cap, entry.loc(), &Handler);
    }
  }

  void handleUnlock(FactSet &FSet, FactManager &FactMan,
                    const CapabilityExpr &Cp, SourceLocation UnlockLoc,
                    bool FullyRemove,
                    ThreadSafetyHandler &Handler) const override {
    assert(!Cp.negative() && "Managing object cannot be negative.");
    for (const auto &UnderlyingMutex : getManaged()) {
      // Remove/lock the underlying mutex if it exists/is still unlocked; warn
      // on double unlocking/locking if we're not destroying the scoped object.
      ThreadSafetyHandler *TSHandler = FullyRemove ? nullptr : &Handler;
      if (UnderlyingMutex.Kind == UCK_Acquired) {
        unlock(FSet, FactMan, UnderlyingMutex.Cap, UnlockLoc, TSHandler);
      } else {
        LockKind kind = UnderlyingMutex.Kind == UCK_ReleasedShared
                            ? LK_Shared
                            : LK_Exclusive;
        lock(FSet, FactMan, UnderlyingMutex.Cap, kind, UnlockLoc, TSHandler);
      }
    }
    if (FullyRemove)
      FSet.removeLock(FactMan, Cp);
  }

  static bool classof(const FactEntry *A) {
    return A->getFactEntryKind() == ScopedLockable;
  }

private:
  void lock(FactSet &FSet, FactManager &FactMan, const CapabilityExpr &Cp,
            LockKind kind, SourceLocation loc,
            ThreadSafetyHandler *Handler) const {
    if (const auto It = FSet.findLockIter(FactMan, Cp); It != FSet.end()) {
      const auto &Fact = cast<LockableFactEntry>(FactMan[*It]);
      if (const FactEntry *RFact = Fact.tryReenter(FactMan, kind)) {
        // This capability has been reentrantly acquired.
        FSet.replaceLock(FactMan, It, RFact);
      } else if (Handler) {
        Handler->handleDoubleLock(Cp.getKind(), Cp.toString(), Fact.loc(), loc);
      }
    } else {
      FSet.removeLock(FactMan, !Cp);
      FSet.addLock(FactMan, FactMan.createFact<LockableFactEntry>(Cp, kind, loc,
                                                                  Managed));
    }
  }

  void unlock(FactSet &FSet, FactManager &FactMan, const CapabilityExpr &Cp,
              SourceLocation loc, ThreadSafetyHandler *Handler) const {
    if (const auto It = FSet.findLockIter(FactMan, Cp); It != FSet.end()) {
      const auto &Fact = cast<LockableFactEntry>(FactMan[*It]);
      if (const FactEntry *RFact = Fact.leaveReentrant(FactMan)) {
        // This capability remains reentrantly acquired.
        FSet.replaceLock(FactMan, It, RFact);
        return;
      }

      FSet.replaceLock(
          FactMan, It,
          FactMan.createFact<LockableFactEntry>(!Cp, LK_Exclusive, loc));
    } else if (Handler) {
      SourceLocation PrevLoc;
      if (const FactEntry *Neg = FSet.findLock(FactMan, !Cp))
        PrevLoc = Neg->loc();
      Handler->handleUnmatchedUnlock(Cp.getKind(), Cp.toString(), loc, PrevLoc);
    }
  }
};

/// Class which implements the core thread safety analysis routines.
/// The body of a trivial inline or constexpr function whose return value can
/// be evaluated in terms of its parameters.
struct TrivialInlineBody {
  const FunctionDecl *DefFD = nullptr;
  const Expr *SingleRet = nullptr;
  const Expr *CondExpr = nullptr;
  const Expr *ThenRet = nullptr;
  const Expr *ElseRet = nullptr;
  llvm::SmallPtrSet<const ValueDecl *, 8> CalleeEscaped;
};

class ThreadSafetyAnalyzer {
  friend class BuildLockset;
  friend class threadSafety::BeforeSet;

  llvm::BumpPtrAllocator Bpa;
  threadSafety::til::MemRegionRef Arena;
  threadSafety::SExprBuilder SxBuilder;

  ThreadSafetyHandler &Handler;
  ASTContext *ASTCtx = nullptr;
  const FunctionDecl *CurrentFunction = nullptr;
  LocalVariableMap LocalVarMap;
  // Maps constructed objects to `this` placeholder prior to initialization.
  llvm::SmallDenseMap<const Expr *, til::LiteralPtr *> ConstructedObjects;
  FactManager FactMan;
  std::vector<CFGBlockInfo> BlockInfo;

  BeforeSet *GlobalBeforeSet;

public:
  ThreadSafetyAnalyzer(ThreadSafetyHandler &H, BeforeSet *Bset)
      : Arena(&Bpa), SxBuilder(Arena), Handler(H), FactMan(Bpa),
        GlobalBeforeSet(Bset) {}

  bool inCurrentScope(const CapabilityExpr &CapE);

  void addLock(FactSet &FSet, const FactEntry *Entry, bool ReqAttr = false);
  void removeLock(FactSet &FSet, const CapabilityExpr &CapE,
                  SourceLocation UnlockLoc, bool FullyRemove, LockKind Kind);

  template <typename AttrType>
  void getMutexIDs(CapExprSet &Mtxs, AttrType *Attr, const Expr *Exp,
                   const NamedDecl *D, til::SExpr *Self = nullptr);

  template <class AttrType>
  void getMutexIDs(CapExprSet &Mtxs, AttrType *Attr, const Expr *Exp,
                   const NamedDecl *D,
                   const CFGBlock *PredBlock, const CFGBlock *CurrBlock,
                   Expr *BrE, bool Neg);

  struct IntDomain {
    unsigned BitWidth = 0;
    llvm::APSInt Lo;
    llvm::APSInt Hi;

    IntDomain() = default;
    IntDomain(unsigned BitWidth, llvm::APSInt Lo, llvm::APSInt Hi)
        : BitWidth(BitWidth), Lo(std::move(Lo)), Hi(std::move(Hi)) {}

    static IntDomain forType(QualType Ty, const ASTContext &Ctx);
    llvm::APSInt toDomainInt(const llvm::APSInt &V) const;
  };

  class IntRangeSet {
    SmallVector<std::pair<llvm::APSInt, llvm::APSInt>, 2> Intervals;

  public:
    IntRangeSet() = default;

    bool empty() const { return Intervals.empty(); }

    static IntRangeSet full(const IntDomain &Dom);
    static IntRangeSet closedRange(const IntDomain &Dom,
                                   const llvm::APSInt &First,
                                   const llvm::APSInt &Last);
    static IntRangeSet single(const IntDomain &Dom, const llvm::APSInt &Val);
    static IntRangeSet forComparison(const IntDomain &Dom,
                                     BinaryOperator::Opcode Opc,
                                     const llvm::APSInt &K);

    /// Union of all \p Sets in O(N log N) time, where N is the total number
    /// of intervals. All sets must belong to the same domain.
    static IntRangeSet unionAll(ArrayRef<IntRangeSet> Sets);

    IntRangeSet complement(const IntDomain &Dom) const;
    IntRangeSet intersect(const IntRangeSet &Other) const;
    IntRangeSet unionWith(const IntRangeSet &Other) const;

    bool subsetOf(const llvm::APSInt &First, const llvm::APSInt &Last) const;
    bool intersects(const llvm::APSInt &First, const llvm::APSInt &Last) const;
    bool subsetOfSet(const IntRangeSet &Other) const;
    bool intersectsSet(const IntRangeSet &Other) const;
    bool isSingleValue(llvm::APSInt &Val) const;
    ArrayRef<std::pair<llvm::APSInt, llvm::APSInt>> intervals() const {
      return Intervals;
    }
  };

  using AcquiredTrylockKey = std::pair<const CallExpr *, const Attr *>;

  struct TrylockExitSpec {
    CapabilityExpr Cap;
    LockKind LK;
    IntRangeSet SuccessSet;
    SourceLocation Loc;
  };

  struct TrylockValueState {
    bool Infeasible = false;
    llvm::SmallDenseMap<const ValueDecl *, IntRangeSet, 4> VarRanges;
    llvm::SmallDenseMap<const Expr *, IntRangeSet, 4> ExprRanges;
    llvm::SmallDenseMap<const BinaryOperator *, bool, 2> ShortCircuitedOps;
    llvm::SmallDenseSet<AcquiredTrylockKey, 4> AcquiredTrylockAttrs;
    // Trylock calls whose capabilities have been acquired on a path and are
    // no longer held, e.g. because these have been released. Branching again
    // on the result of such a call must not acquire the capabilities again.
    llvm::SmallDenseSet<AcquiredTrylockKey, 4> ConsumedTrylockAttrs;
    // Trylock calls whose result has been discarded.
    llvm::SmallSetVector<const CallExpr *, 2> DiscardedTrylockCalls;
    llvm::SmallDenseMap<const ValueDecl *,
                        std::pair<const Expr *, LocalVarContext>, 2>
        UnmaterializedVarDefs;
  };

  struct TrylockEdgeBundle {
    FactSet Lockset;
    TrylockValueState ValState;
  };

  struct PendingTrylockAcquire {
    CapabilityExpr Cap;
    LockKind LK;
    SourceLocation Loc;
  };

  struct ReturnEvalOutcome {
    IntRangeSet Values;
    FactSet Lockset;
    SmallVector<PendingTrylockAcquire, 2> PendingAcquires;
  };

  SmallVector<TrylockExitSpec, 2> CurrentTrylockExitSpecs;
  IntDomain CurrentTrylockRetDom;

  /// The values that select each case label of a switch statement and the
  /// values that select the default label (or skip the switch body).
  struct SwitchCaseTable {
    bool Valid = false;
    llvm::SmallDenseMap<const SwitchCase *, IntRangeSet, 8> CaseSets;
    IntRangeSet DefaultSet;
  };
  // Switch case tables per switch statement and integer domain. Computing
  // these once per switch statement keeps the cost of handling all edges of
  // a switch statement O(N log N) instead of O(N^3).
  mutable llvm::DenseMap<const SwitchStmt *,
                         SmallVector<std::pair<IntDomain, SwitchCaseTable>, 1>>
      SwitchTables;
  /// Return the case table for \p SS in domain \p Dom. The returned
  /// reference is invalidated by the next call of this function.
  const SwitchCaseTable &getSwitchCaseTable(const SwitchStmt *SS,
                                            const IntDomain &Dom) const;

  struct TrylockRangeCondResult {
    const CallExpr *Call = nullptr;
    const NamedDecl *Callee = nullptr;
    IntDomain Dom;
    IntRangeSet TrueSet;
    IntRangeSet FalseSet;

    TrylockRangeCondResult() = default;
    TrylockRangeCondResult(const CallExpr *Call, const NamedDecl *Callee,
                           IntDomain Dom, IntRangeSet TrueSet,
                           IntRangeSet FalseSet)
        : Call(Call), Callee(Callee), Dom(std::move(Dom)),
          TrueSet(std::move(TrueSet)), FalseSet(std::move(FalseSet)) {}
  };

  const CallExpr *getTrylockCallExpr(const Stmt *Cond, LocalVarContext C,
                                     bool &Negate);
  const CallExpr *unwrapTrylockValueExpr(const Expr *E, LocalVarContext C);
  bool isGuaranteedZeroOrOneExpr(const Expr *E, LocalVarContext C);
  TrylockRangeCondResult evaluateTrylockRangeCond(const Stmt *Cond,
                                                  LocalVarContext C);
  TrylockRangeCondResult evaluateTrylockRangeCondImpl(const Stmt *Cond,
                                                      LocalVarContext C);
  // Results of evaluateTrylockRangeCond(), keyed by the condition and the
  // root of the local variable context. Memoization keeps the evaluation of
  // chains of logical operators on variables linear instead of exponential.
  llvm::DenseMap<std::pair<const Stmt *, const void *>, TrylockRangeCondResult>
      RangeCondCache;
  void applyRangeTrylockEdge(
      FactSet &Result, const CFGBlock *PredBlock, const CFGBlock *CurrBlock,
      llvm::SmallDenseSet<AcquiredTrylockKey, 4> *AcquiredAttrs = nullptr,
      const llvm::SmallDenseSet<AcquiredTrylockKey, 4> *ConsumedAttrs =
          nullptr);
  void getRangeTerminatorTrylockCaps(const CFGBlock *Block, CapExprSet &Caps);

  using TerminatorTrylockCall =
      std::tuple<const CallExpr *, const NamedDecl *,
                 std::optional<llvm::scope_exit<std::function<void()>>>>;

  TerminatorTrylockCall getTerminatorTrylockCall(const CFGBlock *Block,
                                                 bool &Negate);

  void getEdgeLockset(
      FactSet &Result, const FactSet &ExitSet, const CFGBlock *PredBlock,
      const CFGBlock *CurrBlock,
      llvm::SmallDenseSet<AcquiredTrylockKey, 4> *AcquiredAttrs = nullptr,
      const llvm::SmallDenseSet<AcquiredTrylockKey, 4> *ConsumedAttrs =
          nullptr);
  void getAcquiredTrylockCaps(const AcquiredTrylockKey &Key, CapExprSet &Caps);

  void getTerminatorTrylockCaps(const CFGBlock *Block, CapExprSet &Caps);

  std::optional<IntDomain> getScalarDomain(QualType Ty) const;
  bool isTrackableLocalVar(
      const ValueDecl *VD,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const;
  const ValueDecl *extractTrackableVarExpr(
      const Expr *E,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const;
  void addLockToExpectedSet(FactSet &Set, const CapabilityExpr &Lock,
                            LockKind LK, SourceLocation Loc);
  bool factSetsEquivalent(const FactSet &A, const FactSet &B) const;
  std::optional<IntRangeSet>
  evaluatePureExprRange(const Expr *E, const TrylockValueState &State,
                        unsigned Depth = 0) const;
  void constrainLeafCondition(
      TrylockValueState &State, const Expr *Cond, bool WantTrue,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
      unsigned Depth = 0) const;
  void constrainValueStateOnEdge(
      TrylockValueState &State, const CFGBlock *PredBlock,
      const CFGBlock *CurrBlock,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const;
  void materializeNarrowedTrylocks(FactSet &Lockset, TrylockValueState &State);
  void updateValueStateForStmt(
      TrylockValueState &State, const Stmt *S, LocalVarContext StmtCtx,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars);
  bool isPureExitBlock(const CFGBlock *B, const CapExprSet &TargetCaps);
  bool exprHasUnmaterializedTrylock(const Expr *E, LocalVarContext Ctx,
                                    const TrylockValueState &State,
                                    bool UseStateDefs, unsigned Depth = 0);
  void evaluateReturnOutcomes(
      const Expr *E, const IntDomain &TargetDom, const FactSet &InLockset,
      const SmallVectorImpl<PendingTrylockAcquire> &InPending,
      const TrylockValueState &State, LocalVarContext Ctx, bool UseVarRanges,
      SmallVectorImpl<ReturnEvalOutcome> &Out, unsigned Depth = 0);
  void evaluateReturnOutcomesImpl(
      const Expr *E, const IntDomain &TargetDom, const FactSet &InLockset,
      const SmallVectorImpl<PendingTrylockAcquire> &InPending,
      const TrylockValueState &State, LocalVarContext Ctx, bool UseVarRanges,
      SmallVectorImpl<ReturnEvalOutcome> &Out, unsigned Depth);
  void evaluateReturnWithPendingTrylocks(
      const Expr *RetVal, const FactSet &InLockset,
      const TrylockValueState &State, LocalVarContext Ctx,
      SmallVectorImpl<ReturnEvalOutcome> &Out);
  // Trylock calls in the function being verified whose result is discarded.
  llvm::SmallPtrSet<const CallExpr *, 4> DiscardedCalls;
  void applyScopeExitCleanups(FactSet &StateSet, const CFGBlock *B,
                              bool OnlyAfterReturn = false);

  // Cache of getTrivialInlineBody() results, keyed by the callee and the
  // number of call arguments.
  mutable llvm::DenseMap<std::pair<const FunctionDecl *, unsigned>,
                         std::optional<TrivialInlineBody>>
      InlineBodyCache;
  // Functions that are being expanded inline and the expansion depth. Used to
  // prevent recursive and deeply nested inline expansion.
  mutable llvm::SmallPtrSet<const FunctionDecl *, 4> ActiveInlineCallees;
  mutable unsigned InlineDepth = 0;
  // The number of inline expansions performed for the current function.
  mutable unsigned InlineExpansionCount = 0;
  std::optional<TrivialInlineBody>
  getCachedTrivialInlineBody(const CallExpr *CallExp) const;
  void checkTrylockExitOutcome(const FactSet &BaseExpectedExitSet,
                               const ReturnEvalOutcome &Outcome,
                               SourceLocation DiagLoc,
                               ThreadSafetyHandler &ExitHandler);

  bool join(const FactEntry &A, const FactEntry &B, SourceLocation JoinLoc,
            LockErrorKind EntryLEK);

  void intersectAndWarn(FactSet &EntrySet, const FactSet &ExitSet,
                        SourceLocation JoinLoc, LockErrorKind EntryLEK,
                        LockErrorKind ExitLEK,
                        const CapExprSet *TrylockRebranchCaps = nullptr,
                        bool RebranchIgnoresDepth = false);

  void intersectAndWarn(FactSet &EntrySet, const FactSet &ExitSet,
                        SourceLocation JoinLoc, LockErrorKind LEK) {
    intersectAndWarn(EntrySet, ExitSet, JoinLoc, LEK, LEK);
  }

  void runAnalysis(AnalysisDeclContext &AC);

  void warnIfMutexNotHeld(const FactSet &FSet, const NamedDecl *D,
                          const Expr *Exp, AccessKind AK, Expr *MutexExp,
                          ProtectedOperationKind POK, til::SExpr *Self,
                          SourceLocation Loc);
  void warnIfAnyMutexNotHeldForRead(const FactSet &FSet, const NamedDecl *D,
                                    const Expr *Exp,
                                    llvm::ArrayRef<Expr *> Args,
                                    ProtectedOperationKind POK,
                                    SourceLocation Loc);
  void warnIfMutexHeld(const FactSet &FSet, const NamedDecl *D, const Expr *Exp,
                       Expr *MutexExp, til::SExpr *Self, SourceLocation Loc);

  void checkAccess(const FactSet &FSet, const Expr *Exp, AccessKind AK,
                   ProtectedOperationKind POK);
  void checkPtAccess(const FactSet &FSet, const Expr *Exp, AccessKind AK,
                     ProtectedOperationKind POK);
};

} // namespace

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
void BeforeSet::checkBeforeAfter(const ValueDecl *StartVd, const FactSet &FSet,
                                 ThreadSafetyAnalyzer &Analyzer,
                                 SourceLocation Loc, StringRef CapKind,
                                 ThreadSafetyHandler *DiagHandler) {
  ThreadSafetyHandler &OutHandler =
      DiagHandler ? *DiagHandler : Analyzer.Handler;
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
        OutHandler.handleLockAcquiredBefore(CapKind, L1, L2, Loc);
      }
      // Transitively search other before sets, and warn on cycles.
      if (traverse(Vdb)) {
        if (CycMap.try_emplace(Vd, true).second) {
          StringRef L1 = Vd->getName();
          OutHandler.handleBeforeAfterCycle(L1, Vd->getLocation());
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
    }
    else {
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
    // The mutex held is the "this" object.
    CapabilityExpr Cp = SxBuilder.translateAttrExpr(nullptr, D, Exp, Self);
    if (Cp.isInvalid()) {
      warnInvalidLock(Handler, nullptr, D, Exp, Cp.getKind());
      return;
    }
    //else
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
    //else
    if (!Cp.shouldIgnore())
      Mtxs.push_back_nodup(Cp);
  }
}

static bool evalTrylockSuccessBool(const Expr *BrE, const ASTContext &Ctx,
                                   bool &Out) {
  if (!BrE || BrE->isValueDependent() || BrE->isTypeDependent())
    return false;
  if (auto ICE = BrE->getIntegerConstantExpr(Ctx)) {
    Out = ICE->getBoolValue();
    return true;
  }
  if (BrE->EvaluateAsBooleanCondition(Out, Ctx))
    return true;
  if (const auto *BLE = dyn_cast<CXXBoolLiteralExpr>(BrE->IgnoreParenCasts())) {
    Out = BLE->getValue();
    return true;
  }
  if (const auto *ILE = dyn_cast<IntegerLiteral>(BrE->IgnoreParenCasts())) {
    Out = ILE->getValue().getBoolValue();
    return true;
  }
  return false;
}

/// Extract the list of mutexIDs from a trylock attribute.  If the
/// trylock applies to the given edge, then push them onto Mtxs, discarding
/// any duplicates.
template <class AttrType>
void ThreadSafetyAnalyzer::getMutexIDs(CapExprSet &Mtxs, AttrType *Attr,
                                       const Expr *Exp, const NamedDecl *D,
                                       const CFGBlock *PredBlock,
                                       const CFGBlock *CurrBlock,
                                       Expr *BrE, bool Neg) {
  // Find out which branch has the lock. Ignore the attribute if its success
  // value cannot be evaluated. Sema warns about such attributes.
  bool branch = false;
  if (!evalTrylockSuccessBool(BrE, *ASTCtx, branch))
    return;

  int branchnum = branch ? 0 : 1;
  if (Neg)
    branchnum = !branchnum;

  // If we've taken the trylock branch, then add the lock
  int i = 0;
  for (CFGBlock::const_succ_iterator SI = PredBlock->succ_begin(),
       SE = PredBlock->succ_end(); SI != SE && i < 2; ++SI, ++i) {
    if (*SI == CurrBlock && i == branchnum)
      getMutexIDs(Mtxs, Attr, Exp, D);
  }
}

static bool getStaticBooleanValue(Expr *E, bool &TCond) {
  if (isa<CXXNullPtrLiteralExpr>(E) || isa<GNUNullExpr>(E)) {
    TCond = false;
    return true;
  } else if (const auto *BLE = dyn_cast<CXXBoolLiteralExpr>(E)) {
    TCond = BLE->getValue();
    return true;
  } else if (const auto *ILE = dyn_cast<IntegerLiteral>(E)) {
    TCond = ILE->getValue().getBoolValue();
    return true;
  } else if (auto *CE = dyn_cast<ImplicitCastExpr>(E))
    return getStaticBooleanValue(CE->getSubExpr(), TCond);
  return false;
}

// If Cond can be traced back to a function call, return the call expression.
// The negate variable should be called with false, and will be set to true
// if the function call is negated, e.g. if (!mu.tryLock(...))
const CallExpr* ThreadSafetyAnalyzer::getTrylockCallExpr(const Stmt *Cond,
                                                         LocalVarContext C,
                                                         bool &Negate) {
  if (!Cond)
    return nullptr;

  if (const auto *CallExp = dyn_cast<CallExpr>(Cond)) {
    if (CallExp->getBuiltinCallee() == Builtin::BI__builtin_expect)
      return getTrylockCallExpr(CallExp->getArg(0), C, Negate);
    return CallExp;
  }
  else if (const auto *PE = dyn_cast<ParenExpr>(Cond))
    return getTrylockCallExpr(PE->getSubExpr(), C, Negate);
  else if (const auto *CE = dyn_cast<ImplicitCastExpr>(Cond))
    return getTrylockCallExpr(CE->getSubExpr(), C, Negate);
  else if (const auto *FE = dyn_cast<FullExpr>(Cond))
    return getTrylockCallExpr(FE->getSubExpr(), C, Negate);
  else if (const auto *DRE = dyn_cast<DeclRefExpr>(Cond)) {
    const Expr *E = LocalVarMap.lookupExpr(DRE->getDecl(), C);
    return getTrylockCallExpr(E, C, Negate);
  }
  else if (const auto *UOP = dyn_cast<UnaryOperator>(Cond)) {
    if (UOP->getOpcode() == UO_LNot) {
      Negate = !Negate;
      return getTrylockCallExpr(UOP->getSubExpr(), C, Negate);
    }
    return nullptr;
  }
  else if (const auto *BOP = dyn_cast<BinaryOperator>(Cond)) {
    if (BOP->getOpcode() == BO_EQ || BOP->getOpcode() == BO_NE) {
      if (BOP->getOpcode() == BO_NE)
        Negate = !Negate;

      bool TCond = false;
      if (getStaticBooleanValue(BOP->getRHS(), TCond)) {
        if (!TCond) Negate = !Negate;
        return getTrylockCallExpr(BOP->getLHS(), C, Negate);
      }
      TCond = false;
      if (getStaticBooleanValue(BOP->getLHS(), TCond)) {
        if (!TCond) Negate = !Negate;
        return getTrylockCallExpr(BOP->getRHS(), C, Negate);
      }
      return nullptr;
    }
    if (BOP->getOpcode() == BO_LAnd) {
      // LHS must have been evaluated in a different block.
      return getTrylockCallExpr(BOP->getRHS(), C, Negate);
    }
    if (BOP->getOpcode() == BO_LOr)
      return getTrylockCallExpr(BOP->getRHS(), C, Negate);
    return nullptr;
  } else if (const auto *COP = dyn_cast<ConditionalOperator>(Cond)) {
    bool TCond, FCond;
    if (getStaticBooleanValue(COP->getTrueExpr(), TCond) &&
        getStaticBooleanValue(COP->getFalseExpr(), FCond)) {
      if (TCond && !FCond)
        return getTrylockCallExpr(COP->getCond(), C, Negate);
      if (!TCond && FCond) {
        Negate = !Negate;
        return getTrylockCallExpr(COP->getCond(), C, Negate);
      }
    }
  } else if (const auto *SE = dyn_cast<StmtExpr>(Cond)) {
    if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
      if (const auto *E = dyn_cast<Expr>(CS->body_back()))
        return getTrylockCallExpr(E, C, Negate);
    }
  }
  return nullptr;
}

/// If the terminator of \p Block branches on the result of a call to a
/// function annotated with try_acquire_capability (possibly negated or stored
/// in a local variable), return that call and its callee. \p Negate is set if
/// the branch tests the negated result of the call. In beta mode, this leaves
/// the local variable lookup closure of SExprBuilder installed so that callers
/// can translate the callee's attribute expressions
ThreadSafetyAnalyzer::TerminatorTrylockCall
ThreadSafetyAnalyzer::getTerminatorTrylockCall(const CFGBlock *Block,
                                               bool &Negate) {
  assert(!Negate && "Must be called with Negate initialized to false");

  const Stmt *Cond = Block->getTerminatorCondition();
  if (!Cond)
    return {};

  // We don't acquire try-locks on ?: branches, except when its result is used.
  if (const auto *COp =
          dyn_cast_if_present<ConditionalOperator>(Block->getTerminatorStmt()))
    if (!COp->getType()->isVoidType())
      return {};

  const LocalVarContext &LVarCtx = BlockInfo[Block->getBlockID()].ExitContext;

  std::optional<llvm::scope_exit<std::function<void()>>> Cleanup;
  if (Handler.issueBetaWarnings()) {
    // Temporarily set the lookup context for SExprBuilder.
    SxBuilder.setLookupLocalVarExpr(
        [this, Ctx = LVarCtx](const NamedDecl *D) mutable -> const Expr * {
          return LocalVarMap.lookupExpr(D, Ctx);
        });
    Cleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
  }

  const auto *Exp = getTrylockCallExpr(Cond, LVarCtx, Negate);
  if (!Exp)
    return {};

  auto *FunDecl = dyn_cast_or_null<NamedDecl>(Exp->getCalleeDecl());
  if (!FunDecl || !FunDecl->hasAttr<TryAcquireCapabilityAttr>())
    return {};

  return {Exp, FunDecl, std::move(Cleanup)};
}

/// Find the lockset that holds on the edge between PredBlock
/// and CurrBlock.  The edge set is the exit set of PredBlock (passed
/// as the ExitSet parameter) plus any trylocks, which are conditionally held.
void ThreadSafetyAnalyzer::getEdgeLockset(
    FactSet &Result, const FactSet &ExitSet, const CFGBlock *PredBlock,
    const CFGBlock *CurrBlock,
    llvm::SmallDenseSet<AcquiredTrylockKey, 4> *AcquiredAttrs,
    const llvm::SmallDenseSet<AcquiredTrylockKey, 4> *ConsumedAttrs) {
  Result = ExitSet;

  {
    bool Negate = false;
    auto [Exp, FunDecl, Cleanup] = getTerminatorTrylockCall(PredBlock, Negate);
    if (Exp) {
      CapExprSet ExclusiveLocksToAdd;
      CapExprSet SharedLocksToAdd;

      // If the condition is a call to a Trylock function, then grab the
      // attributes
      for (const auto *Attr :
           FunDecl->specific_attrs<TryAcquireCapabilityAttr>()) {
        if (ConsumedAttrs && ConsumedAttrs->contains({Exp, Attr}))
          continue;
        CapExprSet AttrLocks;
        getMutexIDs(AttrLocks, Attr, Exp, FunDecl, PredBlock, CurrBlock,
                    Attr->getSuccessValue(), Negate);
        if (!AttrLocks.empty()) {
          if (AcquiredAttrs)
            AcquiredAttrs->insert({Exp, Attr});
          CapExprSet &Dest =
              Attr->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd;
          for (const auto &Cap : AttrLocks)
            Dest.push_back_nodup(Cap);
        }
      }

      // Add and remove locks.
      SourceLocation Loc = Exp->getExprLoc();
      for (const auto &ExclusiveLockToAdd : ExclusiveLocksToAdd)
        addLock(Result, FactMan.createFact<LockableFactEntry>(
                            ExclusiveLockToAdd, LK_Exclusive, Loc));
      for (const auto &SharedLockToAdd : SharedLocksToAdd)
        addLock(Result, FactMan.createFact<LockableFactEntry>(SharedLockToAdd,
                                                              LK_Shared, Loc));
    }
  }

  applyRangeTrylockEdge(Result, PredBlock, CurrBlock, AcquiredAttrs,
                        ConsumedAttrs);
}

/// Add the capabilities acquired by the trylock call and attribute \p Key to
/// \p Caps.
void ThreadSafetyAnalyzer::getAcquiredTrylockCaps(const AcquiredTrylockKey &Key,
                                                  CapExprSet &Caps) {
  const auto *Callee = dyn_cast_or_null<NamedDecl>(Key.first->getCalleeDecl());
  if (!Callee)
    return;
  if (const auto *A = dyn_cast<TryAcquireCapabilityAttr>(Key.second))
    getMutexIDs(Caps, A, Key.first, Callee);
  else if (const auto *A = dyn_cast<TryAcquireCapabilityRangeAttr>(Key.second))
    getMutexIDs(Caps, A, Key.first, Callee);
}

static const NamedDecl *getRangeTrylockCallee(const CallExpr *CallExp) {
  if (!CallExp || !CallExp->getType()->isIntegralOrEnumerationType())
    return nullptr;
  const auto *FunDecl = dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl());
  if (!FunDecl || !FunDecl->hasAttr<TryAcquireCapabilityRangeAttr>())
    return nullptr;
  return FunDecl;
}

static bool isValuePreservingIntegralCast(QualType SrcTy, QualType DstTy,
                                          const ASTContext &Ctx) {
  if (!SrcTy->isIntegralOrEnumerationType() ||
      !DstTy->isIntegralOrEnumerationType() || DstTy->isBooleanType())
    return false;
  // Integral promotion of an enumeration type preserves all values of that
  // enumeration, even if the promoted type is signed while the underlying type
  // is unsigned.
  if (const auto *ET = SrcTy->getAs<EnumType>())
    if (const EnumDecl *ED = ET->getDecl()->getDefinition();
        ED && Ctx.hasSameType(ED->getPromotionType(), DstTy))
      return true;
  unsigned SrcBits = Ctx.getIntWidth(SrcTy);
  unsigned DstBits = Ctx.getIntWidth(DstTy);
  if (DstBits < SrcBits)
    return false;
  bool SrcUnsigned = SrcTy->isUnsignedIntegerOrEnumerationType();
  bool DstUnsigned = DstTy->isUnsignedIntegerOrEnumerationType();
  return SrcUnsigned == DstUnsigned || (SrcUnsigned && DstBits > SrcBits);
}

ThreadSafetyAnalyzer::IntDomain
ThreadSafetyAnalyzer::IntDomain::forType(QualType Ty, const ASTContext &Ctx) {
  assert(Ty->isIntegralOrEnumerationType());
  unsigned Bits = Ctx.getIntWidth(Ty);
  bool IsUnsigned = Ty->isUnsignedIntegerOrEnumerationType();
  unsigned W = std::max(Bits + 2, 66u);
  llvm::APSInt Min = llvm::APSInt::getMinValue(Bits, IsUnsigned).extend(W);
  llvm::APSInt Max = llvm::APSInt::getMaxValue(Bits, IsUnsigned).extend(W);
  Min.setIsSigned(true);
  Max.setIsSigned(true);
  return {W, std::move(Min), std::move(Max)};
}

llvm::APSInt
ThreadSafetyAnalyzer::IntDomain::toDomainInt(const llvm::APSInt &V) const {
  unsigned TempW = std::max(V.getBitWidth() + 2, BitWidth);
  llvm::APSInt Ext = V.extend(TempW);
  Ext.setIsSigned(true);
  llvm::APSInt Res = Ext.extOrTrunc(BitWidth);
  Res.setIsSigned(true);
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::full(const IntDomain &Dom) {
  IntRangeSet S;
  S.Intervals.emplace_back(Dom.Lo, Dom.Hi);
  return S;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::closedRange(const IntDomain &Dom,
                                               const llvm::APSInt &First,
                                               const llvm::APSInt &Last) {
  if (llvm::APSInt::compareValues(First, Last) > 0 ||
      llvm::APSInt::compareValues(Last, Dom.Lo) < 0 ||
      llvm::APSInt::compareValues(First, Dom.Hi) > 0)
    return {};
  llvm::APSInt ClampedLo = llvm::APSInt::compareValues(First, Dom.Lo) <= 0
                               ? Dom.Lo
                               : Dom.toDomainInt(First);
  llvm::APSInt ClampedHi = llvm::APSInt::compareValues(Last, Dom.Hi) >= 0
                               ? Dom.Hi
                               : Dom.toDomainInt(Last);
  IntRangeSet S;
  S.Intervals.emplace_back(std::move(ClampedLo), std::move(ClampedHi));
  return S;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::single(const IntDomain &Dom,
                                          const llvm::APSInt &Val) {
  return closedRange(Dom, Val, Val);
}

static llvm::APSInt incAPSInt(llvm::APSInt V) {
  ++V;
  return V;
}

static llvm::APSInt decAPSInt(llvm::APSInt V) {
  --V;
  return V;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::forComparison(const IntDomain &Dom,
                                                 BinaryOperator::Opcode Opc,
                                                 const llvm::APSInt &K) {
  switch (Opc) {
  case BO_EQ:
    return single(Dom, K);
  case BO_NE:
    return single(Dom, K).complement(Dom);
  case BO_LT:
    if (llvm::APSInt::compareValues(K, Dom.Lo) <= 0)
      return {};
    if (llvm::APSInt::compareValues(K, Dom.Hi) > 0)
      return full(Dom);
    {
      IntRangeSet S;
      S.Intervals.emplace_back(Dom.Lo, decAPSInt(Dom.toDomainInt(K)));
      return S;
    }
  case BO_LE:
    return closedRange(Dom, Dom.Lo, K);
  case BO_GT:
    if (llvm::APSInt::compareValues(K, Dom.Hi) >= 0)
      return {};
    if (llvm::APSInt::compareValues(K, Dom.Lo) < 0)
      return full(Dom);
    {
      IntRangeSet S;
      S.Intervals.emplace_back(incAPSInt(Dom.toDomainInt(K)), Dom.Hi);
      return S;
    }
  case BO_GE:
    return closedRange(Dom, K, Dom.Hi);
  default:
    llvm_unreachable("Unexpected comparison opcode");
  }
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::complement(const IntDomain &Dom) const {
  if (Intervals.empty())
    return full(Dom);
  IntRangeSet Res;
  llvm::APSInt Cursor = Dom.Lo;
  for (const auto &[Lo, Hi] : Intervals) {
    if (Cursor < Lo)
      Res.Intervals.emplace_back(Cursor, decAPSInt(Lo));
    Cursor = incAPSInt(Hi);
  }
  if (Cursor <= Dom.Hi)
    Res.Intervals.emplace_back(Cursor, Dom.Hi);
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::intersect(const IntRangeSet &Other) const {
  IntRangeSet Res;
  size_t I = 0, J = 0;
  while (I < Intervals.size() && J < Other.Intervals.size()) {
    const llvm::APSInt &Lo =
        std::max(Intervals[I].first, Other.Intervals[J].first);
    const llvm::APSInt &Hi =
        std::min(Intervals[I].second, Other.Intervals[J].second);
    if (Lo <= Hi)
      Res.Intervals.emplace_back(Lo, Hi);
    if (Intervals[I].second < Other.Intervals[J].second)
      ++I;
    else
      ++J;
  }
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::unionWith(const IntRangeSet &Other) const {
  IntRangeSet Res;
  auto Append = [&Res](const std::pair<llvm::APSInt, llvm::APSInt> &Iv) {
    if (Res.Intervals.empty() ||
        incAPSInt(Res.Intervals.back().second) < Iv.first)
      Res.Intervals.push_back(Iv);
    else if (Res.Intervals.back().second < Iv.second)
      Res.Intervals.back().second = Iv.second;
  };
  size_t I = 0, J = 0;
  while (I < Intervals.size() && J < Other.Intervals.size()) {
    if (Intervals[I].first <= Other.Intervals[J].first)
      Append(Intervals[I++]);
    else
      Append(Other.Intervals[J++]);
  }
  while (I < Intervals.size())
    Append(Intervals[I++]);
  while (J < Other.Intervals.size())
    Append(Other.Intervals[J++]);
  return Res;
}

ThreadSafetyAnalyzer::IntRangeSet
ThreadSafetyAnalyzer::IntRangeSet::unionAll(ArrayRef<IntRangeSet> Sets) {
  SmallVector<std::pair<llvm::APSInt, llvm::APSInt>, 8> All;
  for (const IntRangeSet &S : Sets)
    llvm::append_range(All, S.Intervals);
  llvm::sort(All, [](const auto &A, const auto &B) {
    return llvm::APSInt::compareValues(A.first, B.first) < 0;
  });
  IntRangeSet Res;
  for (const auto &Iv : All) {
    if (Res.Intervals.empty() ||
        incAPSInt(Res.Intervals.back().second) < Iv.first)
      Res.Intervals.push_back(Iv);
    else if (Res.Intervals.back().second < Iv.second)
      Res.Intervals.back().second = Iv.second;
  }
  return Res;
}

const ThreadSafetyAnalyzer::SwitchCaseTable &
ThreadSafetyAnalyzer::getSwitchCaseTable(const SwitchStmt *SS,
                                         const IntDomain &Dom) const {
  auto &Entries = SwitchTables[SS];
  for (auto &[EDom, Table] : Entries)
    if (EDom.BitWidth == Dom.BitWidth &&
        llvm::APSInt::compareValues(EDom.Lo, Dom.Lo) == 0 &&
        llvm::APSInt::compareValues(EDom.Hi, Dom.Hi) == 0)
      return Table;

  SwitchCaseTable Table;
  Table.Valid = true;
  SmallVector<IntRangeSet, 8> AllCases;
  for (const SwitchCase *SC = SS->getSwitchCaseList(); SC;
       SC = SC->getNextSwitchCase()) {
    const auto *CS = dyn_cast<CaseStmt>(SC);
    if (!CS)
      continue;
    auto Lo = CS->getLHS()->getIntegerConstantExpr(*ASTCtx);
    auto Hi = CS->getRHS() ? CS->getRHS()->getIntegerConstantExpr(*ASTCtx) : Lo;
    if (!Lo || !Hi) {
      Table.Valid = false;
      break;
    }
    IntRangeSet CaseSet = IntRangeSet::closedRange(Dom, *Lo, *Hi);
    AllCases.push_back(CaseSet);
    Table.CaseSets.try_emplace(CS, std::move(CaseSet));
  }
  if (Table.Valid)
    Table.DefaultSet = IntRangeSet::unionAll(AllCases).complement(Dom);
  else
    Table.CaseSets.clear();
  Entries.emplace_back(Dom, std::move(Table));
  return Entries.back().second;
}

bool ThreadSafetyAnalyzer::IntRangeSet::subsetOf(
    const llvm::APSInt &First, const llvm::APSInt &Last) const {
  return !Intervals.empty() &&
         llvm::APSInt::compareValues(Intervals.front().first, First) >= 0 &&
         llvm::APSInt::compareValues(Intervals.back().second, Last) <= 0;
}

bool ThreadSafetyAnalyzer::IntRangeSet::intersects(
    const llvm::APSInt &First, const llvm::APSInt &Last) const {
  return llvm::any_of(Intervals, [&](const auto &Iv) {
    return llvm::APSInt::compareValues(Iv.second, First) >= 0 &&
           llvm::APSInt::compareValues(Iv.first, Last) <= 0;
  });
}

bool ThreadSafetyAnalyzer::IntRangeSet::subsetOfSet(
    const IntRangeSet &Other) const {
  if (Intervals.empty())
    return true;
  if (Other.Intervals.empty())
    return false;
  size_t J = 0;
  for (const auto &[Lo, Hi] : Intervals) {
    while (J < Other.Intervals.size() && Other.Intervals[J].second < Lo)
      ++J;
    if (J == Other.Intervals.size() || Other.Intervals[J].first > Lo ||
        Other.Intervals[J].second < Hi)
      return false;
  }
  return true;
}

bool ThreadSafetyAnalyzer::IntRangeSet::intersectsSet(
    const IntRangeSet &Other) const {
  size_t I = 0, J = 0;
  while (I < Intervals.size() && J < Other.Intervals.size()) {
    if (Intervals[I].second < Other.Intervals[J].first)
      ++I;
    else if (Other.Intervals[J].second < Intervals[I].first)
      ++J;
    else
      return true;
  }
  return false;
}

bool ThreadSafetyAnalyzer::IntRangeSet::isSingleValue(llvm::APSInt &Val) const {
  if (Intervals.size() != 1 || Intervals[0].first != Intervals[0].second)
    return false;
  Val = Intervals[0].first;
  return true;
}

const CallExpr *
ThreadSafetyAnalyzer::unwrapTrylockValueExpr(const Expr *E, LocalVarContext C) {
  while (E) {
    if (const auto *PE = dyn_cast<ParenExpr>(E)) {
      E = PE->getSubExpr();
      continue;
    }
    if (const auto *FE = dyn_cast<FullExpr>(E)) {
      E = FE->getSubExpr();
      continue;
    }
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      switch (CE->getCastKind()) {
      case CK_LValueToRValue:
      case CK_NoOp:
        E = CE->getSubExpr();
        continue;
      case CK_IntegralCast:
        if (isValuePreservingIntegralCast(CE->getSubExpr()->getType(),
                                          CE->getType(), *ASTCtx)) {
          E = CE->getSubExpr();
          continue;
        }
        return nullptr;
      default:
        return nullptr;
      }
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      E = LocalVarMap.lookupExpr(DRE->getDecl(), C);
      continue;
    }
    if (const auto *BOP = dyn_cast<BinaryOperator>(E)) {
      if (BOP->getOpcode() == BO_Assign && !BOP->getLHS()->refersToBitField()) {
        E = BOP->getRHS();
        continue;
      }
      return nullptr;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(E)) {
      if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
        E = dyn_cast<Expr>(CS->body_back());
        continue;
      }
      return nullptr;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      unsigned BuiltinID = CallExp->getBuiltinCallee();
      if (BuiltinID == Builtin::BI__builtin_expect ||
          BuiltinID == Builtin::BI__builtin_expect_with_probability) {
        E = CallExp->getArg(0);
        continue;
      }
      return getRangeTrylockCallee(CallExp) ? CallExp : nullptr;
    }
    return nullptr;
  }
  return nullptr;
}

bool ThreadSafetyAnalyzer::isGuaranteedZeroOrOneExpr(const Expr *E,
                                                     LocalVarContext C) {
  while (E) {
    if (E->getType()->isBooleanType())
      return true;
    if (const auto *PE = dyn_cast<ParenExpr>(E)) {
      E = PE->getSubExpr();
      continue;
    }
    if (const auto *FE = dyn_cast<FullExpr>(E)) {
      E = FE->getSubExpr();
      continue;
    }
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (CE->getCastKind() == CK_LValueToRValue ||
          CE->getCastKind() == CK_NoOp ||
          (CE->getCastKind() == CK_IntegralCast &&
           isValuePreservingIntegralCast(CE->getSubExpr()->getType(),
                                         CE->getType(), *ASTCtx))) {
        E = CE->getSubExpr();
        continue;
      }
      return false;
    }
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      E = LocalVarMap.lookupExpr(DRE->getDecl(), C);
      continue;
    }
    if (const auto *SE = dyn_cast<StmtExpr>(E)) {
      if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
        E = dyn_cast<Expr>(CS->body_back());
        continue;
      }
      return false;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      unsigned BuiltinID = CallExp->getBuiltinCallee();
      if (BuiltinID == Builtin::BI__builtin_expect ||
          BuiltinID == Builtin::BI__builtin_expect_with_probability) {
        E = CallExp->getArg(0);
        continue;
      }
      return false;
    }
    if (const auto *UOP = dyn_cast<UnaryOperator>(E))
      return UOP->getOpcode() == UO_LNot;
    if (const auto *BOP = dyn_cast<BinaryOperator>(E)) {
      if (BOP->getOpcode() == BO_Assign && !BOP->getLHS()->refersToBitField()) {
        E = BOP->getRHS();
        continue;
      }
      return BOP->isComparisonOp() || BOP->isLogicalOp();
    }
    return false;
  }
  return false;
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockRangeCond(const Stmt *Cond,
                                               LocalVarContext C) {
  if (!Cond)
    return {};
  std::pair<const Stmt *, const void *> Key(Cond, C.getRootWithoutRetain());
  if (auto It = RangeCondCache.find(Key); It != RangeCondCache.end())
    return It->second;
  TrylockRangeCondResult Res = evaluateTrylockRangeCondImpl(Cond, C);
  RangeCondCache.try_emplace(Key, Res);
  return Res;
}

ThreadSafetyAnalyzer::TrylockRangeCondResult
ThreadSafetyAnalyzer::evaluateTrylockRangeCondImpl(const Stmt *Cond,
                                                   LocalVarContext C) {
  if (!Cond)
    return {};

  if (const auto *PE = dyn_cast<ParenExpr>(Cond))
    return evaluateTrylockRangeCond(PE->getSubExpr(), C);
  if (const auto *FE = dyn_cast<FullExpr>(Cond))
    return evaluateTrylockRangeCond(FE->getSubExpr(), C);

  if (const auto *CE = dyn_cast<CastExpr>(Cond)) {
    switch (CE->getCastKind()) {
    case CK_LValueToRValue:
    case CK_NoOp:
    case CK_IntegralToBoolean:
      return evaluateTrylockRangeCond(CE->getSubExpr(), C);
    case CK_IntegralCast:
      if (isValuePreservingIntegralCast(CE->getSubExpr()->getType(),
                                        CE->getType(), *ASTCtx))
        return evaluateTrylockRangeCond(CE->getSubExpr(), C);
      return {};
    default:
      return {};
    }
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(Cond)) {
    const Expr *E = LocalVarMap.lookupExpr(DRE->getDecl(), C);
    return evaluateTrylockRangeCond(E, C);
  }

  if (const auto *SE = dyn_cast<StmtExpr>(Cond)) {
    if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty())
      if (const auto *E = dyn_cast<Expr>(CS->body_back()))
        return evaluateTrylockRangeCond(E, C);
    return {};
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(Cond)) {
    unsigned BuiltinID = CallExp->getBuiltinCallee();
    if (BuiltinID == Builtin::BI__builtin_expect ||
        BuiltinID == Builtin::BI__builtin_expect_with_probability)
      return evaluateTrylockRangeCond(CallExp->getArg(0), C);

    if (const NamedDecl *Callee = getRangeTrylockCallee(CallExp)) {
      IntDomain Dom = IntDomain::forType(CallExp->getType(), *ASTCtx);
      IntRangeSet FalseSet = IntRangeSet::single(Dom, llvm::APSInt::get(0));
      IntRangeSet TrueSet = FalseSet.complement(Dom);
      return {CallExp, Callee, std::move(Dom), std::move(TrueSet),
              std::move(FalseSet)};
    }
    return {};
  }

  if (const auto *UOP = dyn_cast<UnaryOperator>(Cond)) {
    if (UOP->getOpcode() == UO_LNot) {
      auto Res = evaluateTrylockRangeCond(UOP->getSubExpr(), C);
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
      return evaluateTrylockRangeCond(BOP->getRHS(), C);
    }

    if (BOP->isComparisonOp()) {
      const CallExpr *CallExp = nullptr;
      BinaryOperator::Opcode CmpOp = BOP->getOpcode();
      std::optional<llvm::APSInt> ConstVal;
      if (const CallExpr *LHSVal = unwrapTrylockValueExpr(BOP->getLHS(), C)) {
        ConstVal = BOP->getRHS()->getIntegerConstantExpr(*ASTCtx);
        if (ConstVal)
          CallExp = LHSVal;
      }
      if (!CallExp) {
        if (const CallExpr *RHSVal = unwrapTrylockValueExpr(BOP->getRHS(), C)) {
          ConstVal = BOP->getLHS()->getIntegerConstantExpr(*ASTCtx);
          if (ConstVal) {
            CallExp = RHSVal;
            CmpOp = BinaryOperator::reverseComparisonOp(CmpOp);
          }
        }
      }
      if (CallExp && ConstVal) {
        const NamedDecl *Callee = getRangeTrylockCallee(CallExp);
        IntDomain Dom = IntDomain::forType(CallExp->getType(), *ASTCtx);
        IntRangeSet TrueSet = IntRangeSet::forComparison(Dom, CmpOp, *ConstVal);
        IntRangeSet FalseSet = TrueSet.complement(Dom);
        return {CallExp, Callee, std::move(Dom), std::move(TrueSet),
                std::move(FalseSet)};
      }

      if (BOP->getOpcode() == BO_EQ || BOP->getOpcode() == BO_NE) {
        auto EvalBoolEq = [&](const Expr *BoolSide,
                              const Expr *ConstSide) -> TrylockRangeCondResult {
          auto K = ConstSide->getIntegerConstantExpr(*ASTCtx);
          if (!K || !isGuaranteedZeroOrOneExpr(BoolSide, C))
            return {};
          auto Res = evaluateTrylockRangeCond(BoolSide, C);
          if (!Res.Call)
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
        };
        if (auto Res = EvalBoolEq(BOP->getLHS(), BOP->getRHS()); Res.Call)
          return Res;
        if (auto Res = EvalBoolEq(BOP->getRHS(), BOP->getLHS()); Res.Call)
          return Res;
      }
      return {};
    }

    if (BOP->getOpcode() == BO_LAnd || BOP->getOpcode() == BO_LOr) {
      auto RHSRes = evaluateTrylockRangeCond(BOP->getRHS(), C);
      if (!RHSRes.Call)
        return {};
      auto LHSRes = evaluateTrylockRangeCond(BOP->getLHS(), C);
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
    return {};
  }

  if (const auto *COP = dyn_cast<ConditionalOperator>(Cond)) {
    bool TCond, FCond;
    if (getStaticBooleanValue(COP->getTrueExpr(), TCond) &&
        getStaticBooleanValue(COP->getFalseExpr(), FCond)) {
      if (TCond && !FCond)
        return evaluateTrylockRangeCond(COP->getCond(), C);
      if (!TCond && FCond) {
        auto Res = evaluateTrylockRangeCond(COP->getCond(), C);
        if (Res.Call)
          std::swap(Res.TrueSet, Res.FalseSet);
        return Res;
      }
    }
    return {};
  }

  return {};
}

void ThreadSafetyAnalyzer::applyRangeTrylockEdge(
    FactSet &Result, const CFGBlock *PredBlock, const CFGBlock *CurrBlock,
    llvm::SmallDenseSet<AcquiredTrylockKey, 4> *AcquiredAttrs,
    const llvm::SmallDenseSet<AcquiredTrylockKey, 4> *ConsumedAttrs) {
  const Stmt *Term = PredBlock->getTerminatorStmt();
  if (!Term || isa<IndirectGotoStmt>(Term))
    return;

  if (const auto *COp = dyn_cast<ConditionalOperator>(Term))
    if (!COp->getType()->isVoidType())
      return;
  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(Term))
    if (!BCO->getType()->isVoidType())
      return;

  const LocalVarContext &LVarCtx =
      BlockInfo[PredBlock->getBlockID()].ExitContext;
  const CallExpr *CallExp = nullptr;
  const NamedDecl *Callee = nullptr;
  IntRangeSet EdgeSet;

  if (const auto *SS = dyn_cast<SwitchStmt>(Term)) {
    CallExp = unwrapTrylockValueExpr(SS->getCond(), LVarCtx);
    if (!CallExp)
      return;
    Callee = getRangeTrylockCallee(CallExp);
    if (!Callee)
      return;
    IntDomain Dom = IntDomain::forType(CallExp->getType(), *ASTCtx);
    const SwitchCaseTable &Table = getSwitchCaseTable(SS, Dom);
    if (!Table.Valid)
      return;
    const auto *TargetCS = dyn_cast_if_present<CaseStmt>(CurrBlock->getLabel());
    if (auto It = Table.CaseSets.find(TargetCS); It != Table.CaseSets.end()) {
      EdgeSet = It->second;
    } else {
      if (!isa_and_nonnull<DefaultStmt>(CurrBlock->getLabel()) &&
          SS->isAllEnumCasesCovered())
        return;
      EdgeSet = Table.DefaultSet;
    }
  } else {
    const Stmt *Cond = PredBlock->getTerminatorCondition();
    if (!Cond)
      return;
    auto CondRes = evaluateTrylockRangeCond(Cond, LVarCtx);
    if (!CondRes.Call)
      return;
    CallExp = CondRes.Call;
    Callee = CondRes.Callee;
    int BranchIdx = 0;
    for (auto SI = PredBlock->succ_begin(), SE = PredBlock->succ_end();
         SI != SE && BranchIdx < 2; ++SI, ++BranchIdx) {
      if (*SI == CurrBlock) {
        EdgeSet = EdgeSet.unionWith(BranchIdx == 0 ? CondRes.TrueSet
                                                   : CondRes.FalseSet);
      }
    }
  }

  if (EdgeSet.empty())
    return;

  std::optional<llvm::scope_exit<std::function<void()>>> Cleanup;
  if (Handler.issueBetaWarnings()) {
    SxBuilder.setLookupLocalVarExpr(
        [this, Ctx = LVarCtx](const NamedDecl *D) mutable -> const Expr * {
          return LocalVarMap.lookupExpr(D, Ctx);
        });
    Cleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
  }

  CapExprSet ExclusiveLocksToAdd;
  CapExprSet SharedLocksToAdd;
  for (const auto *Attr :
       Callee->specific_attrs<TryAcquireCapabilityRangeAttr>()) {
    if (!Attr->getFirstSuccessValue() || !Attr->getLastSuccessValue())
      continue;
    auto First = Attr->getFirstSuccessValue()->getIntegerConstantExpr(*ASTCtx);
    auto Last = Attr->getLastSuccessValue()->getIntegerConstantExpr(*ASTCtx);
    if (!First || !Last)
      continue;
    if (EdgeSet.subsetOf(*First, *Last)) {
      if (ConsumedAttrs && ConsumedAttrs->contains({CallExp, Attr}))
        continue;
      CapExprSet AttrLocks;
      getMutexIDs(AttrLocks, Attr, CallExp, Callee);
      if (!AttrLocks.empty()) {
        if (AcquiredAttrs)
          AcquiredAttrs->insert({CallExp, Attr});
        CapExprSet &Dest =
            Attr->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd;
        for (const auto &Cap : AttrLocks)
          Dest.push_back_nodup(Cap);
      }
    }
  }

  auto AddTrylockFact = [&](const CapabilityExpr &Cap, LockKind LK,
                            SourceLocation Loc) {
    const FactEntry *Existing = Result.findLock(FactMan, Cap);
    if (Existing && Existing->loc() == Loc && !Existing->asserted()) {
      // The fact comes from the same trylock call, e.g. because a join kept
      // the shared fact of a call that acquires the capability exclusively
      // for other return values. Refine the lock kind instead of reporting a
      // double acquisition.
      if (Existing->kind() != LK)
        Result.replaceLock(FactMan, Cap,
                           FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
      return;
    }
    addLock(Result, FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
  };

  SourceLocation Loc = CallExp->getExprLoc();
  for (const auto &ExclusiveLockToAdd : ExclusiveLocksToAdd)
    AddTrylockFact(ExclusiveLockToAdd, LK_Exclusive, Loc);
  for (const auto &SharedLockToAdd : SharedLocksToAdd)
    AddTrylockFact(SharedLockToAdd, LK_Shared, Loc);
}

void ThreadSafetyAnalyzer::getRangeTerminatorTrylockCaps(const CFGBlock *Block,
                                                         CapExprSet &Caps) {
  const Stmt *Term = Block->getTerminatorStmt();
  if (!Term || isa<IndirectGotoStmt>(Term))
    return;
  if (const auto *COp = dyn_cast<ConditionalOperator>(Term))
    if (!COp->getType()->isVoidType())
      return;
  if (const auto *BCO = dyn_cast<BinaryConditionalOperator>(Term))
    if (!BCO->getType()->isVoidType())
      return;

  const LocalVarContext &LVarCtx = BlockInfo[Block->getBlockID()].ExitContext;
  const CallExpr *CallExp = nullptr;
  const NamedDecl *Callee = nullptr;
  SmallVector<IntRangeSet, 4> BranchSets;

  if (const auto *SS = dyn_cast<SwitchStmt>(Term)) {
    CallExp = unwrapTrylockValueExpr(SS->getCond(), LVarCtx);
    if (!CallExp)
      return;
    Callee = getRangeTrylockCallee(CallExp);
    if (!Callee)
      return;
    IntDomain Dom = IntDomain::forType(CallExp->getType(), *ASTCtx);
    const SwitchCaseTable &Table = getSwitchCaseTable(SS, Dom);
    if (!Table.Valid)
      return;
    for (const auto &[CS, CaseSet] : Table.CaseSets)
      BranchSets.push_back(CaseSet);
    BranchSets.push_back(Table.DefaultSet);
  } else {
    const Stmt *Cond = Block->getTerminatorCondition();
    if (!Cond)
      return;
    auto CondRes = evaluateTrylockRangeCond(Cond, LVarCtx);
    if (!CondRes.Call)
      return;
    CallExp = CondRes.Call;
    Callee = CondRes.Callee;
    BranchSets.push_back(std::move(CondRes.TrueSet));
    BranchSets.push_back(std::move(CondRes.FalseSet));
  }

  std::optional<llvm::scope_exit<std::function<void()>>> Cleanup;
  if (Handler.issueBetaWarnings()) {
    SxBuilder.setLookupLocalVarExpr(
        [this, Ctx = LVarCtx](const NamedDecl *D) mutable -> const Expr * {
          return LocalVarMap.lookupExpr(D, Ctx);
        });
    Cleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
  }

  for (const auto *Attr :
       Callee->specific_attrs<TryAcquireCapabilityRangeAttr>()) {
    if (!Attr->getFirstSuccessValue() || !Attr->getLastSuccessValue())
      continue;
    auto First = Attr->getFirstSuccessValue()->getIntegerConstantExpr(*ASTCtx);
    auto Last = Attr->getLastSuccessValue()->getIntegerConstantExpr(*ASTCtx);
    if (!First || !Last)
      continue;
    bool CleanPartition = llvm::all_of(BranchSets, [&](const IntRangeSet &S) {
      return S.empty() || S.subsetOf(*First, *Last) ||
             !S.intersects(*First, *Last);
    });
    if (CleanPartition)
      getMutexIDs(Caps, Attr, CallExp, Callee);
  }
}

/// If the terminator of \p Block branches on the result of a try-lock call
/// (possibly stored in a local variable), add the capabilities acquired by
/// that call to \p Caps.
void ThreadSafetyAnalyzer::getTerminatorTrylockCaps(const CFGBlock *Block,
                                                    CapExprSet &Caps) {
  {
    bool Negate = false;
    auto [Exp, FunDecl, Cleanup] = getTerminatorTrylockCall(Block, Negate);
    if (Exp) {
      for (const auto *Attr :
           FunDecl->specific_attrs<TryAcquireCapabilityAttr>())
        getMutexIDs(Caps, Attr, Exp, FunDecl);
    }
  }
  getRangeTerminatorTrylockCaps(Block, Caps);
}

namespace {

/// Wrapper around ThreadSafetyHandler that deduplicates diagnostics emitted
/// while verifying multiple return outcomes/partitions at function exit. Every
/// callback is forwarded to the wrapped handler unless an identical callback
/// has already been forwarded.
class DedupThreadSafetyHandler final : public ThreadSafetyHandler {
  ThreadSafetyHandler &Inner;
  llvm::StringSet<> Emitted;

  // Append a length-prefixed encoding of each argument to Key such that
  // different argument lists never produce the same key.
  static void encode(std::string &Key, StringRef Str) {
    Key += std::to_string(Str.size());
    Key += ':';
    Key += Str;
  }
  static void encode(std::string &Key, SourceLocation Loc) {
    encode(Key, std::to_string(Loc.getRawEncoding()));
  }
  static void encode(std::string &Key, const void *Ptr) {
    encode(Key, std::to_string(reinterpret_cast<uintptr_t>(Ptr)));
  }
  static void encode(std::string &Key, unsigned long long Val) {
    encode(Key, std::to_string(Val));
  }
  static void encode(std::string &Key, const Name *N) {
    encode(Key, N ? StringRef(*N) : StringRef("<null>"));
  }
  static void encode(std::string &Key, ArrayRef<StringRef> Names) {
    encode(Key, static_cast<unsigned long long>(Names.size()));
    for (StringRef N : Names)
      encode(Key, N);
  }

  template <typename... Ts>
  bool shouldEmit(StringRef Callback, const Ts &...Args) {
    std::string Key;
    encode(Key, Callback);
    (encode(Key, Args), ...);
    return Emitted.insert(Key).second;
  }

  template <typename E> static unsigned long long val(E V) {
    return static_cast<unsigned long long>(V);
  }

public:
  explicit DedupThreadSafetyHandler(ThreadSafetyHandler &Inner) : Inner(Inner) {
    setIssueBetaWarnings(Inner.issueBetaWarnings());
  }

  void handleInvalidLockExp(SourceLocation Loc) override {
    if (shouldEmit("InvalidLockExp", Loc))
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
    if (shouldEmit("IncorrectUnlockKind", Kind, LockName, val(Expected),
                   val(Received), LocLocked, LocUnlock))
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
    if (shouldEmit("NoMutexHeld", static_cast<const void *>(D), val(POK),
                   val(AK), Loc))
      Inner.handleNoMutexHeld(D, POK, AK, Loc);
  }

  void handleGuardedByAnyReadNotHeld(const NamedDecl *D,
                                     ProtectedOperationKind POK,
                                     ArrayRef<StringRef> LockNames,
                                     SourceLocation Loc) override {
    if (shouldEmit("GuardedByAnyReadNotHeld", static_cast<const void *>(D),
                   val(POK), LockNames, Loc))
      Inner.handleGuardedByAnyReadNotHeld(D, POK, LockNames, Loc);
  }

  void handleMutexNotHeld(StringRef Kind, const NamedDecl *D,
                          ProtectedOperationKind POK, Name LockName,
                          LockKind LK, SourceLocation Loc,
                          Name *PossibleMatch = nullptr) override {
    if (shouldEmit("MutexNotHeld", Kind, static_cast<const void *>(D),
                   val(POK), LockName, val(LK), Loc,
                   static_cast<const Name *>(PossibleMatch)))
      Inner.handleMutexNotHeld(Kind, D, POK, LockName, LK, Loc, PossibleMatch);
  }

  void handleNegativeNotHeld(StringRef Kind, Name LockName, Name Neg,
                             SourceLocation Loc) override {
    if (shouldEmit("NegativeNotHeld", Kind, LockName, Neg, Loc))
      Inner.handleNegativeNotHeld(Kind, LockName, Neg, Loc);
  }

  void handleNegativeNotHeld(const NamedDecl *D, Name LockName,
                             SourceLocation Loc) override {
    if (shouldEmit("NegativeNotHeldDecl", static_cast<const void *>(D),
                   LockName, Loc))
      Inner.handleNegativeNotHeld(D, LockName, Loc);
  }

  void handleFunExcludesLock(StringRef Kind, Name FunName, Name LockName,
                             SourceLocation Loc) override {
    if (shouldEmit("FunExcludesLock", Kind, FunName, LockName, Loc))
      Inner.handleFunExcludesLock(Kind, FunName, LockName, Loc);
  }

  void handleUnmatchedUnderlyingMutexes(SourceLocation Loc, SourceLocation DLoc,
                                        Name ScopeName, StringRef Kind,
                                        Name Expected, Name Actual) override {
    if (shouldEmit("UnmatchedUnderlyingMutexes", Loc, DLoc, ScopeName, Kind,
                   Expected, Actual))
      Inner.handleUnmatchedUnderlyingMutexes(Loc, DLoc, ScopeName, Kind,
                                             Expected, Actual);
  }

  void handleExpectMoreUnderlyingMutexes(SourceLocation Loc,
                                         SourceLocation DLoc, Name ScopeName,
                                         StringRef Kind,
                                         Name Expected) override {
    if (shouldEmit("ExpectMoreUnderlyingMutexes", Loc, DLoc, ScopeName, Kind,
                   Expected))
      Inner.handleExpectMoreUnderlyingMutexes(Loc, DLoc, ScopeName, Kind,
                                              Expected);
  }

  void handleExpectFewerUnderlyingMutexes(SourceLocation Loc,
                                          SourceLocation DLoc, Name ScopeName,
                                          StringRef Kind,
                                          Name Actual) override {
    if (shouldEmit("ExpectFewerUnderlyingMutexes", Loc, DLoc, ScopeName, Kind,
                   Actual))
      Inner.handleExpectFewerUnderlyingMutexes(Loc, DLoc, ScopeName, Kind,
                                               Actual);
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

  void enterFunction(const FunctionDecl *FD) override {
    Inner.enterFunction(FD);
  }

  void leaveFunction(const FunctionDecl *FD) override {
    Inner.leaveFunction(FD);
  }
};

} // namespace

static const Expr *stripNoOpExprWrappers(const Expr *E) {
  while (E) {
    if (const auto *PE = dyn_cast<ParenExpr>(E)) {
      E = PE->getSubExpr();
      continue;
    }
    if (const auto *FE = dyn_cast<FullExpr>(E)) {
      E = FE->getSubExpr();
      continue;
    }
    if (const auto *OVE = dyn_cast<OpaqueValueExpr>(E)) {
      if (const Expr *Src = OVE->getSourceExpr()) {
        E = Src;
        continue;
      }
      break;
    }
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (CE->getCastKind() == CK_NoOp) {
        E = CE->getSubExpr();
        continue;
      }
    }
    break;
  }
  return E;
}

static const DeclRefExpr *unwrapDirectLValueDRE(const Expr *E) {
  while (E) {
    if (const auto *PE = dyn_cast<ParenExpr>(E)) {
      E = PE->getSubExpr();
      continue;
    }
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      if (CE->getCastKind() == CK_NoOp) {
        E = CE->getSubExpr();
        continue;
      }
    }
    break;
  }
  return dyn_cast_or_null<DeclRefExpr>(E);
}

static void
scanTrylockVars(const Stmt *Root,
                llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
                llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars) {
  if (!Root)
    return;

  llvm::SmallPtrSet<const DeclRefExpr *, 16> SafeDREs;
  auto VisitNode = [&](auto &Self, const Stmt *S,
                       bool InNestedClosure) -> void {
    if (!S)
      return;

    if (const auto *LE = dyn_cast<LambdaExpr>(S)) {
      for (const LambdaCapture &Cap : LE->captures()) {
        if (Cap.capturesVariable() && Cap.getCaptureKind() == LCK_ByRef) {
          const ValueDecl *VD =
              cast<ValueDecl>(Cap.getCapturedVar()->getCanonicalDecl());
          EscapedVars.insert(VD);
          ModifiedVars.insert(VD);
        }
      }
      InNestedClosure = true;
    } else if (const auto *BE = dyn_cast<BlockExpr>(S)) {
      // The body of a block is not a child of the BlockExpr. Variables
      // captured by reference (__block variables) may be modified whenever
      // the block runs.
      for (const BlockDecl::Capture &Cap : BE->getBlockDecl()->captures()) {
        if (Cap.isByRef()) {
          const ValueDecl *VD =
              cast<ValueDecl>(Cap.getVariable()->getCanonicalDecl());
          EscapedVars.insert(VD);
          ModifiedVars.insert(VD);
        }
      }
      InNestedClosure = true;
    } else if (isa<CapturedStmt>(S)) {
      InNestedClosure = true;
    }

    if (!InNestedClosure) {
      if (const auto *CE = dyn_cast<CastExpr>(S)) {
        if (CE->getCastKind() == CK_LValueToRValue)
          if (const auto *DRE = unwrapDirectLValueDRE(CE->getSubExpr()))
            SafeDREs.insert(DRE);
      } else if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
        if (BO->isAssignmentOp()) {
          if (const auto *DRE = unwrapDirectLValueDRE(BO->getLHS())) {
            SafeDREs.insert(DRE);
            ModifiedVars.insert(
                cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
          }
        }
      } else if (const auto *UO = dyn_cast<UnaryOperator>(S)) {
        if (UO->isIncrementDecrementOp()) {
          if (const auto *DRE = unwrapDirectLValueDRE(UO->getSubExpr())) {
            SafeDREs.insert(DRE);
            ModifiedVars.insert(
                cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
          }
        }
      }
    }

    if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
      if (InNestedClosure || !SafeDREs.contains(DRE)) {
        const ValueDecl *VD =
            cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
        EscapedVars.insert(VD);
        ModifiedVars.insert(VD);
      }
    }

    // Note: DeclStmt::children() includes the variable initializers.
    for (const Stmt *Child : S->children())
      if (Child)
        Self(Self, Child, InNestedClosure);
  };

  VisitNode(VisitNode, Root, /*InNestedClosure=*/false);
}

static void
scanBlockModifiedVars(const CFGBlock *B,
                      llvm::SmallPtrSetImpl<const ValueDecl *> &ModifiedVars) {
  if (!B)
    return;

  // The thread safety analysis builds its CFG with all statements added as
  // separate CFG elements (setAllAlwaysAdd()). Hence, examining each element
  // without its subexpressions finds every modification while visiting each
  // AST node only once.
  for (const CFGElement &BI : *B) {
    std::optional<CFGStmt> CS = BI.getAs<CFGStmt>();
    if (!CS)
      continue;
    const Stmt *S = CS->getStmt();
    if (const auto *DS = dyn_cast<DeclStmt>(S)) {
      for (const Decl *D : DS->decls())
        if (const auto *VD = dyn_cast<VarDecl>(D); VD && VD->hasLocalStorage())
          ModifiedVars.insert(cast<ValueDecl>(VD->getCanonicalDecl()));
    } else if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
      if (BO->isAssignmentOp())
        if (const auto *DRE = unwrapDirectLValueDRE(BO->getLHS()))
          ModifiedVars.insert(
              cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
    } else if (const auto *UO = dyn_cast<UnaryOperator>(S)) {
      if (UO->isIncrementDecrementOp())
        if (const auto *DRE = unwrapDirectLValueDRE(UO->getSubExpr()))
          ModifiedVars.insert(
              cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl()));
    }
  }
}

static bool hasThreadSafetyCallEffects(const NamedDecl *Callee,
                                       const Expr *CallOrCtor) {
  if (CallOrCtor) {
    if (const auto *TagT = CallOrCtor->getType()->getAs<TagType>())
      if (TagT->getDecl()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>())
        return true;
  }
  if (!Callee)
    return false;
  if (Callee->hasAttr<AcquireCapabilityAttr>() ||
      Callee->hasAttr<ReleaseCapabilityAttr>() ||
      Callee->hasAttr<AssertCapabilityAttr>() ||
      Callee->hasAttr<TryAcquireCapabilityAttr>() ||
      Callee->hasAttr<TryAcquireCapabilityRangeAttr>() ||
      Callee->hasAttr<LocksExcludedAttr>() ||
      Callee->hasAttr<RequiresCapabilityAttr>())
    return true;
  if (const auto *FD = dyn_cast<FunctionDecl>(Callee)) {
    for (const ParmVarDecl *P : FD->parameters())
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

static std::optional<TrivialInlineBody>
getTrivialInlineBody(const CallExpr *CallExp) {
  if (!CallExp || CallExp->isTypeDependent() || CallExp->isValueDependent())
    return std::nullopt;
  const FunctionDecl *FD = CallExp->getDirectCallee();
  if (!FD)
    return std::nullopt;
  if (const auto *MD = dyn_cast<CXXMethodDecl>(FD))
    if (!MD->isStatic())
      return std::nullopt;

  const FunctionDecl *DefFD = nullptr;
  const Stmt *Body = FD->getBody(DefFD);
  if (!Body || !DefFD)
    return std::nullopt;
  if ((!DefFD->isInlined() && !DefFD->isConstexpr()) || DefFD->isWeak())
    return std::nullopt;
  if (DefFD->isVariadic() || CallExp->getNumArgs() != DefFD->getNumParams())
    return std::nullopt;
  if (hasThreadSafetyCallEffects(FD, CallExp) ||
      hasThreadSafetyCallEffects(DefFD, CallExp))
    return std::nullopt;

  for (const ParmVarDecl *P : DefFD->parameters()) {
    QualType PTy = P->getType();
    if (PTy.isNull() || PTy->isReferenceType() || PTy.isVolatileQualified())
      return std::nullopt;
  }

  const auto *CS = dyn_cast<CompoundStmt>(Body);
  if (!CS || CS->body_empty())
    return std::nullopt;

  TrivialInlineBody Info;
  Info.DefFD = DefFD;
  llvm::SmallPtrSet<const ValueDecl *, 8> CalleeModified;
  scanTrylockVars(CS, Info.CalleeEscaped, CalleeModified);
  for (const ParmVarDecl *P : DefFD->parameters()) {
    const auto *PVD = cast<ValueDecl>(P->getCanonicalDecl());
    if (Info.CalleeEscaped.contains(PVD) || CalleeModified.contains(PVD))
      return std::nullopt;
  }

  unsigned NumRets = countReturnStmts(CS);
  if (NumRets == 1) {
    if (const auto *RS = dyn_cast<ReturnStmt>(CS->body_back());
        RS && RS->getRetValue()) {
      Info.SingleRet = RS->getRetValue();
      return Info;
    }
    return std::nullopt;
  }

  if (NumRets == 2) {
    if (CS->size() == 1) {
      if (const auto *IS = dyn_cast<IfStmt>(CS->body_front());
          IS && !IS->getInit() && !IS->getConditionVariable() &&
          IS->getCond() && IS->getElse()) {
        const ReturnStmt *ThenRS = unwrapSingleReturnStmt(IS->getThen());
        const ReturnStmt *ElseRS = unwrapSingleReturnStmt(IS->getElse());
        if (ThenRS && ElseRS) {
          Info.CondExpr = IS->getCond();
          Info.ThenRet = ThenRS->getRetValue();
          Info.ElseRet = ElseRS->getRetValue();
          return Info;
        }
      }
    } else if (CS->size() == 2) {
      const auto *IS = dyn_cast<IfStmt>(CS->body_front());
      const auto *ElseRS = dyn_cast<ReturnStmt>(CS->body_back());
      if (IS && !IS->getInit() && !IS->getConditionVariable() &&
          IS->getCond() && !IS->getElse() && ElseRS && ElseRS->getRetValue()) {
        if (const ReturnStmt *ThenRS = unwrapSingleReturnStmt(IS->getThen())) {
          Info.CondExpr = IS->getCond();
          Info.ThenRet = ThenRS->getRetValue();
          Info.ElseRet = ElseRS->getRetValue();
          return Info;
        }
      }
    }
  }

  return std::nullopt;
}

/// The maximum nesting depth of inline helper expansion.
static constexpr unsigned MaxInlineDepth = 4;
/// The maximum number of inline helper expansions per analyzed function.
/// Bounds the cost of analyzing helpers that call other helpers many times.
static constexpr unsigned MaxInlineExpansions = 512;

std::optional<TrivialInlineBody>
ThreadSafetyAnalyzer::getCachedTrivialInlineBody(const CallExpr *CallExp) const {
  const FunctionDecl *FD = CallExp ? CallExp->getDirectCallee() : nullptr;
  if (!FD || CallExp->isTypeDependent() || CallExp->isValueDependent())
    return std::nullopt;
  if (InlineDepth >= MaxInlineDepth ||
      InlineExpansionCount >= MaxInlineExpansions)
    return std::nullopt;
  std::pair<const FunctionDecl *, unsigned> Key(FD->getCanonicalDecl(),
                                                CallExp->getNumArgs());
  auto [It, Inserted] = InlineBodyCache.try_emplace(Key);
  if (Inserted)
    It->second = getTrivialInlineBody(CallExp);
  std::optional<TrivialInlineBody> Info = It->second;
  // Do not expand recursive calls.
  if (Info && ActiveInlineCallees.contains(Info->DefFD))
    return std::nullopt;
  if (Info)
    ++InlineExpansionCount;
  return Info;
}

static bool isStraightLineStmtExprSubStmt(const Stmt *S, bool IsRoot = false) {
  if (!S)
    return true;
  if (!IsRoot && isa<StmtExpr, LambdaExpr, BlockExpr, CapturedStmt>(S))
    return true;
  if (isa<IfStmt, SwitchStmt, WhileStmt, DoStmt, ForStmt, CXXForRangeStmt,
          GotoStmt, IndirectGotoStmt, ReturnStmt, BreakStmt, ContinueStmt,
          LabelStmt, CaseStmt, DefaultStmt, CXXTryStmt>(S))
    return false;
  for (const Stmt *Child : S->children())
    if (Child && !isStraightLineStmtExprSubStmt(Child))
      return false;
  return true;
}

bool ThreadSafetyAnalyzer::isPureExitBlock(const CFGBlock *B,
                                           const CapExprSet &TargetCaps) {
  unsigned CtxIdx = BlockInfo[B->getBlockID()].EntryIndex;
  LocalVarContext StmtCtx = BlockInfo[B->getBlockID()].EntryContext;

  for (const CFGElement &BI : *B) {
    switch (BI.getKind()) {
    case CFGElement::Statement: {
      const Stmt *S = BI.castAs<CFGStmt>().getStmt();
      llvm::scope_exit AdvanceCtx(
          [&] { StmtCtx = LocalVarMap.getNextContext(CtxIdx, S, StmtCtx); });

      if (const auto *CCE = dyn_cast<CXXConstructExpr>(S)) {
        if (hasThreadSafetyCallEffects(CCE->getConstructor(), CCE))
          return false;
        break;
      }

      const auto *CE = dyn_cast<CallExpr>(S);
      if (!CE)
        break;

      unsigned BuiltinID = CE->getBuiltinCallee();
      if (BuiltinID == Builtin::BI__builtin_expect ||
          BuiltinID == Builtin::BI__builtin_expect_with_probability)
        break;

      const auto *Callee = dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
      if (!hasThreadSafetyCallEffects(Callee, CE))
        break;

      if (!Callee)
        return false;
      if (const auto *TagT = CE->getType()->getAs<TagType>())
        if (TagT->getDecl()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>())
          return false;
      if (const auto *MD = dyn_cast<CXXMethodDecl>(Callee))
        if (MD->getParent()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>())
          return false;
      if (const auto *FD = dyn_cast<FunctionDecl>(Callee))
        for (const ParmVarDecl *P : FD->parameters())
          if (P->hasAttrs())
            return false;

      std::optional<llvm::scope_exit<std::function<void()>>> LookupCleanup;
      if (Handler.issueBetaWarnings()) {
        LocalVarContext LookupCtx = StmtCtx;
        SxBuilder.setLookupLocalVarExpr(
            [this, LookupCtx](const NamedDecl *D) mutable -> const Expr * {
              return LocalVarMap.lookupExpr(D, LookupCtx);
            });
        LookupCleanup.emplace(
            [this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
      }

      auto CheckCapDisjoint = [&](Expr *Arg) -> bool {
        CapabilityExpr Cp =
            SxBuilder.translateAttrExpr(Arg, Callee, CE, /*Self=*/nullptr);
        if (Cp.isInvalid())
          return false;
        if (Cp.shouldIgnore())
          return true;
        return llvm::none_of(TargetCaps, [&](const CapabilityExpr &TC) {
          return TC.equals(Cp);
        });
      };

      for (const Attr *At : Callee->attrs()) {
        switch (At->getKind()) {
        case attr::AcquireCapability:
        case attr::TryAcquireCapability:
        case attr::TryAcquireCapabilityRange:
        case attr::AssertCapability:
        case attr::LocksExcluded:
          return false;
        case attr::ReleaseCapability: {
          const auto *A = cast<ReleaseCapabilityAttr>(At);
          if (A->args_size() == 0) {
            if (!isa<CXXMethodDecl>(Callee) || !CheckCapDisjoint(nullptr))
              return false;
          } else {
            for (Expr *Arg : A->args())
              if (!CheckCapDisjoint(Arg))
                return false;
          }
          break;
        }
        case attr::RequiresCapability: {
          const auto *A = cast<RequiresCapabilityAttr>(At);
          if (A->args_size() == 0) {
            if (!isa<CXXMethodDecl>(Callee) || !CheckCapDisjoint(nullptr))
              return false;
          } else {
            for (Expr *Arg : A->args())
              if (!CheckCapDisjoint(Arg))
                return false;
          }
          break;
        }
        default:
          break;
        }
      }
      break;
    }
    case CFGElement::AutomaticObjectDtor:
    case CFGElement::CleanupFunction:
      break;
    case CFGElement::TemporaryDtor: {
      // Destroying a temporary does not affect the lockset unless its
      // destructor has thread safety attributes.
      const CXXDestructorDecl *DD =
          BI.castAs<CFGTemporaryDtor>().getDestructorDecl(*ASTCtx);
      if (!DD ||
          DD->getParent()->getMostRecentDecl()->hasAttr<ScopedLockableAttr>() ||
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

static std::optional<ThreadSafetyAnalyzer::IntDomain>
getScalarDomainForType(QualType Ty, const ASTContext &Ctx) {
  using IntDomain = ThreadSafetyAnalyzer::IntDomain;
  if (Ty.isNull() || Ty->isDependentType())
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
  const unsigned PtrBits = ASTCtx->getIntWidth(ASTCtx->getUIntPtrType());
  while (E) {
    E = stripNoOpExprWrappers(E);
    if (const auto *CE = dyn_cast<CastExpr>(E)) {
      QualType SubTy = CE->getSubExpr()->getType();
      QualType DstTy = CE->getType();
      if (CE->getCastKind() == CK_LValueToRValue) {
        E = CE->getSubExpr();
        continue;
      }
      if (CE->getCastKind() == CK_IntegralCast &&
          isValuePreservingIntegralCast(SubTy, DstTy, *ASTCtx)) {
        E = CE->getSubExpr();
        continue;
      }
      if (CE->getCastKind() == CK_BitCast && DstTy->isAnyPointerType() &&
          SubTy->isAnyPointerType()) {
        E = CE->getSubExpr();
        continue;
      }
      if (CE->getCastKind() == CK_PointerToIntegral &&
          SubTy->isAnyPointerType() &&
          DstTy->isUnsignedIntegerOrEnumerationType() &&
          !DstTy->isBooleanType() && ASTCtx->getIntWidth(DstTy) >= PtrBits) {
        E = CE->getSubExpr();
        continue;
      }
      if (CE->getCastKind() == CK_IntegralToPointer &&
          DstTy->isAnyPointerType() &&
          SubTy->isUnsignedIntegerOrEnumerationType() &&
          !SubTy->isBooleanType() && ASTCtx->getIntWidth(SubTy) <= PtrBits) {
        E = CE->getSubExpr();
        continue;
      }
      return nullptr;
    }
    if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
      unsigned BuiltinID = CallExp->getBuiltinCallee();
      if (BuiltinID == Builtin::BI__builtin_expect ||
          BuiltinID == Builtin::BI__builtin_expect_with_probability) {
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

void ThreadSafetyAnalyzer::addLockToExpectedSet(FactSet &Set,
                                                const CapabilityExpr &Lock,
                                                LockKind LK,
                                                SourceLocation Loc) {
  if (Lock.shouldIgnore())
    return;
  if (auto It = Set.findLockIter(FactMan, Lock); It != Set.end()) {
    const auto &Existing = FactMan[*It];
    if (const auto *LFE = dyn_cast<LockableFactEntry>(&Existing)) {
      if (const FactEntry *RFact = LFE->tryReenter(FactMan, LK)) {
        Set.replaceLock(FactMan, It, RFact);
        return;
      }
    }
    if (Existing.kind() == LK_Shared && LK == LK_Exclusive)
      Set.replaceLock(
          FactMan, It,
          FactMan.createFact<LockableFactEntry>(Lock, LK_Exclusive, Loc));
    return;
  }
  Set.removeLock(FactMan, !Lock);
  Set.addLock(FactMan, FactMan.createFact<LockableFactEntry>(Lock, LK, Loc));
}

bool ThreadSafetyAnalyzer::factSetsEquivalent(const FactSet &A,
                                              const FactSet &B) const {
  auto FactMatchesIn = [&](const FactEntry &FA, const FactSet &Other) -> bool {
    const FactEntry *FB =
        Other.findLock(const_cast<FactManager &>(FactMan), FA);
    if (!FB)
      return false;
    if (FA.getFactEntryKind() != FB->getFactEntryKind() ||
        FA.kind() != FB->kind() || FA.negative() != FB->negative() ||
        FA.asserted() != FB->asserted())
      return false;
    if (const auto *LA = dyn_cast<LockableFactEntry>(&FA)) {
      const auto *LB = cast<LockableFactEntry>(FB);
      if (LA->getReentrancyDepth() != LB->getReentrancyDepth())
        return false;
    }
    return true;
  };
  for (FactID ID : A)
    if (!FactMatchesIn(FactMan[ID], B))
      return false;
  for (FactID ID : B)
    if (!FactMatchesIn(FactMan[ID], A))
      return false;
  return true;
}

static ThreadSafetyAnalyzer::IntRangeSet
reprojectRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                  const ThreadSafetyAnalyzer::IntDomain &Dom) {
  ThreadSafetyAnalyzer::IntRangeSet Res;
  for (const auto &[Lo, Hi] : Src.intervals())
    Res = Res.unionWith(
        ThreadSafetyAnalyzer::IntRangeSet::closedRange(Dom, Lo, Hi));
  return Res;
}

static ThreadSafetyAnalyzer::IntRangeSet
nonZeroRangeSet(const ThreadSafetyAnalyzer::IntDomain &Dom) {
  return ThreadSafetyAnalyzer::IntRangeSet::single(Dom, llvm::APSInt::get(0))
      .complement(Dom);
}

static ThreadSafetyAnalyzer::IntRangeSet
castDerivedToBaseRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                          const ThreadSafetyAnalyzer::IntDomain &Dom) {
  if (Src.empty())
    return {};
  auto Zero =
      ThreadSafetyAnalyzer::IntRangeSet::single(Dom, llvm::APSInt::get(0));
  ThreadSafetyAnalyzer::IntRangeSet Mapped = reprojectRangeSet(Src, Dom);
  ThreadSafetyAnalyzer::IntRangeSet Res;
  if (Mapped.intersectsSet(Zero))
    Res = Res.unionWith(Zero);
  if (!Mapped.subsetOfSet(Zero))
    Res = Res.unionWith(nonZeroRangeSet(Dom));
  return Res;
}

static ThreadSafetyAnalyzer::IntRangeSet
booleanizeRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                   const ThreadSafetyAnalyzer::IntDomain &SrcDom,
                   const ThreadSafetyAnalyzer::IntDomain &DstDom) {
  if (Src.empty())
    return {};
  auto Zero =
      ThreadSafetyAnalyzer::IntRangeSet::single(SrcDom, llvm::APSInt::get(0));
  ThreadSafetyAnalyzer::IntRangeSet Res;
  if (Src.intersectsSet(Zero))
    Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
        DstDom, llvm::APSInt::get(0)));
  if (!Src.subsetOfSet(Zero))
    Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
        DstDom, llvm::APSInt::get(1)));
  return Res;
}

static ThreadSafetyAnalyzer::IntRangeSet
castIntegralRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src,
                     QualType DstTy, const ASTContext &Ctx) {
  if (Src.empty())
    return {};
  auto DstDom = ThreadSafetyAnalyzer::IntDomain::forType(DstTy, Ctx);
  if (DstTy->isBooleanType()) {
    // Boolean conversion is != 0, handled via booleanizeRangeSet by callers.
    auto Zero =
        ThreadSafetyAnalyzer::IntRangeSet::single(DstDom, llvm::APSInt::get(0));
    ThreadSafetyAnalyzer::IntRangeSet Res;
    for (const auto &[Lo, Hi] : Src.intervals()) {
      if (llvm::APSInt::compareValues(Lo, llvm::APSInt::get(0)) <= 0 &&
          llvm::APSInt::compareValues(Hi, llvm::APSInt::get(0)) >= 0)
        Res = Res.unionWith(Zero);
      if (llvm::APSInt::compareValues(Lo, llvm::APSInt::get(0)) != 0 ||
          llvm::APSInt::compareValues(Hi, llvm::APSInt::get(0)) != 0)
        Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
            DstDom, llvm::APSInt::get(1)));
    }
    return Res;
  }

  unsigned DstBits = Ctx.getIntWidth(DstTy);
  bool DstUnsigned = DstTy->isUnsignedIntegerOrEnumerationType();
  llvm::APSInt MaxSmallSpan(DstDom.BitWidth, /*isUnsigned=*/false);
  MaxSmallSpan = 16;

  // The intervals of Src may be wider than the destination domain, e.g. for
  // __int128 sources. Use a width that can represent all values involved.
  unsigned WideW = std::max(DstDom.BitWidth + 2, DstBits + 3);
  for (const auto &[Lo, Hi] : Src.intervals())
    WideW = std::max({WideW, Lo.getBitWidth() + 1, Hi.getBitWidth() + 1});
  llvm::APSInt ZeroW(llvm::APInt::getZero(WideW), /*isUnsigned=*/false);
  llvm::APSInt OneW(llvm::APInt(WideW, 1), /*isUnsigned=*/false);
  llvm::APSInt NegOneW(llvm::APInt::getAllOnes(WideW), /*isUnsigned=*/false);
  llvm::APSInt TwoPowW(llvm::APInt::getOneBitSet(WideW, DstBits),
                       /*isUnsigned=*/false);
  llvm::APSInt SignBitVal(llvm::APInt::getOneBitSet(WideW, DstBits - 1),
                          /*isUnsigned=*/false);
  llvm::APSInt SignedMin = -SignBitVal;
  llvm::APSInt SignedMax = SignBitVal - OneW;
  llvm::APSInt MaxUnsigned = TwoPowW - OneW;

  ThreadSafetyAnalyzer::IntRangeSet Res;
  for (const auto &[Lo, Hi] : Src.intervals()) {
    if (llvm::APSInt::compareValues(Lo, DstDom.Lo) >= 0 &&
        llvm::APSInt::compareValues(Hi, DstDom.Hi) <= 0) {
      Res = Res.unionWith(
          ThreadSafetyAnalyzer::IntRangeSet::closedRange(DstDom, Lo, Hi));
      continue;
    }
    if (!DstUnsigned && llvm::APSInt::compareValues(Lo, ZeroW) >= 0 &&
        llvm::APSInt::compareValues(Hi, MaxUnsigned) <= 0) {
      llvm::APSInt LoW = Lo.extend(WideW);
      llvm::APSInt HiW = Hi.extend(WideW);
      if (LoW < SignBitVal) {
        llvm::APSInt SubHi = HiW < SignedMax ? HiW : SignedMax;
        Res = Res.unionWith(
            ThreadSafetyAnalyzer::IntRangeSet::closedRange(DstDom, LoW, SubHi));
      }
      if (HiW >= SignBitVal) {
        llvm::APSInt SubLo = LoW > SignBitVal ? LoW : SignBitVal;
        Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::closedRange(
            DstDom, SubLo - TwoPowW, HiW - TwoPowW));
      }
      continue;
    }
    if (DstUnsigned && llvm::APSInt::compareValues(Lo, SignedMin) >= 0 &&
        llvm::APSInt::compareValues(Hi, SignedMax) <= 0) {
      llvm::APSInt LoW = Lo.extend(WideW);
      llvm::APSInt HiW = Hi.extend(WideW);
      if (LoW < ZeroW) {
        llvm::APSInt SubHi = HiW < NegOneW ? HiW : NegOneW;
        Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::closedRange(
            DstDom, LoW + TwoPowW, SubHi + TwoPowW));
      }
      if (HiW >= ZeroW) {
        llvm::APSInt SubLo = LoW > ZeroW ? LoW : ZeroW;
        Res = Res.unionWith(
            ThreadSafetyAnalyzer::IntRangeSet::closedRange(DstDom, SubLo, HiW));
      }
      continue;
    }
    if (llvm::APSInt::compareValues(Hi - Lo, MaxSmallSpan) <= 0) {
      for (llvm::APSInt V = Lo; V <= Hi; ++V) {
        llvm::APSInt Trunc = V.extOrTrunc(DstBits);
        Trunc.setIsUnsigned(DstUnsigned);
        Res = Res.unionWith(
            ThreadSafetyAnalyzer::IntRangeSet::single(DstDom, Trunc));
      }
      continue;
    }
    return ThreadSafetyAnalyzer::IntRangeSet::full(DstDom);
  }
  return Res;
}

static ThreadSafetyAnalyzer::IntRangeSet
negateRangeSet(const ThreadSafetyAnalyzer::IntRangeSet &Src, QualType ResTy,
               const ASTContext &Ctx) {
  if (Src.empty())
    return {};
  auto Dom = ThreadSafetyAnalyzer::IntDomain::forType(ResTy, Ctx);
  unsigned Bits = Ctx.getIntWidth(ResTy);
  bool IsUnsigned = ResTy->isUnsignedIntegerOrEnumerationType();
  llvm::APSInt MaxSmallSpan(Dom.BitWidth, /*isUnsigned=*/false);
  MaxSmallSpan = 16;

  ThreadSafetyAnalyzer::IntRangeSet Res;
  for (const auto &[Lo, Hi] : Src.intervals()) {
    llvm::APSInt NegHi = -Hi;
    llvm::APSInt NegLo = -Lo;
    if (!IsUnsigned && llvm::APSInt::compareValues(NegHi, Dom.Lo) >= 0 &&
        llvm::APSInt::compareValues(NegLo, Dom.Hi) <= 0) {
      Res = Res.unionWith(
          ThreadSafetyAnalyzer::IntRangeSet::closedRange(Dom, NegHi, NegLo));
      continue;
    }
    if (llvm::APSInt::compareValues(Hi - Lo, MaxSmallSpan) <= 0) {
      for (llvm::APSInt V = Lo; V <= Hi; ++V) {
        llvm::APSInt NegV = (-V).extOrTrunc(Bits);
        NegV.setIsUnsigned(IsUnsigned);
        Res =
            Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(Dom, NegV));
      }
      continue;
    }
    return ThreadSafetyAnalyzer::IntRangeSet::full(Dom);
  }
  return Res;
}

static std::optional<ThreadSafetyAnalyzer::IntRangeSet> compareRangeSets(
    BinaryOperator::Opcode Opc, const ThreadSafetyAnalyzer::IntRangeSet &L,
    const ThreadSafetyAnalyzer::IntRangeSet &R,
    const ThreadSafetyAnalyzer::IntDomain &ResDom, bool IsMemberPtrComparison) {
  if (L.empty() || R.empty())
    return ThreadSafetyAnalyzer::IntRangeSet{};

  bool CanBeTrue = false;
  bool CanBeFalse = false;

  if (IsMemberPtrComparison) {
    if (Opc != BO_EQ && Opc != BO_NE)
      return std::nullopt;
    llvm::APSInt Z = llvm::APSInt::get(0);
    bool LNull = L.intersects(Z, Z);
    bool LNonNull = !L.subsetOf(Z, Z);
    bool RNull = R.intersects(Z, Z);
    bool RNonNull = !R.subsetOf(Z, Z);
    bool CanEq = (LNull && RNull) || (LNonNull && RNonNull);
    bool CanNe =
        (LNull && RNonNull) || (LNonNull && RNull) || (LNonNull && RNonNull);
    CanBeTrue = (Opc == BO_EQ) ? CanEq : CanNe;
    CanBeFalse = (Opc == BO_EQ) ? CanNe : CanEq;
  } else {
    const llvm::APSInt &LMin = L.intervals().front().first;
    const llvm::APSInt &LMax = L.intervals().back().second;
    const llvm::APSInt &RMin = R.intervals().front().first;
    const llvm::APSInt &RMax = R.intervals().back().second;

    switch (Opc) {
    case BO_EQ: {
      CanBeTrue = L.intersectsSet(R);
      llvm::APSInt LV, RV;
      CanBeFalse = !(L.isSingleValue(LV) && R.isSingleValue(RV) &&
                     llvm::APSInt::compareValues(LV, RV) == 0);
      break;
    }
    case BO_NE: {
      llvm::APSInt LV, RV;
      CanBeTrue = !(L.isSingleValue(LV) && R.isSingleValue(RV) &&
                    llvm::APSInt::compareValues(LV, RV) == 0);
      CanBeFalse = L.intersectsSet(R);
      break;
    }
    case BO_LT:
      CanBeTrue = llvm::APSInt::compareValues(LMin, RMax) < 0;
      CanBeFalse = llvm::APSInt::compareValues(LMax, RMin) >= 0;
      break;
    case BO_LE:
      CanBeTrue = llvm::APSInt::compareValues(LMin, RMax) <= 0;
      CanBeFalse = llvm::APSInt::compareValues(LMax, RMin) > 0;
      break;
    case BO_GT:
      CanBeTrue = llvm::APSInt::compareValues(LMax, RMin) > 0;
      CanBeFalse = llvm::APSInt::compareValues(LMin, RMax) <= 0;
      break;
    case BO_GE:
      CanBeTrue = llvm::APSInt::compareValues(LMax, RMin) >= 0;
      CanBeFalse = llvm::APSInt::compareValues(LMin, RMax) < 0;
      break;
    default:
      return std::nullopt;
    }
  }

  ThreadSafetyAnalyzer::IntRangeSet Res;
  if (CanBeFalse)
    Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
        ResDom, llvm::APSInt::get(0)));
  if (CanBeTrue)
    Res = Res.unionWith(ThreadSafetyAnalyzer::IntRangeSet::single(
        ResDom, llvm::APSInt::get(1)));
  return Res;
}

std::optional<ThreadSafetyAnalyzer::IntRangeSet>
ThreadSafetyAnalyzer::evaluatePureExprRange(const Expr *E,
                                            const TrylockValueState &State,
                                            unsigned Depth) const {
  if (!E || Depth > 24 || E->isTypeDependent() || E->isValueDependent())
    return std::nullopt;

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

  if (E->getType()->isIntegralOrEnumerationType()) {
    if (auto ICE = E->getIntegerConstantExpr(*ASTCtx))
      return IntRangeSet::single(Dom, *ICE);
  }

  if (isa<CXXNullPtrLiteralExpr, GNUNullExpr>(E))
    return IntRangeSet::single(Dom, llvm::APSInt::get(0));
  if (isa<CXXThisExpr>(E))
    return nonZeroRangeSet(Dom);

  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (VD) {
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
        return reprojectRangeSet(It->second, Dom);
    }
    return std::nullopt;
  }

  if (const auto *CE = dyn_cast<CastExpr>(E)) {
    switch (CE->getCastKind()) {
    case CK_LValueToRValue:
    case CK_NoOp: {
      auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
      return Sub ? std::optional<IntRangeSet>(reprojectRangeSet(*Sub, Dom))
                 : std::nullopt;
    }
    case CK_NullToPointer:
    case CK_NullToMemberPointer:
      return IntRangeSet::single(Dom, llvm::APSInt::get(0));
    case CK_ArrayToPointerDecay:
    case CK_FunctionToPointerDecay:
      return nonZeroRangeSet(Dom);
    case CK_BitCast:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType()) {
        auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
        return Sub ? std::optional<IntRangeSet>(reprojectRangeSet(*Sub, Dom))
                   : std::nullopt;
      }
      return std::nullopt;
    case CK_DerivedToBase:
    case CK_UncheckedDerivedToBase:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType()) {
        auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
        return Sub ? std::optional<IntRangeSet>(
                         castDerivedToBaseRangeSet(*Sub, Dom))
                   : std::nullopt;
      }
      return std::nullopt;
    case CK_PointerToIntegral:
      if (CE->getSubExpr()->getType()->isAnyPointerType() &&
          CE->getType()->isIntegralOrEnumerationType()) {
        auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
        return Sub ? std::optional<IntRangeSet>(
                         castIntegralRangeSet(*Sub, CE->getType(), *ASTCtx))
                   : std::nullopt;
      }
      return std::nullopt;
    case CK_IntegralToPointer:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isIntegralOrEnumerationType()) {
        auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
        return Sub ? std::optional<IntRangeSet>(castIntegralRangeSet(
                         *Sub, ASTCtx->getUIntPtrType(), *ASTCtx))
                   : std::nullopt;
      }
      return std::nullopt;
    case CK_IntegralToBoolean:
    case CK_PointerToBoolean:
    case CK_MemberPointerToBoolean: {
      auto SubDom = getScalarDomain(CE->getSubExpr()->getType());
      auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
      if (!SubDom || !Sub)
        return std::nullopt;
      return booleanizeRangeSet(*Sub, *SubDom, Dom);
    }
    case CK_BooleanToSignedIntegral: {
      auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
      return Sub ? std::optional<IntRangeSet>(reprojectRangeSet(*Sub, Dom))
                 : std::nullopt;
    }
    case CK_IntegralCast: {
      if (!CE->getSubExpr()->getType()->isIntegralOrEnumerationType() ||
          !CE->getType()->isIntegralOrEnumerationType())
        return std::nullopt;
      auto Sub = evaluatePureExprRange(CE->getSubExpr(), State, Depth + 1);
      if (!Sub)
        return std::nullopt;
      return castIntegralRangeSet(*Sub, CE->getType(), *ASTCtx);
    }
    default:
      return std::nullopt;
    }
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
    unsigned BuiltinID = CallExp->getBuiltinCallee();
    if (BuiltinID == Builtin::BI__builtin_expect ||
        BuiltinID == Builtin::BI__builtin_expect_with_probability) {
      auto Sub = evaluatePureExprRange(CallExp->getArg(0), State, Depth + 1);
      if (!Sub)
        return std::nullopt;
      return castIntegralRangeSet(*Sub, CallExp->getType(), *ASTCtx);
    }
    if (auto InlineInfo = getCachedTrivialInlineBody(CallExp)) {
      TrylockValueState CalleeState;
      for (unsigned I = 0, N = CallExp->getNumArgs(); I < N; ++I) {
        const auto *PVD = cast<ValueDecl>(
            InlineInfo->DefFD->getParamDecl(I)->getCanonicalDecl());
        auto PDom = getScalarDomain(PVD->getType());
        if (!PDom)
          continue;
        if (auto ArgR =
                evaluatePureExprRange(CallExp->getArg(I), State, Depth + 1))
          CalleeState.VarRanges[PVD] = reprojectRangeSet(*ArgR, *PDom);
      }
      ActiveInlineCallees.insert(InlineInfo->DefFD);
      ++InlineDepth;
      llvm::scope_exit PopInline([&] {
        --InlineDepth;
        ActiveInlineCallees.erase(InlineInfo->DefFD);
      });
      if (InlineInfo->SingleRet) {
        auto RetR = evaluatePureExprRange(InlineInfo->SingleRet, CalleeState,
                                          Depth + 1);
        return RetR ? std::optional<IntRangeSet>(reprojectRangeSet(*RetR, Dom))
                    : std::nullopt;
      }
      TrylockValueState TState = CalleeState;
      TrylockValueState FState = CalleeState;
      constrainLeafCondition(TState, InlineInfo->CondExpr, /*WantTrue=*/true,
                             InlineInfo->CalleeEscaped, Depth + 1);
      constrainLeafCondition(FState, InlineInfo->CondExpr, /*WantTrue=*/false,
                             InlineInfo->CalleeEscaped, Depth + 1);
      IntRangeSet Res;
      if (!TState.Infeasible) {
        auto TR = evaluatePureExprRange(InlineInfo->ThenRet, TState, Depth + 1);
        if (!TR)
          return std::nullopt;
        Res = Res.unionWith(reprojectRangeSet(*TR, Dom));
      }
      if (!FState.Infeasible) {
        auto FR = evaluatePureExprRange(InlineInfo->ElseRet, FState, Depth + 1);
        if (!FR)
          return std::nullopt;
        Res = Res.unionWith(reprojectRangeSet(*FR, Dom));
      }
      return Res;
    }
    return std::nullopt;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(E)) {
    switch (UO->getOpcode()) {
    case UO_AddrOf:
      return nonZeroRangeSet(Dom);
    case UO_Plus:
      return evaluatePureExprRange(UO->getSubExpr(), State, Depth + 1);
    case UO_Minus: {
      if (!UO->getType()->isIntegralOrEnumerationType())
        return std::nullopt;
      auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, Depth + 1);
      if (!Sub)
        return std::nullopt;
      return negateRangeSet(*Sub, UO->getType(), *ASTCtx);
    }
    case UO_Not: {
      if (!UO->getType()->isIntegralOrEnumerationType())
        return std::nullopt;
      auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, Depth + 1);
      llvm::APSInt V;
      if (!Sub || !Sub->isSingleValue(V))
        return std::nullopt;
      unsigned Bits = ASTCtx->getIntWidth(UO->getType());
      bool IsUnsigned = UO->getType()->isUnsignedIntegerOrEnumerationType();
      llvm::APSInt NotV = (~V).extOrTrunc(Bits);
      NotV.setIsUnsigned(IsUnsigned);
      return IntRangeSet::single(Dom, NotV);
    }
    case UO_LNot: {
      auto SubDom = getScalarDomain(UO->getSubExpr()->getType());
      auto Sub = evaluatePureExprRange(UO->getSubExpr(), State, Depth + 1);
      if (!SubDom || !Sub)
        return std::nullopt;
      IntRangeSet B = booleanizeRangeSet(*Sub, *SubDom, Dom);
      llvm::APSInt Z = llvm::APSInt::get(0);
      llvm::APSInt One = llvm::APSInt::get(1);
      IntRangeSet Res;
      if (B.intersects(One, One))
        Res = Res.unionWith(IntRangeSet::single(Dom, Z));
      if (B.intersects(Z, Z))
        Res = Res.unionWith(IntRangeSet::single(Dom, One));
      return Res;
    }
    default:
      return std::nullopt;
    }
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign)
      return evaluatePureExprRange(BO->getRHS(), State, Depth + 1);

    if (BO->isComparisonOp()) {
      auto L = evaluatePureExprRange(BO->getLHS(), State, Depth + 1);
      auto R = evaluatePureExprRange(BO->getRHS(), State, Depth + 1);
      if (!L || !R)
        return std::nullopt;
      bool IsMemberPtrCmp = BO->getLHS()->getType()->isMemberPointerType();
      return compareRangeSets(BO->getOpcode(), *L, *R, Dom, IsMemberPtrCmp);
    }

    if (BO->isLogicalOp()) {
      if (auto It = State.ShortCircuitedOps.find(BO);
          It != State.ShortCircuitedOps.end())
        return IntRangeSet::single(Dom, llvm::APSInt::get(It->second ? 1 : 0));
      auto BoolDom = IntDomain::forType(ASTCtx->BoolTy, *ASTCtx);
      auto EvalBool = [&](const Expr *Op) -> IntRangeSet {
        auto OpDom = getScalarDomain(Op->getType());
        auto OpR = evaluatePureExprRange(Op, State, Depth + 1);
        if (!OpDom || !OpR)
          return IntRangeSet::full(BoolDom);
        return booleanizeRangeSet(*OpR, *OpDom, BoolDom);
      };
      IntRangeSet LB = EvalBool(BO->getLHS());
      IntRangeSet RB = EvalBool(BO->getRHS());
      llvm::APSInt Z = llvm::APSInt::get(0);
      llvm::APSInt One = llvm::APSInt::get(1);
      bool L0 = LB.intersects(Z, Z), L1 = LB.intersects(One, One);
      bool R0 = RB.intersects(Z, Z), R1 = RB.intersects(One, One);
      bool Can0 = (BO->getOpcode() == BO_LAnd) ? (L0 || R0) : (L0 && R0);
      bool Can1 = (BO->getOpcode() == BO_LAnd) ? (L1 && R1) : (L1 || R1);
      IntRangeSet Res;
      if (Can0)
        Res = Res.unionWith(IntRangeSet::single(Dom, Z));
      if (Can1)
        Res = Res.unionWith(IntRangeSet::single(Dom, One));
      return Res;
    }

    if (E->getType()->isIntegralOrEnumerationType()) {
      auto L = evaluatePureExprRange(BO->getLHS(), State, Depth + 1);
      auto R = evaluatePureExprRange(BO->getRHS(), State, Depth + 1);
      llvm::APSInt LV, RV;
      if (L && R && L->isSingleValue(LV) && R->isSingleValue(RV)) {
        std::optional<llvm::APSInt> ResV;
        switch (BO->getOpcode()) {
        case BO_Add:
          ResV = LV + RV;
          break;
        case BO_Sub:
          ResV = LV - RV;
          break;
        case BO_And:
          ResV = LV & RV;
          break;
        case BO_Or:
          ResV = LV | RV;
          break;
        case BO_Xor:
          ResV = LV ^ RV;
          break;
        default:
          break;
        }
        if (ResV) {
          unsigned Bits = ASTCtx->getIntWidth(E->getType());
          bool IsUnsigned = E->getType()->isUnsignedIntegerOrEnumerationType();
          llvm::APSInt Trunc = ResV->extOrTrunc(Bits);
          Trunc.setIsUnsigned(IsUnsigned);
          return IntRangeSet::single(Dom, Trunc);
        }
      }
    }
    return std::nullopt;
  }

  if (const auto *COP = dyn_cast<AbstractConditionalOperator>(E)) {
    auto CondDom = getScalarDomain(COP->getCond()->getType());
    if (!CondDom)
      return std::nullopt;
    auto BoolDom = IntDomain::forType(ASTCtx->BoolTy, *ASTCtx);
    IntRangeSet CondB = IntRangeSet::full(BoolDom);
    if (auto CR = evaluatePureExprRange(COP->getCond(), State, Depth + 1))
      CondB = booleanizeRangeSet(*CR, *CondDom, BoolDom);
    llvm::APSInt Z = llvm::APSInt::get(0);
    llvm::APSInt One = llvm::APSInt::get(1);
    IntRangeSet Res;
    if (CondB.intersects(One, One)) {
      auto TR = evaluatePureExprRange(COP->getTrueExpr(), State, Depth + 1);
      if (!TR)
        return std::nullopt;
      Res = Res.unionWith(reprojectRangeSet(*TR, Dom));
    }
    if (CondB.intersects(Z, Z)) {
      auto FR = evaluatePureExprRange(COP->getFalseExpr(), State, Depth + 1);
      if (!FR)
        return std::nullopt;
      Res = Res.unionWith(reprojectRangeSet(*FR, Dom));
    }
    return Res;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(E)) {
    const CompoundStmt *CS = SE->getSubStmt();
    if (!CS || CS->body_empty() || !isStraightLineStmtExprSubStmt(CS, true))
      return std::nullopt;
    const auto *LastExpr = dyn_cast<Expr>(CS->body_back());
    if (!LastExpr)
      return std::nullopt;

    llvm::SmallPtrSet<const ValueDecl *, 4> LocalDecls;
    for (const Stmt *S : CS->body())
      if (const auto *DS = dyn_cast<DeclStmt>(S))
        for (const Decl *D : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(D);
              VD && VD->hasLocalStorage())
            LocalDecls.insert(cast<ValueDecl>(VD->getCanonicalDecl()));

    llvm::SmallPtrSet<const ValueDecl *, 4> SEEscaped, SEModified;
    scanTrylockVars(CS, SEEscaped, SEModified);
    for (const ValueDecl *MVD : SEModified)
      if (!SEEscaped.contains(MVD) && !LocalDecls.contains(MVD))
        return std::nullopt;

    TrylockValueState SubState = State;
    for (const Stmt *S : llvm::drop_end(CS->body())) {
      if (const auto *DS = dyn_cast<DeclStmt>(S)) {
        for (const Decl *D : DS->decls()) {
          const auto *VD = dyn_cast<VarDecl>(D);
          if (!VD || !VD->hasLocalStorage())
            continue;
          const auto *CanonVD = cast<ValueDecl>(VD->getCanonicalDecl());
          if (SEEscaped.contains(CanonVD) || !VD->getInit())
            continue;
          // The initializer may modify local variables, e.g.
          // 'int d = (r = 0, r);'. Evaluating such an initializer would use
          // stale values, so forget the modified variables and the
          // initialized variable instead.
          llvm::SmallPtrSet<const ValueDecl *, 4> InitEsc, InitMod;
          scanTrylockVars(VD->getInit(), InitEsc, InitMod);
          if (!InitMod.empty()) {
            for (const ValueDecl *MVD : InitMod)
              SubState.VarRanges.erase(MVD);
            SubState.VarRanges.erase(CanonVD);
            continue;
          }
          auto VDom = getScalarDomain(VD->getType());
          auto InitR =
              evaluatePureExprRange(VD->getInit(), SubState, Depth + 1);
          if (VDom && InitR)
            SubState.VarRanges[CanonVD] = reprojectRangeSet(*InitR, *VDom);
          else
            SubState.VarRanges.erase(CanonVD);
        }
        continue;
      }
      const Expr *StmtE = dyn_cast<Expr>(S);
      if (const auto *BO =
              dyn_cast_or_null<BinaryOperator>(stripNoOpExprWrappers(StmtE));
          BO && BO->getOpcode() == BO_Assign) {
        if (const auto *DRE = unwrapDirectLValueDRE(BO->getLHS())) {
          const auto *CanonVD =
              cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
          if (LocalDecls.contains(CanonVD) && !SEEscaped.contains(CanonVD)) {
            // The right-hand side may modify local variables, e.g.
            // 'd = (r = 0);'. Forget these and the assigned variable.
            llvm::SmallPtrSet<const ValueDecl *, 4> RHSEsc, RHSMod;
            scanTrylockVars(BO->getRHS(), RHSEsc, RHSMod);
            if (!RHSMod.empty()) {
              for (const ValueDecl *MVD : RHSMod)
                SubState.VarRanges.erase(MVD);
              SubState.VarRanges.erase(CanonVD);
              continue;
            }
            auto VDom = getScalarDomain(CanonVD->getType());
            auto RHSR =
                evaluatePureExprRange(BO->getRHS(), SubState, Depth + 1);
            if (VDom && RHSR)
              SubState.VarRanges[CanonVD] = reprojectRangeSet(*RHSR, *VDom);
            else
              SubState.VarRanges.erase(CanonVD);
            continue;
          }
        }
      }
      llvm::SmallPtrSet<const ValueDecl *, 4> SubEsc, SubMod;
      scanTrylockVars(S, SubEsc, SubMod);
      for (const ValueDecl *MVD : SubMod)
        if (LocalDecls.contains(MVD))
          SubState.VarRanges.erase(MVD);
    }
    auto Sub = evaluatePureExprRange(LastExpr, SubState, Depth + 1);
    return Sub ? std::optional<IntRangeSet>(reprojectRangeSet(*Sub, Dom))
               : std::nullopt;
  }

  return std::nullopt;
}

static void
unionIntoValueState(ThreadSafetyAnalyzer::TrylockValueState &Dst,
                    const ThreadSafetyAnalyzer::TrylockValueState &Src,
                    const ASTContext &Ctx) {
  if (Src.Infeasible)
    return;
  if (Dst.Infeasible) {
    Dst = Src;
    return;
  }

  // A missing entry means that nothing is known about a value. Drop entries
  // that cover the whole domain of their type such that the state does not
  // keep growing with every branch condition, which would make the analysis
  // quadratic in the size of the function.
  auto CoversDomain = [&Ctx](const ThreadSafetyAnalyzer::IntRangeSet &R,
                             QualType Ty) {
    auto Dom = getScalarDomainForType(Ty, Ctx);
    return Dom && R.intervals().size() == 1 &&
           llvm::APSInt::compareValues(R.intervals()[0].first, Dom->Lo) <= 0 &&
           llvm::APSInt::compareValues(R.intervals()[0].second, Dom->Hi) >= 0;
  };

  SmallVector<const ValueDecl *, 4> VarsToErase;
  for (auto &[VD, R] : Dst.VarRanges) {
    if (auto It = Src.VarRanges.find(VD); It != Src.VarRanges.end()) {
      R = R.unionWith(It->second);
      if (CoversDomain(R, VD->getType()))
        VarsToErase.push_back(VD);
    } else {
      VarsToErase.push_back(VD);
    }
  }
  for (const ValueDecl *VD : VarsToErase)
    Dst.VarRanges.erase(VD);

  SmallVector<const Expr *, 4> ExprsToErase;
  for (auto &[E, R] : Dst.ExprRanges) {
    if (auto It = Src.ExprRanges.find(E); It != Src.ExprRanges.end()) {
      R = R.unionWith(It->second);
      if (CoversDomain(R, E->getType()))
        ExprsToErase.push_back(E);
    } else {
      ExprsToErase.push_back(E);
    }
  }
  for (const Expr *E : ExprsToErase)
    Dst.ExprRanges.erase(E);

  SmallVector<const BinaryOperator *, 2> OpsToErase;
  for (const auto &[BO, Val] : Dst.ShortCircuitedOps) {
    auto It = Src.ShortCircuitedOps.find(BO);
    if (It == Src.ShortCircuitedOps.end() || It->second != Val)
      OpsToErase.push_back(BO);
  }
  for (const BinaryOperator *BO : OpsToErase)
    Dst.ShortCircuitedOps.erase(BO);

  for (const auto &Key : Src.AcquiredTrylockAttrs)
    Dst.AcquiredTrylockAttrs.insert(Key);
  for (const auto &Key : Src.ConsumedTrylockAttrs)
    Dst.ConsumedTrylockAttrs.insert(Key);
  for (const CallExpr *CE : Src.DiscardedTrylockCalls)
    Dst.DiscardedTrylockCalls.insert(CE);

  SmallVector<const ValueDecl *, 2> DefsToErase;
  for (const auto &[VD, DefPair] : Dst.UnmaterializedVarDefs) {
    auto It = Src.UnmaterializedVarDefs.find(VD);
    if (It == Src.UnmaterializedVarDefs.end() ||
        It->second.first != DefPair.first)
      DefsToErase.push_back(VD);
  }
  for (const ValueDecl *VD : DefsToErase)
    Dst.UnmaterializedVarDefs.erase(VD);
}

void ThreadSafetyAnalyzer::constrainLeafCondition(
    TrylockValueState &State, const Expr *Cond, bool WantTrue,
    const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
    unsigned Depth) const {
  if (State.Infeasible || !Cond || Depth > 24)
    return;

  Cond = stripNoOpExprWrappers(Cond);

  if (auto CondDom = getScalarDomain(Cond->getType())) {
    IntRangeSet Zero = IntRangeSet::single(*CondDom, llvm::APSInt::get(0));
    IntRangeSet Allowed = WantTrue ? Zero.complement(*CondDom) : Zero;
    if (auto Cur = evaluatePureExprRange(Cond, State, Depth + 1)) {
      Allowed = Allowed.intersect(*Cur);
      if (Allowed.empty()) {
        State.Infeasible = true;
        return;
      }
    }
    State.ExprRanges[Cond] = std::move(Allowed);
  }

  if (const auto *CE = dyn_cast<CastExpr>(Cond)) {
    switch (CE->getCastKind()) {
    case CK_LValueToRValue:
    case CK_NoOp:
    case CK_IntegralToBoolean:
    case CK_PointerToBoolean:
    case CK_MemberPointerToBoolean:
    case CK_BooleanToSignedIntegral:
      constrainLeafCondition(State, CE->getSubExpr(), WantTrue, EscapedVars,
                             Depth + 1);
      return;
    case CK_IntegralCast:
      if (isValuePreservingIntegralCast(CE->getSubExpr()->getType(),
                                        CE->getType(), *ASTCtx))
        constrainLeafCondition(State, CE->getSubExpr(), WantTrue, EscapedVars,
                               Depth + 1);
      return;
    case CK_BitCast:
    case CK_DerivedToBase:
    case CK_UncheckedDerivedToBase:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType())
        constrainLeafCondition(State, CE->getSubExpr(), WantTrue, EscapedVars,
                               Depth + 1);
      return;
    default:
      return;
    }
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(Cond)) {
    unsigned BuiltinID = CallExp->getBuiltinCallee();
    if (BuiltinID == Builtin::BI__builtin_expect ||
        BuiltinID == Builtin::BI__builtin_expect_with_probability) {
      constrainLeafCondition(State, CallExp->getArg(0), WantTrue, EscapedVars,
                             Depth + 1);
      return;
    }
    if (auto InlineInfo = getCachedTrivialInlineBody(CallExp)) {
      TrylockValueState CalleeState;
      for (unsigned I = 0, N = CallExp->getNumArgs(); I < N; ++I) {
        const auto *PVD = cast<ValueDecl>(
            InlineInfo->DefFD->getParamDecl(I)->getCanonicalDecl());
        auto PDom = getScalarDomain(PVD->getType());
        if (!PDom)
          continue;
        if (auto ArgR =
                evaluatePureExprRange(CallExp->getArg(I), State, Depth + 1))
          CalleeState.VarRanges[PVD] = reprojectRangeSet(*ArgR, *PDom);
      }
      ActiveInlineCallees.insert(InlineInfo->DefFD);
      ++InlineDepth;
      llvm::scope_exit PopInline([&] {
        --InlineDepth;
        ActiveInlineCallees.erase(InlineInfo->DefFD);
      });
      if (InlineInfo->SingleRet) {
        constrainLeafCondition(CalleeState, InlineInfo->SingleRet, WantTrue,
                               InlineInfo->CalleeEscaped, Depth + 1);
      } else {
        TrylockValueState TState = CalleeState;
        TrylockValueState FState = CalleeState;
        constrainLeafCondition(TState, InlineInfo->CondExpr, /*WantTrue=*/true,
                               InlineInfo->CalleeEscaped, Depth + 1);
        constrainLeafCondition(TState, InlineInfo->ThenRet, WantTrue,
                               InlineInfo->CalleeEscaped, Depth + 1);
        constrainLeafCondition(FState, InlineInfo->CondExpr, /*WantTrue=*/false,
                               InlineInfo->CalleeEscaped, Depth + 1);
        constrainLeafCondition(FState, InlineInfo->ElseRet, WantTrue,
                               InlineInfo->CalleeEscaped, Depth + 1);
        CalleeState.Infeasible = true;
        unionIntoValueState(CalleeState, TState, *ASTCtx);
        unionIntoValueState(CalleeState, FState, *ASTCtx);
      }
      if (CalleeState.Infeasible) {
        State.Infeasible = true;
        return;
      }
      for (unsigned I = 0, N = CallExp->getNumArgs(); I < N; ++I) {
        const ValueDecl *CallerVD =
            extractTrackableVarExpr(CallExp->getArg(I), EscapedVars);
        if (!CallerVD)
          continue;
        auto CallerDom = getScalarDomain(CallerVD->getType());
        if (!CallerDom)
          continue;
        const auto *PVD = cast<ValueDecl>(
            InlineInfo->DefFD->getParamDecl(I)->getCanonicalDecl());
        auto PIt = CalleeState.VarRanges.find(PVD);
        if (PIt == CalleeState.VarRanges.end())
          continue;
        IntRangeSet Mapped = reprojectRangeSet(PIt->second, *CallerDom);
        IntRangeSet Cur = IntRangeSet::full(*CallerDom);
        if (auto CIt = State.VarRanges.find(CallerVD);
            CIt != State.VarRanges.end())
          Cur = CIt->second;
        IntRangeSet Restricted = Cur.intersect(Mapped);
        if (Restricted.empty()) {
          State.Infeasible = true;
          return;
        }
        State.VarRanges[CallerVD] = std::move(Restricted);
      }
    }
    return;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(Cond)) {
    const CompoundStmt *CS = SE->getSubStmt();
    if (!CS || CS->body_empty() || !isStraightLineStmtExprSubStmt(CS, true))
      return;
    const auto *LastExpr = dyn_cast<Expr>(CS->body_back());
    if (!LastExpr)
      return;

    llvm::SmallPtrSet<const ValueDecl *, 4> LocalDecls;
    for (const Stmt *S : CS->body())
      if (const auto *DS = dyn_cast<DeclStmt>(S))
        for (const Decl *D : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(D);
              VD && VD->hasLocalStorage())
            LocalDecls.insert(cast<ValueDecl>(VD->getCanonicalDecl()));

    llvm::SmallPtrSet<const ValueDecl *, 4> SEEscaped, SEModified;
    scanTrylockVars(CS, SEEscaped, SEModified);
    for (const ValueDecl *MVD : SEModified)
      if (!SEEscaped.contains(MVD) && !LocalDecls.contains(MVD))
        return;

    auto UsesAnyLocalDecl = [&](auto &Self, const Stmt *S) -> bool {
      if (!S)
        return false;
      if (const auto *DRE = dyn_cast<DeclRefExpr>(S))
        if (LocalDecls.contains(
                cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl())))
          return true;
      for (const Stmt *Child : S->children())
        if (Child && Self(Self, Child))
          return true;
      return false;
    };

    const Expr *UnwrappedLast = stripNoOpExprWrappers(LastExpr);
    if (const auto *L2R = dyn_cast<CastExpr>(UnwrappedLast);
        L2R && L2R->getCastKind() == CK_LValueToRValue)
      UnwrappedLast = stripNoOpExprWrappers(L2R->getSubExpr());

    if (const auto *DRE = dyn_cast<DeclRefExpr>(UnwrappedLast)) {
      const auto *TargetVD =
          cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      if (LocalDecls.contains(TargetVD) && !SEEscaped.contains(TargetVD)) {
        const Expr *AssignedRHS = nullptr;
        unsigned AssignCount = 0;
        for (const Stmt *S : llvm::drop_end(CS->body())) {
          if (const auto *DS = dyn_cast<DeclStmt>(S)) {
            for (const Decl *D : DS->decls()) {
              const auto *VD = dyn_cast<VarDecl>(D);
              if (!VD || !VD->getInit())
                continue;
              // An initializer may assign to the target variable, e.g.
              // 'int d = (r = 0);'.
              llvm::SmallPtrSet<const ValueDecl *, 4> InitEsc, InitMod;
              scanTrylockVars(VD->getInit(), InitEsc, InitMod);
              if (InitMod.contains(TargetVD))
                return;
              if (VD->getCanonicalDecl() == TargetVD) {
                AssignedRHS = VD->getInit();
                ++AssignCount;
              }
            }
            continue;
          }
          const Expr *StmtE = dyn_cast<Expr>(S);
          if (const auto *BO = dyn_cast_or_null<BinaryOperator>(
                  stripNoOpExprWrappers(StmtE));
              BO && BO->getOpcode() == BO_Assign) {
            if (const auto *LHSDRE = unwrapDirectLValueDRE(BO->getLHS());
                LHSDRE && LHSDRE->getDecl()->getCanonicalDecl() == TargetVD) {
              AssignedRHS = BO->getRHS();
              ++AssignCount;
              continue;
            }
          }
          llvm::SmallPtrSet<const ValueDecl *, 4> SubEsc, SubMod;
          scanTrylockVars(S, SubEsc, SubMod);
          if (SubMod.contains(TargetVD))
            return;
        }
        if (AssignCount == 1 && AssignedRHS &&
            !UsesAnyLocalDecl(UsesAnyLocalDecl, AssignedRHS))
          constrainLeafCondition(State, AssignedRHS, WantTrue, EscapedVars,
                                 Depth + 1);
        return;
      }
    }

    if (!UsesAnyLocalDecl(UsesAnyLocalDecl, LastExpr))
      constrainLeafCondition(State, LastExpr, WantTrue, EscapedVars, Depth + 1);
    return;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(Cond)) {
    if (UO->getOpcode() == UO_LNot)
      constrainLeafCondition(State, UO->getSubExpr(), !WantTrue, EscapedVars,
                             Depth + 1);
    return;
  }

  if (const ValueDecl *VD = extractTrackableVarExpr(Cond, EscapedVars)) {
    auto VarDom = getScalarDomain(VD->getType());
    if (!VarDom)
      return;
    IntRangeSet Zero = IntRangeSet::single(*VarDom, llvm::APSInt::get(0));
    IntRangeSet Constraint = WantTrue ? Zero.complement(*VarDom) : Zero;
    IntRangeSet Cur = IntRangeSet::full(*VarDom);
    if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
      Cur = It->second;
    IntRangeSet Restricted = Cur.intersect(Constraint);
    if (Restricted.empty()) {
      State.Infeasible = true;
      return;
    }
    State.VarRanges[VD] = std::move(Restricted);
    return;
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(Cond)) {
    if (BO->getOpcode() == BO_Comma) {
      constrainLeafCondition(State, BO->getRHS(), WantTrue, EscapedVars,
                             Depth + 1);
      return;
    }
    if (BO->getOpcode() == BO_LAnd) {
      if (WantTrue) {
        constrainLeafCondition(State, BO->getLHS(), true, EscapedVars,
                               Depth + 1);
        constrainLeafCondition(State, BO->getRHS(), true, EscapedVars,
                               Depth + 1);
      } else {
        TrylockValueState LState = State;
        TrylockValueState RState = State;
        constrainLeafCondition(LState, BO->getLHS(), false, EscapedVars,
                               Depth + 1);
        constrainLeafCondition(RState, BO->getRHS(), false, EscapedVars,
                               Depth + 1);
        State.Infeasible = true;
        unionIntoValueState(State, LState, *ASTCtx);
        unionIntoValueState(State, RState, *ASTCtx);
      }
      return;
    }
    if (BO->getOpcode() == BO_LOr) {
      if (!WantTrue) {
        constrainLeafCondition(State, BO->getLHS(), false, EscapedVars,
                               Depth + 1);
        constrainLeafCondition(State, BO->getRHS(), false, EscapedVars,
                               Depth + 1);
      } else {
        TrylockValueState LState = State;
        TrylockValueState RState = State;
        constrainLeafCondition(LState, BO->getLHS(), true, EscapedVars,
                               Depth + 1);
        constrainLeafCondition(RState, BO->getRHS(), true, EscapedVars,
                               Depth + 1);
        State.Infeasible = true;
        unionIntoValueState(State, LState, *ASTCtx);
        unionIntoValueState(State, RState, *ASTCtx);
      }
      return;
    }

    if (BO->isComparisonOp()) {
      auto TryConstrainVarCmp = [&](const Expr *VarSide, const Expr *ConstSide,
                                    BinaryOperator::Opcode CmpOp) -> bool {
        const ValueDecl *VD = extractTrackableVarExpr(VarSide, EscapedVars);
        if (!VD)
          return false;
        auto VarDom = getScalarDomain(VD->getType());
        if (!VarDom)
          return false;

        std::optional<llvm::APSInt> KVal;
        if (auto R = evaluatePureExprRange(ConstSide, State, Depth + 1)) {
          llvm::APSInt SingleK;
          if (R->isSingleValue(SingleK))
            KVal = SingleK;
        }
        if (!KVal)
          return false;

        bool IsMemberPtr = VarSide->getType()->isMemberPointerType();
        if (IsMemberPtr && CmpOp != BO_EQ && CmpOp != BO_NE)
          return false;
        if (IsMemberPtr && *KVal != 0)
          return false;

        IntRangeSet Constraint =
            IntRangeSet::forComparison(*VarDom, CmpOp, *KVal);
        if (!WantTrue)
          Constraint = Constraint.complement(*VarDom);

        IntRangeSet Cur = IntRangeSet::full(*VarDom);
        if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
          Cur = It->second;
        IntRangeSet Restricted = Cur.intersect(Constraint);
        if (Restricted.empty())
          State.Infeasible = true;
        else
          State.VarRanges[VD] = std::move(Restricted);
        return true;
      };

      if (TryConstrainVarCmp(BO->getLHS(), BO->getRHS(), BO->getOpcode()))
        return;
      if (TryConstrainVarCmp(
              BO->getRHS(), BO->getLHS(),
              BinaryOperator::reverseComparisonOp(BO->getOpcode())))
        return;

      if (BO->getOpcode() == BO_EQ || BO->getOpcode() == BO_NE) {
        auto TryBoolOrZeroEq = [&](const Expr *SubSide,
                                   const Expr *ConstSide) -> bool {
          auto R = evaluatePureExprRange(ConstSide, State, Depth + 1);
          llvm::APSInt K;
          if (!R || !R->isSingleValue(K))
            return false;
          bool Eq = (BO->getOpcode() == BO_EQ) == WantTrue;
          if (K == 0) {
            constrainLeafCondition(State, SubSide, !Eq, EscapedVars, Depth + 1);
            return true;
          }
          QualType SubTy = SubSide->getType();
          const Expr *StrippedSub = stripNoOpExprWrappers(SubSide);
          bool IsZeroOrOne =
              SubTy->isBooleanType() ||
              (isa<UnaryOperator>(StrippedSub) &&
               cast<UnaryOperator>(StrippedSub)->getOpcode() == UO_LNot) ||
              (isa<BinaryOperator>(StrippedSub) &&
               (cast<BinaryOperator>(StrippedSub)->isComparisonOp() ||
                cast<BinaryOperator>(StrippedSub)->isLogicalOp()));
          if (!IsZeroOrOne)
            return false;
          if (K == 1) {
            constrainLeafCondition(State, SubSide, Eq, EscapedVars, Depth + 1);
            return true;
          }
          if (Eq)
            State.Infeasible = true;
          return true;
        };
        if (TryBoolOrZeroEq(BO->getLHS(), BO->getRHS()))
          return;
        if (TryBoolOrZeroEq(BO->getRHS(), BO->getLHS()))
          return;
      }
    }
  }
}

void ThreadSafetyAnalyzer::constrainValueStateOnEdge(
    TrylockValueState &State, const CFGBlock *PredBlock,
    const CFGBlock *CurrBlock,
    const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const {
  if (State.Infeasible)
    return;

  const Stmt *Term = PredBlock->getTerminatorStmt();
  if (!Term || isa<IndirectGotoStmt>(Term))
    return;

  if (const auto *SS = dyn_cast<SwitchStmt>(Term)) {
    const Expr *Cond = SS->getCond();
    if (!Cond)
      return;
    const ValueDecl *VD = extractTrackableVarExpr(Cond, EscapedVars);
    auto DomOpt =
        VD ? getScalarDomain(VD->getType()) : getScalarDomain(Cond->getType());
    if (!DomOpt)
      return;
    const IntDomain &Dom = *DomOpt;
    const SwitchCaseTable &Table = getSwitchCaseTable(SS, Dom);
    if (!Table.Valid)
      return;
    const auto *TargetCS = dyn_cast_if_present<CaseStmt>(CurrBlock->getLabel());
    IntRangeSet EdgeSet;
    if (auto It = Table.CaseSets.find(TargetCS); It != Table.CaseSets.end()) {
      EdgeSet = It->second;
    } else {
      if (!isa_and_nonnull<DefaultStmt>(CurrBlock->getLabel()) &&
          SS->isAllEnumCasesCovered()) {
        State.Infeasible = true;
        return;
      }
      EdgeSet = Table.DefaultSet;
    }

    if (VD) {
      IntRangeSet Cur = IntRangeSet::full(Dom);
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
        Cur = It->second;
      IntRangeSet Restricted = Cur.intersect(EdgeSet);
      if (Restricted.empty()) {
        State.Infeasible = true;
        return;
      }
      State.VarRanges[VD] = std::move(Restricted);
    }
    if (auto CondDom = getScalarDomain(Cond->getType())) {
      const Expr *StrippedCond = stripNoOpExprWrappers(Cond);
      IntRangeSet CondEdge = reprojectRangeSet(EdgeSet, *CondDom);
      if (auto Cur = evaluatePureExprRange(StrippedCond, State))
        CondEdge = CondEdge.intersect(*Cur);
      if (CondEdge.empty()) {
        State.Infeasible = true;
        return;
      }
      State.ExprRanges[StrippedCond] = std::move(CondEdge);
    }
    return;
  }

  const auto *RawCond =
      dyn_cast_or_null<Expr>(PredBlock->getTerminatorCondition());
  if (!RawCond)
    return;

  bool MatchesTrue = false;
  bool MatchesFalse = false;
  int BranchIdx = 0;
  for (auto SI = PredBlock->succ_begin(), SE = PredBlock->succ_end();
       SI != SE && BranchIdx < 2; ++SI, ++BranchIdx) {
    if (*SI == CurrBlock) {
      if (BranchIdx == 0)
        MatchesTrue = true;
      else
        MatchesFalse = true;
    }
  }
  if (MatchesTrue == MatchesFalse)
    return;

  bool TakeTrue = MatchesTrue;
  if (const auto *TermBO = dyn_cast<BinaryOperator>(Term)) {
    if (TermBO->getOpcode() == BO_LAnd && !TakeTrue)
      State.ShortCircuitedOps[TermBO] = false;
    else if (TermBO->getOpcode() == BO_LOr && TakeTrue)
      State.ShortCircuitedOps[TermBO] = true;
  }

  // In Clang's linearized CFG, PredBlock evaluated the rightmost leaf of any
  // top-level && / || chain in RawCond.
  const Expr *LeafCond = stripNoOpExprWrappers(RawCond);
  while (const auto *BO = dyn_cast<BinaryOperator>(LeafCond)) {
    if (!BO->isLogicalOp())
      break;
    LeafCond = stripNoOpExprWrappers(BO->getRHS());
  }

  constrainLeafCondition(State, LeafCond, TakeTrue, EscapedVars);
  if (State.Infeasible)
    return;

  const Expr *StrippedRaw = stripNoOpExprWrappers(RawCond);
  if (StrippedRaw != LeafCond) {
    if (auto RawDom = getScalarDomain(StrippedRaw->getType())) {
      IntRangeSet Zero = IntRangeSet::single(*RawDom, llvm::APSInt::get(0));
      IntRangeSet Allowed = TakeTrue ? Zero.complement(*RawDom) : Zero;
      if (auto Cur = evaluatePureExprRange(StrippedRaw, State))
        Allowed = Allowed.intersect(*Cur);
      if (Allowed.empty()) {
        State.Infeasible = true;
        return;
      }
      State.ExprRanges[StrippedRaw] = std::move(Allowed);
    }
    if (const auto *RawBO = dyn_cast<BinaryOperator>(StrippedRaw)) {
      if (RawBO->isLogicalOp())
        constrainLeafCondition(State, StrippedRaw, TakeTrue, EscapedVars);
    }
  }
}

void ThreadSafetyAnalyzer::materializeNarrowedTrylocks(
    FactSet &Lockset, TrylockValueState &State) {
  if (State.Infeasible || State.UnmaterializedVarDefs.empty())
    return;

  auto UnwrapDirectTrylockCall =
      [&](const Expr *E, LocalVarContext Ctx, QualType VarTy,
          bool &PreservesExactInt) -> const CallExpr * {
    PreservesExactInt = true;
    while (E) {
      E = stripNoOpExprWrappers(E);
      if (const auto *CE = dyn_cast<CastExpr>(E)) {
        switch (CE->getCastKind()) {
        case CK_LValueToRValue:
        case CK_NoOp:
          E = CE->getSubExpr();
          continue;
        case CK_IntegralCast:
          if (isValuePreservingIntegralCast(CE->getSubExpr()->getType(),
                                            CE->getType(), *ASTCtx)) {
            E = CE->getSubExpr();
            continue;
          }
          return nullptr;
        case CK_BitCast:
        case CK_DerivedToBase:
        case CK_UncheckedDerivedToBase:
          if (CE->getType()->isAnyPointerType() &&
              CE->getSubExpr()->getType()->isAnyPointerType()) {
            PreservesExactInt = false;
            E = CE->getSubExpr();
            continue;
          }
          return nullptr;
        case CK_IntegralToBoolean:
        case CK_PointerToBoolean:
        case CK_MemberPointerToBoolean:
          if (VarTy->isBooleanType()) {
            PreservesExactInt = false;
            E = CE->getSubExpr();
            continue;
          }
          return nullptr;
        default:
          return nullptr;
        }
      }
      if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
        E = LocalVarMap.lookupExpr(DRE->getDecl(), Ctx);
        continue;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
        if (BO->getOpcode() == BO_Assign) {
          E = BO->getRHS();
          continue;
        }
        return nullptr;
      }
      if (const auto *SE = dyn_cast<StmtExpr>(E)) {
        if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
          E = dyn_cast<Expr>(CS->body_back());
          continue;
        }
        return nullptr;
      }
      if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
        unsigned BuiltinID = CallExp->getBuiltinCallee();
        if (BuiltinID == Builtin::BI__builtin_expect ||
            BuiltinID == Builtin::BI__builtin_expect_with_probability) {
          E = CallExp->getArg(0);
          continue;
        }
        return CallExp;
      }
      return nullptr;
    }
    return nullptr;
  };

  auto AddTrylockFact = [&](const CapabilityExpr &Cap, LockKind LK,
                            SourceLocation Loc) {
    const FactEntry *Existing = Lockset.findLock(FactMan, Cap);
    if (Existing && Existing->loc() == Loc && !Existing->asserted()) {
      // The fact comes from the same trylock call, e.g. because a join kept
      // the shared fact of a call that acquires the capability exclusively
      // for other return values. Refine the lock kind instead of reporting a
      // double acquisition.
      if (Existing->kind() != LK)
        Lockset.replaceLock(FactMan, Cap,
                           FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
      return;
    }
    addLock(Lockset, FactMan.createFact<LockableFactEntry>(Cap, LK, Loc));
  };

  for (const auto &[VD, DefPair] : State.UnmaterializedVarDefs) {
    auto VR = State.VarRanges.find(VD);
    if (VR == State.VarRanges.end() || VR->second.empty())
      continue;
    auto VarDom = getScalarDomain(VD->getType());
    if (!VarDom)
      continue;
    bool PreservesExactInt = false;
    const CallExpr *CallExp = UnwrapDirectTrylockCall(
        DefPair.first, DefPair.second, VD->getType(), PreservesExactInt);
    if (!CallExp)
      continue;
    const auto *Callee = dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl());
    if (!Callee)
      continue;

    std::optional<llvm::scope_exit<std::function<void()>>> Cleanup;
    if (Handler.issueBetaWarnings()) {
      SxBuilder.setLookupLocalVarExpr(
          [this, LookupCtx = DefPair.second](const NamedDecl *D) mutable
              -> const Expr * { return LocalVarMap.lookupExpr(D, LookupCtx); });
      Cleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
    }

    CapExprSet ExclusiveLocksToAdd;
    CapExprSet SharedLocksToAdd;

    for (const auto *Attr :
         Callee->specific_attrs<TryAcquireCapabilityAttr>()) {
      if (State.AcquiredTrylockAttrs.contains({CallExp, Attr}))
        continue;
      bool SuccBool = false;
      if (!evalTrylockSuccessBool(Attr->getSuccessValue(), *ASTCtx, SuccBool))
        continue;
      IntRangeSet SuccSet = IntRangeSet::single(*VarDom, llvm::APSInt::get(0));
      if (SuccBool)
        SuccSet = SuccSet.complement(*VarDom);
      if (VR->second.subsetOfSet(SuccSet)) {
        CapExprSet AttrLocks;
        getMutexIDs(AttrLocks, Attr, CallExp, Callee);
        if (!AttrLocks.empty()) {
          State.AcquiredTrylockAttrs.insert({CallExp, Attr});
          CapExprSet &Dest =
              Attr->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd;
          for (const auto &Cap : AttrLocks)
            Dest.push_back_nodup(Cap);
        }
      }
    }

    if (PreservesExactInt &&
        CallExp->getType()->isIntegralOrEnumerationType() &&
        VD->getType()->isIntegralOrEnumerationType()) {
      for (const auto *Attr :
           Callee->specific_attrs<TryAcquireCapabilityRangeAttr>()) {
        if (State.AcquiredTrylockAttrs.contains({CallExp, Attr}))
          continue;
        if (!Attr->getFirstSuccessValue() || !Attr->getLastSuccessValue())
          continue;
        auto First =
            Attr->getFirstSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        auto Last =
            Attr->getLastSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        if (!First || !Last)
          continue;
        IntRangeSet SuccSet = IntRangeSet::closedRange(*VarDom, *First, *Last);
        if (VR->second.subsetOfSet(SuccSet)) {
          CapExprSet AttrLocks;
          getMutexIDs(AttrLocks, Attr, CallExp, Callee);
          if (!AttrLocks.empty()) {
            State.AcquiredTrylockAttrs.insert({CallExp, Attr});
            CapExprSet &Dest =
                Attr->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd;
            for (const auto &Cap : AttrLocks)
              Dest.push_back_nodup(Cap);
          }
        }
      }
    }

    SourceLocation Loc = CallExp->getExprLoc();
    for (const auto &Cap : ExclusiveLocksToAdd)
      AddTrylockFact(Cap, LK_Exclusive, Loc);
    for (const auto &Cap : SharedLocksToAdd)
      AddTrylockFact(Cap, LK_Shared, Loc);
  }
}

void ThreadSafetyAnalyzer::updateValueStateForStmt(
    TrylockValueState &State, const Stmt *S, LocalVarContext StmtCtx,
    const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) {
  if (State.Infeasible || !S)
    return;

  if (const auto *E = dyn_cast<Expr>(S)) {
    State.ExprRanges.erase(stripNoOpExprWrappers(E));
    if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
      if (BO->isLogicalOp()) {
        if (auto It = State.ShortCircuitedOps.find(BO);
            It != State.ShortCircuitedOps.end()) {
          // Preserve ShortCircuitedOps[BO] so the enclosing statement can read
          // the short-circuited value.
        }
      }
    }
    if (const auto *CE = dyn_cast<CallExpr>(E);
        CE && DiscardedCalls.contains(CE)) {
      if (const auto *Callee =
              dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
          Callee && (Callee->hasAttr<TryAcquireCapabilityAttr>() ||
                     Callee->hasAttr<TryAcquireCapabilityRangeAttr>()))
        State.DiscardedTrylockCalls.insert(CE);
    }
    if (const auto *CE = dyn_cast<CallExpr>(E)) {
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

  auto UpdateVarFromExpr = [&](const ValueDecl *VD, const Expr *RHS) {
    VD = cast<ValueDecl>(VD->getCanonicalDecl());
    if (!isTrackableLocalVar(VD, EscapedVars)) {
      State.VarRanges.erase(VD);
      State.UnmaterializedVarDefs.erase(VD);
      return;
    }
    if (!RHS) {
      State.VarRanges.erase(VD);
      State.UnmaterializedVarDefs.erase(VD);
      return;
    }
    if (const ValueDecl *SrcVD = extractTrackableVarExpr(RHS, EscapedVars)) {
      if (auto DefIt = State.UnmaterializedVarDefs.find(SrcVD);
          DefIt != State.UnmaterializedVarDefs.end()) {
        // Copy the definition first: inserting VD may grow the map and
        // invalidate DefIt.
        auto Def = DefIt->second;
        State.UnmaterializedVarDefs.insert_or_assign(VD, Def);
      } else if (exprHasUnmaterializedTrylock(RHS, StmtCtx, State,
                                              /*UseStateDefs=*/true))
        State.UnmaterializedVarDefs.insert_or_assign(
            VD, std::make_pair(RHS, StmtCtx));
      else
        State.UnmaterializedVarDefs.erase(VD);
    } else if (exprHasUnmaterializedTrylock(RHS, StmtCtx, State,
                                            /*UseStateDefs=*/true)) {
      State.UnmaterializedVarDefs.insert_or_assign(
          VD, std::make_pair(RHS, StmtCtx));
    } else {
      State.UnmaterializedVarDefs.erase(VD);
    }

    auto VarDom = getScalarDomain(VD->getType());
    auto R = evaluatePureExprRange(RHS, State);
    if (VarDom && R)
      State.VarRanges[VD] = reprojectRangeSet(*R, *VarDom);
    else
      State.VarRanges.erase(VD);
  };

  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    for (const Decl *D : DS->decls())
      if (const auto *VD = dyn_cast<VarDecl>(D))
        UpdateVarFromExpr(VD, VD->getInit());
    return;
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (!BO->isAssignmentOp())
      return;
    const auto *DRE = unwrapDirectLValueDRE(BO->getLHS());
    if (!DRE)
      return;
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (!VD)
      return;
    if (BO->getOpcode() == BO_Assign) {
      UpdateVarFromExpr(VD, BO->getRHS());
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end())
        State.ExprRanges[stripNoOpExprWrappers(BO)] = It->second;
    } else {
      State.UnmaterializedVarDefs.erase(VD);
      // Arithmetic on a bool converts the result back to bool instead of
      // wrapping it. Do not model that.
      if (isTrackableLocalVar(VD, EscapedVars) &&
          VD->getType()->isIntegralOrEnumerationType() &&
          !VD->getType()->isBooleanType()) {
        auto L = evaluatePureExprRange(BO->getLHS(), State);
        auto R = evaluatePureExprRange(BO->getRHS(), State);
        llvm::APSInt LV, RV;
        if (L && R && L->isSingleValue(LV) && R->isSingleValue(RV) &&
            (BO->getOpcode() == BO_AddAssign ||
             BO->getOpcode() == BO_SubAssign)) {
          unsigned W = std::max(LV.getBitWidth(), RV.getBitWidth()) + 1;
          LV = LV.extend(W);
          RV = RV.extend(W);
          llvm::APSInt ResV =
              (BO->getOpcode() == BO_AddAssign) ? (LV + RV) : (LV - RV);
          unsigned Bits = ASTCtx->getIntWidth(VD->getType());
          bool IsUnsigned = VD->getType()->isUnsignedIntegerOrEnumerationType();
          llvm::APSInt Trunc = ResV.extOrTrunc(Bits);
          Trunc.setIsUnsigned(IsUnsigned);
          auto VarDom = *getScalarDomain(VD->getType());
          State.VarRanges[VD] = IntRangeSet::single(VarDom, Trunc);
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
    if (!DRE)
      return;
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (!VD)
      return;
    State.UnmaterializedVarDefs.erase(VD);
    if (isTrackableLocalVar(VD, EscapedVars) &&
        VD->getType()->isIntegralOrEnumerationType() &&
        !VD->getType()->isBooleanType()) {
      if (auto It = State.VarRanges.find(VD); It != State.VarRanges.end()) {
        llvm::APSInt V;
        if (It->second.isSingleValue(V)) {
          llvm::APInt NextV = UO->isIncrementOp() ? (V + 1) : (V - 1);
          unsigned Bits = ASTCtx->getIntWidth(VD->getType());
          bool IsUnsigned = VD->getType()->isUnsignedIntegerOrEnumerationType();
          llvm::APSInt Trunc(NextV.sextOrTrunc(Bits), IsUnsigned);
          auto VarDom = *getScalarDomain(VD->getType());
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
  }
}

bool ThreadSafetyAnalyzer::exprHasUnmaterializedTrylock(
    const Expr *E, LocalVarContext Ctx, const TrylockValueState &State,
    bool UseStateDefs, unsigned Depth) {
  if (!E || Depth > 24)
    return false;
  E = stripNoOpExprWrappers(E);

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->isLogicalOp() && UseStateDefs &&
        State.ShortCircuitedOps.contains(BO))
      return false;
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
    unsigned BuiltinID = CallExp->getBuiltinCallee();
    if (BuiltinID == Builtin::BI__builtin_expect ||
        BuiltinID == Builtin::BI__builtin_expect_with_probability)
      return exprHasUnmaterializedTrylock(CallExp->getArg(0), Ctx, State,
                                          UseStateDefs, Depth + 1);
    if (const auto *Callee =
            dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl())) {
      for (const auto *Attr :
           Callee->specific_attrs<TryAcquireCapabilityAttr>())
        if (!State.AcquiredTrylockAttrs.contains({CallExp, Attr}))
          return true;
      if (CallExp->getType()->isIntegralOrEnumerationType()) {
        for (const auto *Attr :
             Callee->specific_attrs<TryAcquireCapabilityRangeAttr>())
          if (!State.AcquiredTrylockAttrs.contains({CallExp, Attr}))
            return true;
      }
    }
    return false;
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    if (UseStateDefs && VD) {
      if (auto It = State.UnmaterializedVarDefs.find(VD);
          It != State.UnmaterializedVarDefs.end())
        return exprHasUnmaterializedTrylock(It->second.first, It->second.second,
                                            State, /*UseStateDefs=*/false,
                                            Depth + 1);
    }
    LocalVarContext SubCtx = Ctx;
    if (const Expr *DefE = LocalVarMap.lookupExpr(DRE->getDecl(), SubCtx))
      return exprHasUnmaterializedTrylock(DefE, SubCtx, State,
                                          /*UseStateDefs=*/false, Depth + 1);
    return false;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(E)) {
    if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty())
      if (const auto *Last = dyn_cast<Expr>(CS->body_back()))
        return exprHasUnmaterializedTrylock(Last, Ctx, State, UseStateDefs,
                                            Depth + 1);
    return false;
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign)
      return exprHasUnmaterializedTrylock(BO->getRHS(), Ctx, State,
                                          UseStateDefs, Depth + 1);
  }

  for (const Stmt *Child : E->children())
    if (const auto *ChildE = dyn_cast_or_null<Expr>(Child))
      if (exprHasUnmaterializedTrylock(ChildE, Ctx, State, UseStateDefs,
                                       Depth + 1))
        return true;
  return false;
}

/// The maximum number of distinct outcomes that evaluateReturnOutcomes()
/// produces for a single expression.
static constexpr unsigned MaxReturnOutcomes = 64;

/// Evaluate the return value \p RetVal. Before doing that, split the outcomes
/// on every trylock call that may have succeeded on the current path but
/// whose result is not referenced by \p RetVal, either because the result has
/// been stored in a variable that is not used by \p RetVal or because the
/// result has been discarded. Without this, the capabilities acquired by such
/// a trylock call would not be taken into account.
void ThreadSafetyAnalyzer::evaluateReturnWithPendingTrylocks(
    const Expr *RetVal, const FactSet &InLockset,
    const TrylockValueState &State, LocalVarContext Ctx,
    SmallVectorImpl<ReturnEvalOutcome> &Out) {
  // The trylock calls referenced by the return value.
  llvm::SmallPtrSet<const Expr *, 4> ReferencedDefs;
  auto CollectRefs = [&](auto &Self, const Stmt *S) -> void {
    if (!S)
      return;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
      const auto *VD = cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
      if (auto It = State.UnmaterializedVarDefs.find(VD);
          It != State.UnmaterializedVarDefs.end())
        ReferencedDefs.insert(It->second.first);
    }
    for (const Stmt *Child : S->children())
      Self(Self, Child);
  };
  CollectRefs(CollectRefs, RetVal);

  // Sort the variables by source location for deterministic diagnostics.
  SmallVector<std::pair<const ValueDecl *, std::pair<const Expr *,
                                                     LocalVarContext>>,
              4>
      Defs(State.UnmaterializedVarDefs.begin(),
           State.UnmaterializedVarDefs.end());
  llvm::sort(Defs, [](const auto &A, const auto &B) {
    return A.first->getLocation().getRawEncoding() <
           B.first->getLocation().getRawEncoding();
  });

  struct Start {
    FactSet Lockset;
    SmallVector<PendingTrylockAcquire, 2> Pending;
  };
  SmallVector<Start, 2> Starts;
  Starts.push_back({InLockset, {}});
  TrylockValueState EmptyState;
  llvm::SmallPtrSet<const Expr *, 4> Done;

  auto Fork = [&](const Expr *DefE, LocalVarContext DefCtx,
                  const IntRangeSet *Allowed, const IntDomain &Dom) {
    SmallVector<Start, 2> Next;
    for (const Start &St : Starts) {
      SmallVector<ReturnEvalOutcome, 2> Outs;
      evaluateReturnOutcomes(DefE, Dom, St.Lockset, St.Pending, State, DefCtx,
                             /*UseVarRanges=*/false, Outs);
      for (ReturnEvalOutcome &O : Outs) {
        if (Allowed && O.Values.intersect(*Allowed).empty())
          continue;
        Next.push_back({std::move(O.Lockset), std::move(O.PendingAcquires)});
      }
    }
    if (!Next.empty() && Next.size() <= MaxReturnOutcomes)
      Starts = std::move(Next);
  };

  for (const auto &[VD, DefPair] : Defs) {
    const Expr *DefE = DefPair.first;
    if (ReferencedDefs.contains(DefE) || !Done.insert(DefE).second)
      continue;
    auto Dom = getScalarDomain(VD->getType());
    if (!Dom)
      continue;
    auto VR = State.VarRanges.find(VD);
    Fork(DefE, DefPair.second,
         VR != State.VarRanges.end() ? &VR->second : nullptr, *Dom);
  }
  for (const CallExpr *CE : State.DiscardedTrylockCalls) {
    if (!Done.insert(CE).second)
      continue;
    auto Dom = getScalarDomain(CE->getType());
    if (!Dom)
      continue;
    Fork(CE, Ctx, /*Allowed=*/nullptr, *Dom);
  }

  for (const Start &St : Starts)
    evaluateReturnOutcomes(RetVal, CurrentTrylockRetDom, St.Lockset, St.Pending,
                           State, Ctx, /*UseVarRanges=*/true, Out);
}

void ThreadSafetyAnalyzer::evaluateReturnOutcomes(
    const Expr *E, const IntDomain &TargetDom, const FactSet &InLockset,
    const SmallVectorImpl<PendingTrylockAcquire> &InPending,
    const TrylockValueState &State, LocalVarContext Ctx, bool UseVarRanges,
    SmallVectorImpl<ReturnEvalOutcome> &Out, unsigned Depth) {
  SmallVector<ReturnEvalOutcome, 4> Local;
  evaluateReturnOutcomesImpl(E, TargetDom, InLockset, InPending, State, Ctx,
                             UseVarRanges, Local, Depth);

  // Merge outcomes that only differ in their values. This keeps the number
  // of outcomes linear instead of exponential in the number of trylock calls
  // in nested comparisons and logical operators.
  auto SamePending = [](const SmallVectorImpl<PendingTrylockAcquire> &A,
                        const SmallVectorImpl<PendingTrylockAcquire> &B) {
    return A.size() == B.size() &&
           llvm::all_of(llvm::zip_equal(A, B), [](const auto &P) {
             const PendingTrylockAcquire &PA = std::get<0>(P);
             const PendingTrylockAcquire &PB = std::get<1>(P);
             return PA.LK == PB.LK && PA.Loc == PB.Loc &&
                    PA.Cap.equals(PB.Cap);
           });
  };
  SmallVector<ReturnEvalOutcome, 4> Merged;
  for (ReturnEvalOutcome &O : Local) {
    auto It = llvm::find_if(Merged, [&](const ReturnEvalOutcome &M) {
      return SamePending(M.PendingAcquires, O.PendingAcquires) &&
             factSetsEquivalent(M.Lockset, O.Lockset);
    });
    if (It != Merged.end())
      It->Values = It->Values.unionWith(O.Values);
    else
      Merged.push_back(std::move(O));
  }

  if (Merged.size() > MaxReturnOutcomes) {
    // Give up on tracking the lock state per outcome. Assume that every
    // capability that any outcome holds or acquires is held or acquired for
    // every return value, such that a capability that is acquired on some
    // path is not forgotten. This may report false positives but never
    // misses a leaked capability.
    ReturnEvalOutcome O;
    O.Values = IntRangeSet::full(TargetDom);
    O.Lockset = InLockset;
    for (const ReturnEvalOutcome &M : Merged) {
      for (const auto &Fact : M.Lockset)
        if (!O.Lockset.findLock(FactMan, FactMan[Fact]))
          O.Lockset.addLock(FactMan, &FactMan[Fact]);
      for (const PendingTrylockAcquire &PA : M.PendingAcquires) {
        // Acquire each capability at most once.
        auto It = llvm::find_if(O.PendingAcquires,
                                [&](const PendingTrylockAcquire &Existing) {
                                  return Existing.Cap.equals(PA.Cap);
                                });
        if (It == O.PendingAcquires.end())
          O.PendingAcquires.push_back(PA);
        else if (PA.LK == LK_Exclusive)
          It->LK = LK_Exclusive;
      }
    }
    Out.push_back(std::move(O));
    return;
  }
  for (ReturnEvalOutcome &O : Merged)
    Out.push_back(std::move(O));
}

void ThreadSafetyAnalyzer::evaluateReturnOutcomesImpl(
    const Expr *E, const IntDomain &TargetDom, const FactSet &InLockset,
    const SmallVectorImpl<PendingTrylockAcquire> &InPending,
    const TrylockValueState &State, LocalVarContext Ctx, bool UseVarRanges,
    SmallVectorImpl<ReturnEvalOutcome> &Out, unsigned Depth) {
  if (State.Infeasible)
    return;

  auto EmitDefault = [&]() {
    ReturnEvalOutcome O;
    O.Values = IntRangeSet::full(TargetDom);
    O.Lockset = InLockset;
    O.PendingAcquires.assign(InPending.begin(), InPending.end());
    Out.push_back(std::move(O));
  };

  if (!E || Depth > 24 || E->isTypeDependent() || E->isValueDependent()) {
    EmitDefault();
    return;
  }

  E = stripNoOpExprWrappers(E);
  size_t StartIdx = Out.size();
  auto ApplyExprConstraint = [&]() {
    if (!UseVarRanges && !isa<CallExpr>(E))
      return;
    auto It = State.ExprRanges.find(E);
    if (It == State.ExprRanges.end())
      return;
    IntRangeSet Allowed = reprojectRangeSet(It->second, TargetDom);
    size_t WriteIdx = StartIdx;
    for (size_t I = StartIdx; I < Out.size(); ++I) {
      Out[I].Values = Out[I].Values.intersect(Allowed);
      if (!Out[I].Values.empty()) {
        if (WriteIdx != I)
          Out[WriteIdx] = std::move(Out[I]);
        ++WriteIdx;
      }
    }
    Out.truncate(WriteIdx);
  };

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->isLogicalOp() && UseVarRanges) {
      if (auto It = State.ShortCircuitedOps.find(BO);
          It != State.ShortCircuitedOps.end()) {
        ReturnEvalOutcome O;
        O.Values = IntRangeSet::single(TargetDom,
                                       llvm::APSInt::get(It->second ? 1 : 0));
        O.Lockset = InLockset;
        O.PendingAcquires.assign(InPending.begin(), InPending.end());
        Out.push_back(std::move(O));
        ApplyExprConstraint();
        return;
      }
    }
  }

  if (!exprHasUnmaterializedTrylock(E, Ctx, State, UseVarRanges)) {
    TrylockValueState EmptyState;
    const TrylockValueState &EvalState = UseVarRanges ? State : EmptyState;
    if (auto R = evaluatePureExprRange(E, EvalState)) {
      IntRangeSet Mapped = reprojectRangeSet(*R, TargetDom);
      if (!Mapped.empty()) {
        ReturnEvalOutcome O;
        O.Values = std::move(Mapped);
        O.Lockset = InLockset;
        O.PendingAcquires.assign(InPending.begin(), InPending.end());
        Out.push_back(std::move(O));
      }
      ApplyExprConstraint();
      return;
    }
    EmitDefault();
    ApplyExprConstraint();
    return;
  }

  if (const auto *SE = dyn_cast<StmtExpr>(E)) {
    if (const auto *CS = SE->getSubStmt(); CS && !CS->body_empty()) {
      if (const auto *Last = dyn_cast<Expr>(CS->body_back())) {
        evaluateReturnOutcomes(Last, TargetDom, InLockset, InPending, State,
                               Ctx, UseVarRanges, Out, Depth + 1);
        ApplyExprConstraint();
        return;
      }
    }
    EmitDefault();
    ApplyExprConstraint();
    return;
  }

  if (const auto *CE = dyn_cast<CastExpr>(E)) {
    switch (CE->getCastKind()) {
    case CK_LValueToRValue:
    case CK_NoOp:
      evaluateReturnOutcomes(CE->getSubExpr(), TargetDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Out, Depth + 1);
      ApplyExprConstraint();
      return;
    case CK_BitCast:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType()) {
        evaluateReturnOutcomes(CE->getSubExpr(), TargetDom, InLockset,
                               InPending, State, Ctx, UseVarRanges, Out,
                               Depth + 1);
        ApplyExprConstraint();
        return;
      }
      EmitDefault();
      ApplyExprConstraint();
      return;
    case CK_DerivedToBase:
    case CK_UncheckedDerivedToBase:
      if (CE->getType()->isAnyPointerType() &&
          CE->getSubExpr()->getType()->isAnyPointerType()) {
        auto PtrDom = getScalarDomain(CE->getType());
        if (!PtrDom) {
          EmitDefault();
          ApplyExprConstraint();
          return;
        }
        SmallVector<ReturnEvalOutcome, 2> Sub;
        evaluateReturnOutcomes(CE->getSubExpr(), *PtrDom, InLockset, InPending,
                               State, Ctx, UseVarRanges, Sub, Depth + 1);
        for (auto &SO : Sub) {
          SO.Values = reprojectRangeSet(
              castDerivedToBaseRangeSet(SO.Values, *PtrDom), TargetDom);
          if (!SO.Values.empty())
            Out.push_back(std::move(SO));
        }
        ApplyExprConstraint();
        return;
      }
      EmitDefault();
      ApplyExprConstraint();
      return;
    case CK_PointerToIntegral: {
      if (!CE->getSubExpr()->getType()->isAnyPointerType() ||
          !CE->getType()->isIntegralOrEnumerationType()) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      auto SubDom = getScalarDomain(CE->getSubExpr()->getType());
      if (!SubDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CE->getSubExpr(), *SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(
            castIntegralRangeSet(SO.Values, CE->getType(), *ASTCtx), TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }
    case CK_IntegralToPointer: {
      if (!CE->getType()->isAnyPointerType() ||
          !CE->getSubExpr()->getType()->isIntegralOrEnumerationType()) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      IntDomain SubDom =
          IntDomain::forType(CE->getSubExpr()->getType(), *ASTCtx);
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CE->getSubExpr(), SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(
            castIntegralRangeSet(SO.Values, ASTCtx->getUIntPtrType(), *ASTCtx),
            TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }
    case CK_IntegralToBoolean:
    case CK_PointerToBoolean:
    case CK_MemberPointerToBoolean: {
      auto SubDom = getScalarDomain(CE->getSubExpr()->getType());
      if (!SubDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CE->getSubExpr(), *SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      IntRangeSet Zero = IntRangeSet::single(*SubDom, llvm::APSInt::get(0));
      IntRangeSet NonZero = Zero.complement(*SubDom);
      for (auto &SO : Sub) {
        if (!SO.Values.intersect(Zero).empty()) {
          ReturnEvalOutcome O = SO;
          O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
          Out.push_back(std::move(O));
        }
        if (!SO.Values.intersect(NonZero).empty()) {
          ReturnEvalOutcome O = std::move(SO);
          O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(1));
          Out.push_back(std::move(O));
        }
      }
      ApplyExprConstraint();
      return;
    }
    case CK_BooleanToSignedIntegral: {
      auto SubDom = getScalarDomain(CE->getSubExpr()->getType());
      if (!SubDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CE->getSubExpr(), *SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(SO.Values, TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }
    case CK_IntegralCast: {
      if (!CE->getSubExpr()->getType()->isIntegralOrEnumerationType() ||
          !CE->getType()->isIntegralOrEnumerationType()) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      IntDomain SubDom =
          IntDomain::forType(CE->getSubExpr()->getType(), *ASTCtx);
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CE->getSubExpr(), SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(
            castIntegralRangeSet(SO.Values, CE->getType(), *ASTCtx), TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }
    default:
      EmitDefault();
      ApplyExprConstraint();
      return;
    }
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    const auto *VD = dyn_cast<ValueDecl>(DRE->getDecl()->getCanonicalDecl());
    const Expr *DefE = nullptr;
    LocalVarContext DefCtx = Ctx;
    if (UseVarRanges && VD) {
      if (auto It = State.UnmaterializedVarDefs.find(VD);
          It != State.UnmaterializedVarDefs.end()) {
        DefE = It->second.first;
        DefCtx = It->second.second;
      }
    }
    if (!DefE) {
      DefCtx = Ctx;
      DefE = LocalVarMap.lookupExpr(DRE->getDecl(), DefCtx);
    }
    if (DefE) {
      if (auto SubDom = getScalarDomain(DefE->getType())) {
        SmallVector<ReturnEvalOutcome, 2> Sub;
        evaluateReturnOutcomes(DefE, *SubDom, InLockset, InPending, State,
                               DefCtx, /*UseVarRanges=*/false, Sub, Depth + 1);
        std::optional<IntRangeSet> VarConstraint;
        if (UseVarRanges && VD) {
          if (auto VR = State.VarRanges.find(VD); VR != State.VarRanges.end())
            VarConstraint = reprojectRangeSet(VR->second, TargetDom);
        }
        for (auto &SO : Sub) {
          SO.Values = reprojectRangeSet(SO.Values, TargetDom);
          if (VarConstraint)
            SO.Values = SO.Values.intersect(*VarConstraint);
          if (!SO.Values.empty())
            Out.push_back(std::move(SO));
        }
        ApplyExprConstraint();
        return;
      }
    }
    EmitDefault();
    ApplyExprConstraint();
    return;
  }

  if (const auto *UO = dyn_cast<UnaryOperator>(E)) {
    switch (UO->getOpcode()) {
    case UO_Plus:
      evaluateReturnOutcomes(UO->getSubExpr(), TargetDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Out, Depth + 1);
      ApplyExprConstraint();
      return;
    case UO_Minus: {
      if (!UO->getType()->isIntegralOrEnumerationType()) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(UO->getSubExpr(), TargetDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(
            negateRangeSet(SO.Values, UO->getType(), *ASTCtx), TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }
    case UO_LNot: {
      auto SubDom = getScalarDomain(UO->getSubExpr()->getType());
      if (!SubDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(UO->getSubExpr(), *SubDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      IntRangeSet Zero = IntRangeSet::single(*SubDom, llvm::APSInt::get(0));
      IntRangeSet NonZero = Zero.complement(*SubDom);
      for (auto &SO : Sub) {
        if (!SO.Values.intersect(Zero).empty()) {
          ReturnEvalOutcome O = SO;
          O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(1));
          Out.push_back(std::move(O));
        }
        if (!SO.Values.intersect(NonZero).empty()) {
          ReturnEvalOutcome O = std::move(SO);
          O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
          Out.push_back(std::move(O));
        }
      }
      ApplyExprConstraint();
      return;
    }
    default:
      EmitDefault();
      ApplyExprConstraint();
      return;
    }
  }

  if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
    if (BO->getOpcode() == BO_Comma || BO->getOpcode() == BO_Assign) {
      evaluateReturnOutcomes(BO->getRHS(), TargetDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Out, Depth + 1);
      ApplyExprConstraint();
      return;
    }

    if (BO->isComparisonOp()) {
      auto LDom = getScalarDomain(BO->getLHS()->getType());
      auto RDom = getScalarDomain(BO->getRHS()->getType());
      if (!LDom || !RDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      bool IsMemberPtrCmp = BO->getLHS()->getType()->isMemberPointerType();
      SmallVector<ReturnEvalOutcome, 2> LHSOut;
      evaluateReturnOutcomes(BO->getLHS(), *LDom, InLockset, InPending, State,
                             Ctx, UseVarRanges, LHSOut, Depth + 1);
      for (const auto &LO : LHSOut) {
        SmallVector<ReturnEvalOutcome, 2> RHSOut;
        evaluateReturnOutcomes(BO->getRHS(), *RDom, LO.Lockset,
                               LO.PendingAcquires, State, Ctx, UseVarRanges,
                               RHSOut, Depth + 1);
        for (auto &RO : RHSOut) {
          auto Cmp = compareRangeSets(BO->getOpcode(), LO.Values, RO.Values,
                                      TargetDom, IsMemberPtrCmp);
          if (!Cmp) {
            RO.Values = IntRangeSet::full(TargetDom);
            Out.push_back(std::move(RO));
            continue;
          }
          llvm::APSInt Z = llvm::APSInt::get(0);
          llvm::APSInt One = llvm::APSInt::get(1);
          if (Cmp->intersects(Z, Z)) {
            ReturnEvalOutcome O = RO;
            O.Values = IntRangeSet::single(TargetDom, Z);
            Out.push_back(std::move(O));
          }
          if (Cmp->intersects(One, One)) {
            ReturnEvalOutcome O = std::move(RO);
            O.Values = IntRangeSet::single(TargetDom, One);
            Out.push_back(std::move(O));
          }
        }
      }
      ApplyExprConstraint();
      return;
    }

    if (BO->isLogicalOp()) {
      auto LDom = getScalarDomain(BO->getLHS()->getType());
      auto RDom = getScalarDomain(BO->getRHS()->getType());
      if (!LDom || !RDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> LHSOut;
      evaluateReturnOutcomes(BO->getLHS(), *LDom, InLockset, InPending, State,
                             Ctx, UseVarRanges, LHSOut, Depth + 1);
      IntRangeSet ZeroL = IntRangeSet::single(*LDom, llvm::APSInt::get(0));
      IntRangeSet NonZeroL = ZeroL.complement(*LDom);
      IntRangeSet ZeroR = IntRangeSet::single(*RDom, llvm::APSInt::get(0));
      IntRangeSet NonZeroR = ZeroR.complement(*RDom);

      for (const auto &LO : LHSOut) {
        if (BO->getOpcode() == BO_LAnd) {
          if (!LO.Values.intersect(ZeroL).empty()) {
            ReturnEvalOutcome O = LO;
            O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
            Out.push_back(std::move(O));
          }
          if (!LO.Values.intersect(NonZeroL).empty()) {
            SmallVector<ReturnEvalOutcome, 2> RHSOut;
            evaluateReturnOutcomes(BO->getRHS(), *RDom, LO.Lockset,
                                   LO.PendingAcquires, State, Ctx, UseVarRanges,
                                   RHSOut, Depth + 1);
            for (auto &RO : RHSOut) {
              if (!RO.Values.intersect(ZeroR).empty()) {
                ReturnEvalOutcome O = RO;
                O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
                Out.push_back(std::move(O));
              }
              if (!RO.Values.intersect(NonZeroR).empty()) {
                ReturnEvalOutcome O = std::move(RO);
                O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(1));
                Out.push_back(std::move(O));
              }
            }
          }
        } else {
          if (!LO.Values.intersect(NonZeroL).empty()) {
            ReturnEvalOutcome O = LO;
            O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(1));
            Out.push_back(std::move(O));
          }
          if (!LO.Values.intersect(ZeroL).empty()) {
            SmallVector<ReturnEvalOutcome, 2> RHSOut;
            evaluateReturnOutcomes(BO->getRHS(), *RDom, LO.Lockset,
                                   LO.PendingAcquires, State, Ctx, UseVarRanges,
                                   RHSOut, Depth + 1);
            for (auto &RO : RHSOut) {
              if (!RO.Values.intersect(ZeroR).empty()) {
                ReturnEvalOutcome O = RO;
                O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
                Out.push_back(std::move(O));
              }
              if (!RO.Values.intersect(NonZeroR).empty()) {
                ReturnEvalOutcome O = std::move(RO);
                O.Values = IntRangeSet::single(TargetDom, llvm::APSInt::get(1));
                Out.push_back(std::move(O));
              }
            }
          }
        }
      }
      ApplyExprConstraint();
      return;
    }

    EmitDefault();
    ApplyExprConstraint();
    return;
  }

  if (const auto *COP = dyn_cast<AbstractConditionalOperator>(E)) {
    auto CondDom = getScalarDomain(COP->getCond()->getType());
    if (!CondDom) {
      EmitDefault();
      ApplyExprConstraint();
      return;
    }
    SmallVector<ReturnEvalOutcome, 2> CondOut;
    evaluateReturnOutcomes(COP->getCond(), *CondDom, InLockset, InPending,
                           State, Ctx, UseVarRanges, CondOut, Depth + 1);
    IntRangeSet ZeroC = IntRangeSet::single(*CondDom, llvm::APSInt::get(0));
    IntRangeSet NonZeroC = ZeroC.complement(*CondDom);
    for (const auto &CO : CondOut) {
      if (!CO.Values.intersect(NonZeroC).empty())
        evaluateReturnOutcomes(COP->getTrueExpr(), TargetDom, CO.Lockset,
                               CO.PendingAcquires, State, Ctx, UseVarRanges,
                               Out, Depth + 1);
      if (!CO.Values.intersect(ZeroC).empty())
        evaluateReturnOutcomes(COP->getFalseExpr(), TargetDom, CO.Lockset,
                               CO.PendingAcquires, State, Ctx, UseVarRanges,
                               Out, Depth + 1);
    }
    ApplyExprConstraint();
    return;
  }

  if (const auto *CallExp = dyn_cast<CallExpr>(E)) {
    unsigned BuiltinID = CallExp->getBuiltinCallee();
    if (BuiltinID == Builtin::BI__builtin_expect ||
        BuiltinID == Builtin::BI__builtin_expect_with_probability) {
      auto ArgDom = getScalarDomain(CallExp->getArg(0)->getType());
      if (!ArgDom) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      SmallVector<ReturnEvalOutcome, 2> Sub;
      evaluateReturnOutcomes(CallExp->getArg(0), *ArgDom, InLockset, InPending,
                             State, Ctx, UseVarRanges, Sub, Depth + 1);
      for (auto &SO : Sub) {
        SO.Values = reprojectRangeSet(
            castIntegralRangeSet(SO.Values, CallExp->getType(), *ASTCtx),
            TargetDom);
        if (!SO.Values.empty())
          Out.push_back(std::move(SO));
      }
      ApplyExprConstraint();
      return;
    }

    const auto *Callee = dyn_cast_or_null<NamedDecl>(CallExp->getCalleeDecl());
    if (!Callee) {
      EmitDefault();
      ApplyExprConstraint();
      return;
    }

    std::optional<llvm::scope_exit<std::function<void()>>> Cleanup;
    if (Handler.issueBetaWarnings()) {
      SxBuilder.setLookupLocalVarExpr(
          [this, LookupCtx = Ctx](const NamedDecl *D) mutable -> const Expr * {
            return LocalVarMap.lookupExpr(D, LookupCtx);
          });
      Cleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
    }

    SmallVector<ReturnEvalOutcome, 2> CallOutcomes;
    ReturnEvalOutcome InitO;
    InitO.Values = IntRangeSet::full(TargetDom);
    InitO.Lockset = InLockset;
    InitO.PendingAcquires.assign(InPending.begin(), InPending.end());
    CallOutcomes.push_back(std::move(InitO));

    SmallVector<TrylockExitSpec, 2> CallSpecs;
    SmallVector<std::pair<CapabilityExpr, LockKind>, 2> AlreadyAcquiredCaps;
    auto RecordCallSpec = [&](const Attr *At, const IntRangeSet &SuccSet,
                              const CapExprSet &Caps, LockKind LK) {
      bool AlreadyMaterialized =
          State.AcquiredTrylockAttrs.contains({CallExp, At});
      for (const auto &Cap : Caps) {
        if (Cap.shouldIgnore())
          continue;
        if (AlreadyMaterialized) {
          AlreadyAcquiredCaps.push_back({Cap, LK});
          continue;
        }
        bool Merged = false;
        for (TrylockExitSpec &Existing : CallSpecs) {
          if (Existing.Cap.equals(Cap) && Existing.LK == LK) {
            Existing.SuccessSet = Existing.SuccessSet.unionWith(SuccSet);
            Merged = true;
            break;
          }
        }
        if (!Merged)
          CallSpecs.push_back({Cap, LK, SuccSet, CallExp->getExprLoc()});
      }
    };

    for (const auto *Attr :
         Callee->specific_attrs<TryAcquireCapabilityAttr>()) {
      bool SuccBool = false;
      if (!evalTrylockSuccessBool(Attr->getSuccessValue(), *ASTCtx, SuccBool)) {
        EmitDefault();
        ApplyExprConstraint();
        return;
      }
      IntRangeSet SuccSet =
          IntRangeSet::single(TargetDom, llvm::APSInt::get(0));
      if (SuccBool)
        SuccSet = SuccSet.complement(TargetDom);
      CapExprSet Caps;
      getMutexIDs(Caps, Attr, CallExp, Callee);
      RecordCallSpec(Attr, SuccSet, Caps,
                     Attr->isShared() ? LK_Shared : LK_Exclusive);
    }

    if (CallExp->getType()->isIntegralOrEnumerationType()) {
      for (const auto *Attr :
           Callee->specific_attrs<TryAcquireCapabilityRangeAttr>()) {
        if (!Attr->getFirstSuccessValue() || !Attr->getLastSuccessValue()) {
          EmitDefault();
          ApplyExprConstraint();
          return;
        }
        auto First =
            Attr->getFirstSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        auto Last =
            Attr->getLastSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        if (!First || !Last) {
          EmitDefault();
          ApplyExprConstraint();
          return;
        }
        IntRangeSet SuccSet =
            IntRangeSet::closedRange(TargetDom, *First, *Last);
        CapExprSet Caps;
        getMutexIDs(Caps, Attr, CallExp, Callee);
        RecordCallSpec(Attr, SuccSet, Caps,
                       Attr->isShared() ? LK_Shared : LK_Exclusive);
      }
    }

    for (const TrylockExitSpec &Spec : CallSpecs) {
      bool AlreadyAcq = llvm::any_of(AlreadyAcquiredCaps, [&](const auto &P) {
        return P.first.equals(Spec.Cap) && P.second == Spec.LK;
      });
      if (AlreadyAcq)
        continue;
      IntRangeSet FailSet = Spec.SuccessSet.complement(TargetDom);
      SmallVector<ReturnEvalOutcome, 2> Next;
      for (auto &CO : CallOutcomes) {
        IntRangeSet In = CO.Values.intersect(Spec.SuccessSet);
        IntRangeSet OutSet = CO.Values.intersect(FailSet);
        if (!In.empty()) {
          ReturnEvalOutcome WithLocks = CO;
          WithLocks.Values = std::move(In);
          WithLocks.PendingAcquires.push_back({Spec.Cap, Spec.LK, Spec.Loc});
          Next.push_back(std::move(WithLocks));
        }
        if (!OutSet.empty()) {
          CO.Values = std::move(OutSet);
          Next.push_back(std::move(CO));
        }
      }
      CallOutcomes = std::move(Next);
    }

    for (auto &CO : CallOutcomes)
      if (!CO.Values.empty())
        Out.push_back(std::move(CO));
    ApplyExprConstraint();
    return;
  }

  EmitDefault();
  ApplyExprConstraint();
}

void ThreadSafetyAnalyzer::applyScopeExitCleanups(FactSet &StateSet,
                                                  const CFGBlock *B,
                                                  bool OnlyAfterReturn) {
  ThreadSafetyHandler QuietHandler;
  bool SeenReturn = false;
  unsigned CtxIdx = BlockInfo[B->getBlockID()].EntryIndex;
  LocalVarContext StmtCtx = BlockInfo[B->getBlockID()].EntryContext;

  std::optional<llvm::scope_exit<std::function<void()>>> LookupCleanup;
  if (Handler.issueBetaWarnings()) {
    SxBuilder.setLookupLocalVarExpr(
        [this, &StmtCtx](const NamedDecl *D) -> const Expr * {
          LocalVarContext LookupCtx = StmtCtx;
          return LocalVarMap.lookupExpr(D, LookupCtx);
        });
    LookupCleanup.emplace([this] { SxBuilder.setLookupLocalVarExpr(nullptr); });
  }

  auto ApplyCallee = [&](const NamedDecl *Callee, const Expr *Exp,
                         til::SExpr *Self, SourceLocation Loc,
                         bool FullyRemove) {
    if (!Callee || !Callee->hasAttrs())
      return;
    CapExprSet ExclusiveLocksToAdd, SharedLocksToAdd;
    CapExprSet ExclusiveLocksToRemove, SharedLocksToRemove,
        GenericLocksToRemove;

    for (const Attr *At : Callee->attrs()) {
      switch (At->getKind()) {
      case attr::AcquireCapability: {
        const auto *A = cast<AcquireCapabilityAttr>(At);
        getMutexIDs(A->isShared() ? SharedLocksToAdd : ExclusiveLocksToAdd, A,
                    Exp, Callee, Self);
        break;
      }
      case attr::AssertCapability: {
        const auto *A = cast<AssertCapabilityAttr>(At);
        CapExprSet AssertLocks;
        getMutexIDs(AssertLocks, A, Exp, Callee, Self);
        for (const auto &AssertLock : AssertLocks) {
          if (!AssertLock.shouldIgnore() &&
              !StateSet.findLock(FactMan, AssertLock)) {
            StateSet.removeLock(FactMan, !AssertLock);
            StateSet.addLock(FactMan,
                             FactMan.createFact<LockableFactEntry>(
                                 AssertLock,
                                 A->isShared() ? LK_Shared : LK_Exclusive, Loc,
                                 FactEntry::Asserted));
          }
        }
        break;
      }
      case attr::ReleaseCapability: {
        const auto *A = cast<ReleaseCapabilityAttr>(At);
        if (A->isGeneric())
          getMutexIDs(GenericLocksToRemove, A, Exp, Callee, Self);
        else if (A->isShared())
          getMutexIDs(SharedLocksToRemove, A, Exp, Callee, Self);
        else
          getMutexIDs(ExclusiveLocksToRemove, A, Exp, Callee, Self);
        break;
      }
      default:
        break;
      }
    }

    auto QuietRemove = [&](const CapabilityExpr &Cp) {
      if (Cp.shouldIgnore())
        return;
      if (const FactEntry *LDat = StateSet.findLock(FactMan, Cp))
        LDat->handleUnlock(StateSet, FactMan, Cp, Loc, FullyRemove,
                           QuietHandler);
    };
    for (const auto &M : ExclusiveLocksToRemove)
      QuietRemove(M);
    for (const auto &M : SharedLocksToRemove)
      QuietRemove(M);
    for (const auto &M : GenericLocksToRemove)
      QuietRemove(M);

    auto QuietAdd = [&](const CapabilityExpr &Cp, LockKind LK) {
      if (Cp.shouldIgnore())
        return;
      const auto *Entry = FactMan.createFact<LockableFactEntry>(
          Cp, LK, Loc, FactEntry::Acquired);
      if (const FactEntry *Existing = StateSet.findLock(FactMan, *Entry)) {
        Existing->handleLock(StateSet, FactMan, *Entry, QuietHandler);
      } else {
        StateSet.removeLock(FactMan, !*Entry);
        StateSet.addLock(FactMan, Entry);
      }
    };
    for (const auto &M : ExclusiveLocksToAdd)
      QuietAdd(M, LK_Exclusive);
    for (const auto &M : SharedLocksToAdd)
      QuietAdd(M, LK_Shared);
  };

  for (const auto &BI : *B) {
    if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
      const Stmt *S = CS->getStmt();
      llvm::scope_exit AdvanceCtx(
          [&] { StmtCtx = LocalVarMap.getNextContext(CtxIdx, S, StmtCtx); });
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
        }
      }
      continue;
    }
    if (OnlyAfterReturn && !SeenReturn)
      continue;
    if (!OnlyAfterReturn && SeenReturn)
      continue;

    if (BI.getKind() == CFGElement::AutomaticObjectDtor) {
      CFGAutomaticObjDtor AD = BI.castAs<CFGAutomaticObjDtor>();
      if (isa_and_nonnull<ParmVarDecl>(AD.getVarDecl()))
        continue;
      const auto *DD = AD.getDestructorDecl(*ASTCtx);
      if (!DD || !DD->hasAttrs())
        continue;
      ApplyCallee(DD, /*Exp=*/nullptr,
                  SxBuilder.translateVariable(AD.getVarDecl(), nullptr),
                  AD.getTriggerStmt()->getEndLoc(), /*FullyRemove=*/true);
    } else if (BI.getKind() == CFGElement::CleanupFunction) {
      const CFGCleanupFunction &CF = BI.castAs<CFGCleanupFunction>();
      ApplyCallee(CF.getFunctionDecl(), /*Exp=*/nullptr,
                  SxBuilder.translateVariable(CF.getVarDecl(), nullptr),
                  CF.getVarDecl()->getLocation(), /*FullyRemove=*/true);
    }
  }
}

/// Returns whether \p Cap is reached through a local pointer variable of the
/// analyzed function, e.g. 'head->lock'. If the definition of such a variable
/// could have been resolved, the variable would have been replaced by its
/// definition. Hence, the analysis does not know which object the variable
/// points to, e.g. because its value has been loaded by inline assembly.
static bool isReachedThroughUnresolvedLocal(const CapabilityExpr &Cap) {
  const til::SExpr *E = Cap.sexpr();
  while (E) {
    if (const auto *P = dyn_cast<til::Project>(E))
      E = P->record();
    else if (const auto *A = dyn_cast<til::SApply>(E))
      E = A->sfun();
    else if (const auto *C = dyn_cast<til::Cast>(E))
      E = C->expr();
    else if (const auto *U = dyn_cast<til::UnaryOp>(E))
      E = U->expr();
    else if (const auto *AI = dyn_cast<til::ArrayIndex>(E))
      E = AI->array();
    else
      break;
  }
  const auto *LP = dyn_cast_or_null<til::LiteralPtr>(E);
  const auto *VD = LP ? dyn_cast_or_null<VarDecl>(LP->clangDecl()) : nullptr;
  return VD && VD->hasLocalStorage() && !isa<ParmVarDecl>(VD) &&
         VD->getType()->isPointerType();
}

void ThreadSafetyAnalyzer::checkTrylockExitOutcome(
    const FactSet &BaseExpectedExitSet, const ReturnEvalOutcome &Outcome,
    SourceLocation DiagLoc, ThreadSafetyHandler &ExitHandler) {
  if (Outcome.Values.empty())
    return;

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

  for (const ExitPartition &P : Partitions) {
    // A capability that is held but not expected and that is reached through
    // a local pointer whose value is not known may be the same capability as
    // one that is expected but not held, e.g. 'head->lock' and
    // 'req->head->lock' after 'head = smp_load_acquire(&req->head)'. Since
    // the analysis cannot tell, do not report such pairs.
    llvm::SmallPtrSet<const FactEntry *, 2> Paired;
    for (const auto &Fact : Outcome.Lockset) {
      const FactEntry &ExitFact = FactMan[Fact];
      if (ExitFact.negative() || P.ExpectedSet.findLock(FactMan, ExitFact) ||
          !isReachedThroughUnresolvedLocal(ExitFact))
        continue;
      for (const auto &EFact : P.ExpectedSet) {
        const FactEntry &EntryFact = FactMan[EFact];
        if (EntryFact.negative() || Paired.contains(&EntryFact) ||
            Outcome.Lockset.findLock(FactMan, EntryFact) ||
            EntryFact.kind() != ExitFact.kind() ||
            EntryFact.getKind() != ExitFact.getKind())
          continue;
        Paired.insert(&EntryFact);
        Paired.insert(&ExitFact);
        break;
      }
    }

    for (const auto &Fact : Outcome.Lockset) {
      const FactEntry &ExitFact = FactMan[Fact];
      if (Paired.contains(&ExitFact))
        continue;
      if (const FactEntry *EntryFact =
              P.ExpectedSet.findLock(FactMan, ExitFact)) {
        unsigned ReentrancyA = 0, ReentrancyB = 0;
        if (const auto *LFE = dyn_cast<LockableFactEntry>(EntryFact))
          ReentrancyA = LFE->getReentrancyDepth();
        if (const auto *LFE = dyn_cast<LockableFactEntry>(&ExitFact))
          ReentrancyB = LFE->getReentrancyDepth();

        if (ReentrancyA != ReentrancyB) {
          bool MissingAcquire = ReentrancyB < ReentrancyA;
          ExitHandler.handleMutexHeldEndOfScope(
              ExitFact.getKind(), ExitFact.toString(),
              MissingAcquire ? EntryFact->loc() : ExitFact.loc(), DiagLoc,
              MissingAcquire ? LEK_NotLockedAtEndOfFunction
                             : LEK_LockedAtEndOfFunction,
              /*ReentrancyMismatch=*/true);
        } else if (EntryFact->kind() != ExitFact.kind()) {
          if (!((EntryFact->managed() || EntryFact->asserted()) &&
                (ExitFact.managed() || ExitFact.asserted()))) {
            ExitHandler.handleExclusiveAndShared(
                ExitFact.getKind(), ExitFact.toString(), ExitFact.loc(),
                EntryFact->loc());
          }
        }
      } else {
        ExitFact.handleRemovalFromIntersection(
            Outcome.Lockset, FactMan, DiagLoc, LEK_LockedAtEndOfFunction,
            ExitHandler);
      }
    }

    for (const auto &Fact : P.ExpectedSet) {
      const FactEntry &EntryFact = FactMan[Fact];
      if (Paired.contains(&EntryFact))
        continue;
      if (!Outcome.Lockset.findLock(FactMan, EntryFact)) {
        EntryFact.handleRemovalFromIntersection(P.ExpectedSet, FactMan, DiagLoc,
                                                LEK_NotLockedAtEndOfFunction,
                                                ExitHandler);
      }
    }
  }
}

namespace {

/// We use this class to visit different types of expressions in
/// CFGBlocks, and build up the lockset.
/// An expression may cause us to add or remove locks from the lockset, or else
/// output error messages related to missing locks.
/// FIXME: In future, we may be able to not inherit from a visitor.
class BuildLockset : public ConstStmtVisitor<BuildLockset> {
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
  void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *Exp);
  void VisitReturnStmt(const ReturnStmt *S);
};

} // namespace

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
      const auto *Scope = cast<ScopedLockableFactEntry>(Fact);
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
}

static const Expr *UnpackConstruction(const Expr *E) {
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
      E = UnpackConstruction(E);

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
            UnpackConstruction(Exp->getSubExpr()));
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
    if (!Analyzer->CurrentTrylockExitSpecs.empty()) {
      FactSet NonNullExitSet = FunctionExitFSet;
      llvm::APSInt One = llvm::APSInt::get(1);
      for (const auto &Spec : Analyzer->CurrentTrylockExitSpecs)
        if (Spec.SuccessSet.intersects(One, One))
          Analyzer->addLockToExpectedSet(NonNullExitSet, Spec.Cap, Spec.LK,
                                         Spec.Loc);
      Analyzer->checkPtAccess(NonNullExitSet, RetVal,
                              ReturnType->getPointeeType().isConstQualified()
                                  ? AK_Read
                                  : AK_Written,
                              POK_ReturnPointer);
    } else {
      Analyzer->checkPtAccess(FunctionExitFSet, RetVal,
                              ReturnType->getPointeeType().isConstQualified()
                                  ? AK_Read
                                  : AK_Written,
                              POK_ReturnPointer);
    }
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
/// \param RebranchIgnoresDepth Whether a reentrancy depth difference of a
/// re-branched capability is not diagnosed either. Only set at the exit
/// blocks of a try-acquire function, where the lock state is verified per
/// path.
void ThreadSafetyAnalyzer::intersectAndWarn(
    FactSet &EntrySet, const FactSet &ExitSet, SourceLocation JoinLoc,
    LockErrorKind EntryLEK, LockErrorKind ExitLEK,
    const CapExprSet *TrylockRebranchCaps, bool RebranchIgnoresDepth) {
  FactSet EntrySetOrig = EntrySet;

  auto GetFactReentrancyDepth = [](const FactEntry &FE) -> unsigned {
    if (const auto *LFE = dyn_cast<LockableFactEntry>(&FE))
      return LFE->getReentrancyDepth();
    return 0;
  };

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
          (RebranchIgnoresDepth || GetFactReentrancyDepth(EntryFact) ==
                                       GetFactReentrancyDepth(ExitFact))) {
        // Both facts have been created by the same trylock call, whose result
        // is checked again by the terminator of this block. The lock kind may
        // differ if the trylock function has range attributes for different
        // lock kinds. Keep the shared fact; the edges out of this block
        // refine the lock kind.
        if (EntryFact.kind() != ExitFact.kind()) {
          if (ExitFact.kind() == LK_Shared)
            *EntryIt = Fact;
        } else if (EntryFact.asserted() && !ExitFact.asserted()) {
          *EntryIt = Fact;
        }
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
static bool neverReturns(const CFGBlock *B) {
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
  RangeCondCache.clear();
  SwitchTables.clear();
  InlineBodyCache.clear();
  InlineExpansionCount = 0;
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

  // Compute SSA names for local variables
  LocalVarMap.traverseCFG(CFGraph, SortedGraph, BlockInfo);

  // Fill in source locations for all CFGBlocks.
  findBlockLocations(CFGraph, SortedGraph, BlockInfo);

  CapExprSet ExclusiveLocksAcquired;
  CapExprSet SharedLocksAcquired;
  CapExprSet LocksReleased;
  CurrentTrylockExitSpecs.clear();

  QualType FuncReturnType;
  if (CurrentFunction)
    FuncReturnType = CurrentFunction->getReturnType();
  else if (const auto *OMD = dyn_cast<ObjCMethodDecl>(D))
    FuncReturnType = OMD->getReturnType();

  auto AddTrylockExitSpec = [&](const CapabilityExpr &Cap, LockKind LK,
                                const IntRangeSet &SuccSet,
                                SourceLocation AttrLoc) {
    if (Cap.shouldIgnore())
      return;
    for (TrylockExitSpec &Existing : CurrentTrylockExitSpecs) {
      if (Existing.Cap.equals(Cap) && Existing.LK == LK) {
        Existing.SuccessSet = Existing.SuccessSet.unionWith(SuccSet);
        return;
      }
    }
    CurrentTrylockExitSpecs.push_back({Cap, LK, SuccSet, AttrLoc});
  };

  bool SawTryAcquireAttr = false;

  // Add locks from exclusive_locks_required and shared_locks_required
  // to initial lockset. Also turn off checking for underlying lock and unlock
  // primitives that take zero capability arguments.
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
      } else if (const auto *A = dyn_cast<TryAcquireCapabilityAttr>(Attr)) {
        if (A->args_size() == 0)
          return;
        SawTryAcquireAttr = true;
        auto RetDom = getScalarDomain(FuncReturnType);
        if (!RetDom)
          return;
        CurrentTrylockRetDom = *RetDom;
        bool SuccBool = false;
        if (!evalTrylockSuccessBool(A->getSuccessValue(), *ASTCtx, SuccBool))
          return;
        IntRangeSet SuccSet =
            IntRangeSet::single(CurrentTrylockRetDom, llvm::APSInt::get(0));
        if (SuccBool)
          SuccSet = SuccSet.complement(CurrentTrylockRetDom);
        CapExprSet AttrCaps;
        getMutexIDs(AttrCaps, A, nullptr, D);
        LockKind LK = A->isShared() ? LK_Shared : LK_Exclusive;
        for (const auto &Cap : AttrCaps)
          AddTrylockExitSpec(Cap, LK, SuccSet, D->getLocation());
      } else if (const auto *A =
                     dyn_cast<TryAcquireCapabilityRangeAttr>(Attr)) {
        if (A->args_size() == 0)
          return;
        SawTryAcquireAttr = true;
        if (FuncReturnType.isNull() || FuncReturnType->isDependentType() ||
            !FuncReturnType->isIntegralOrEnumerationType() ||
            FuncReturnType->isBooleanType())
          return;
        auto RetDom = getScalarDomain(FuncReturnType);
        if (!RetDom)
          return;
        CurrentTrylockRetDom = *RetDom;
        if (!A->getFirstSuccessValue() || !A->getLastSuccessValue() ||
            A->getFirstSuccessValue()->isValueDependent() ||
            A->getLastSuccessValue()->isValueDependent())
          return;
        auto First = A->getFirstSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        auto Last = A->getLastSuccessValue()->getIntegerConstantExpr(*ASTCtx);
        if (!First || !Last)
          return;
        IntRangeSet SuccSet =
            IntRangeSet::closedRange(CurrentTrylockRetDom, *First, *Last);
        CapExprSet AttrCaps;
        getMutexIDs(AttrCaps, A, nullptr, D);
        LockKind LK = A->isShared() ? LK_Shared : LK_Exclusive;
        for (const auto &Cap : AttrCaps)
          AddTrylockExitSpec(Cap, LK, SuccSet, D->getLocation());
      }
    }
    if (SawTryAcquireAttr && CurrentTrylockExitSpecs.empty())
      return;

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

  const bool CheckingTrylockBody = !CurrentTrylockExitSpecs.empty();
  const CFGBlock *ExitBlock = &CFGraph->getExit();
  const unsigned NumBlocks = CFGraph->getNumBlockIDs();

  CapExprSet CurrentTrylockExitCaps;
  llvm::SmallPtrSet<const ValueDecl *, 8> EscapedVars;
  llvm::SmallPtrSet<const ValueDecl *, 8> LoopModifiedVars;
  std::vector<unsigned> RPOIdx;
  std::vector<llvm::SmallPtrSet<const ValueDecl *, 4>> BlockModifiedVars;
  std::vector<bool> PureExitPathBlocks;
  std::vector<TrylockValueState> BlockExitValState;
  std::vector<SmallVector<TrylockEdgeBundle, 2>> PureBlockBundles;
  std::vector<bool> BundleOverflow;
  std::vector<FactSet> PreReturnLocksets;
  std::vector<TrylockValueState> PreReturnValStates;
  std::vector<LocalVarContext> PreReturnVarCtx;

  if (CheckingTrylockBody) {
    for (const auto &Spec : CurrentTrylockExitSpecs)
      CurrentTrylockExitCaps.push_back_nodup(Spec.Cap);

    scanTrylockVars(AC.getBody(), EscapedVars, LoopModifiedVars);

    // Collect the calls whose result is discarded: expression statements and
    // casts to void.
    DiscardedCalls.clear();
    auto CollectDiscarded = [&](auto &Self, const Stmt *S) -> void {
      if (!S || isa<LambdaExpr, BlockExpr, CapturedStmt>(S))
        return;
      auto Note = [&](const Stmt *Child) {
        const auto *E = dyn_cast_or_null<Expr>(Child);
        while (E) {
          E = E->IgnoreParens();
          if (const auto *FE = dyn_cast<FullExpr>(E)) {
            E = FE->getSubExpr();
            continue;
          }
          if (const auto *CE = dyn_cast<CastExpr>(E);
              CE && CE->getCastKind() == CK_ToVoid) {
            E = CE->getSubExpr();
            continue;
          }
          break;
        }
        if (const auto *Call = dyn_cast_or_null<CallExpr>(E))
          DiscardedCalls.insert(Call);
      };
      if (const auto *CS = dyn_cast<CompoundStmt>(S)) {
        // The value of the last statement of a statement expression is used.
        for (const Stmt *Child : CS->body())
          Note(Child);
      } else if (const auto *CE = dyn_cast<CastExpr>(S);
                 CE && CE->getCastKind() == CK_ToVoid) {
        Note(CE);
      }
      for (const Stmt *Child : S->children())
        Self(Self, Child);
    };
    CollectDiscarded(CollectDiscarded, AC.getBody());

    // The result of the last statement of a statement expression is used.
    auto UnmarkStmtExprResults = [&](auto &Self, const Stmt *S) -> void {
      if (!S)
        return;
      if (const auto *SE = dyn_cast<StmtExpr>(S))
        if (const CompoundStmt *CS = SE->getSubStmt(); CS && !CS->body_empty())
          if (const auto *E = dyn_cast<Expr>(CS->body_back()))
            if (const auto *Call =
                    dyn_cast<CallExpr>(E->IgnoreParens()->IgnoreImplicit()))
              DiscardedCalls.erase(Call);
      for (const Stmt *Child : S->children())
        Self(Self, Child);
    };
    UnmarkStmtExprResults(UnmarkStmtExprResults, AC.getBody());

    RPOIdx.assign(NumBlocks, UINT_MAX);
    BlockModifiedVars.resize(NumBlocks);
    unsigned CurRPO = 0;
    for (const CFGBlock *B : *SortedGraph) {
      RPOIdx[B->getBlockID()] = CurRPO++;
      scanBlockModifiedVars(B, BlockModifiedVars[B->getBlockID()]);
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
      getTerminatorTrylockCaps(B, TCaps);
      if (!TCaps.empty())
        continue;

      if (!isPureExitBlock(B, CurrentTrylockExitCaps))
        continue;

      PureExitPathBlocks[B->getBlockID()] = true;
    }

    BlockExitValState.resize(NumBlocks);
    PureBlockBundles.resize(NumBlocks);
    BundleOverflow.assign(NumBlocks, false);
    PreReturnLocksets.resize(NumBlocks);
    PreReturnValStates.resize(NumBlocks);
    PreReturnVarCtx.resize(NumBlocks, LocalVarMap.getEmptyContext());
  }

  auto SameShortCircuits = [](const TrylockValueState &A,
                              const TrylockValueState &B) {
    if (A.ShortCircuitedOps.size() != B.ShortCircuitedOps.size())
      return false;
    for (const auto &[BO, Val] : A.ShortCircuitedOps) {
      auto It = B.ShortCircuitedOps.find(BO);
      if (It == B.ShortCircuitedOps.end() || It->second != Val)
        return false;
    }
    return true;
  };

  auto SameUnmaterializedDefs = [](const TrylockValueState &A,
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
  };

  auto AddOrMergeBundle = [&](unsigned BlockID, TrylockEdgeBundle Candidate) {
    if (BundleOverflow[BlockID] || Candidate.ValState.Infeasible)
      return;
    auto &Bundles = PureBlockBundles[BlockID];
    for (TrylockEdgeBundle &Existing : Bundles) {
      if (factSetsEquivalent(Existing.Lockset, Candidate.Lockset) &&
          SameShortCircuits(Existing.ValState, Candidate.ValState) &&
          Existing.ValState.AcquiredTrylockAttrs ==
              Candidate.ValState.AcquiredTrylockAttrs &&
          Existing.ValState.ConsumedTrylockAttrs ==
              Candidate.ValState.ConsumedTrylockAttrs &&
          Existing.ValState.DiscardedTrylockCalls ==
              Candidate.ValState.DiscardedTrylockCalls &&
          SameUnmaterializedDefs(Existing.ValState, Candidate.ValState)) {
        unionIntoValueState(Existing.ValState, Candidate.ValState, *ASTCtx);
        return;
      }
    }
    if (Bundles.size() >= 64) {
      BundleOverflow[BlockID] = true;
      Bundles.clear();
      return;
    }
    Bundles.push_back(std::move(Candidate));
  };

  auto IntersectFactSetsQuietly = [&](FactSet &Acc, const FactSet &Other) {
    FactSet AccOrig = Acc;
    for (const auto &Fact : AccOrig) {
      const FactEntry &AFact = FactMan[Fact];
      const FactEntry *BFact = Other.findLock(FactMan, AFact);
      if (!BFact || AFact.negative() != BFact->negative()) {
        Acc.removeLock(FactMan, AFact);
        continue;
      }
      FactSet::iterator It = Acc.findLockIter(FactMan, AFact);
      if (It == Acc.end())
        continue;
      unsigned DepthA = 0, DepthB = 0;
      if (const auto *LFE = dyn_cast<LockableFactEntry>(&AFact))
        DepthA = LFE->getReentrancyDepth();
      if (const auto *LFE = dyn_cast<LockableFactEntry>(BFact))
        DepthB = LFE->getReentrancyDepth();
      if (DepthA != DepthB) {
        if (DepthB < DepthA)
          Acc.replaceLock(FactMan, It, BFact);
      } else if (AFact.kind() != BFact->kind()) {
        if (BFact->kind() == LK_Shared)
          Acc.replaceLock(FactMan, It, BFact);
      } else if (AFact.asserted() && !BFact->asserted()) {
        Acc.replaceLock(FactMan, It, BFact);
      }
    }
  };

  for (const auto *CurrBlock : *SortedGraph) {
    unsigned CurrBlockID = CurrBlock->getBlockID();
    CFGBlockInfo *CurrBlockInfo = &BlockInfo[CurrBlockID];

    // Use the default initial lockset in case there are no predecessors.
    VisitedBlocks.insert(CurrBlock);

    if (CheckingTrylockBody && CurrBlock == ExitBlock) {
      for (CFGBlock::const_pred_iterator PI = CurrBlock->pred_begin(),
                                         PE = CurrBlock->pred_end();
           PI != PE; ++PI) {
        if (*PI == nullptr || RPOIdx[(*PI)->getBlockID()] == UINT_MAX ||
            !VisitedBlocks.alreadySet(*PI))
          continue;
        if (!neverReturns(*PI) && BlockInfo[(*PI)->getBlockID()].Reachable) {
          CurrBlockInfo->Reachable = true;
          break;
        }
      }
      continue;
    }

    const bool IsPureBlock =
        CheckingTrylockBody && PureExitPathBlocks[CurrBlockID];
    TrylockValueState CurrValState;
    if (CheckingTrylockBody && CurrBlock != &CFGraph->getEntry())
      CurrValState.Infeasible = true;
    SmallVector<const CFGBlock *, 2> UnvisitedBackPreds;

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
    for (CFGBlock::const_pred_iterator PI = CurrBlock->pred_begin(),
         PE  = CurrBlock->pred_end(); PI != PE; ++PI) {
      if (*PI == nullptr ||
          (CheckingTrylockBody && RPOIdx[(*PI)->getBlockID()] == UINT_MAX))
        continue;
      // if *PI -> CurrBlock is a back edge
      if (!VisitedBlocks.alreadySet(*PI)) {
        if (CheckingTrylockBody)
          UnvisitedBackPreds.push_back(*PI);
        continue;
      }

      unsigned PrevBlockID = (*PI)->getBlockID();
      CFGBlockInfo *PrevBlockInfo = &BlockInfo[PrevBlockID];

      // Ignore edges from blocks that can't return.
      if (neverReturns(*PI) || !PrevBlockInfo->Reachable)
        continue;

      // Okay, we can reach this block from the entry.
      CurrBlockInfo->Reachable = true;

      FactSet PrevLockset;
      if (CheckingTrylockBody) {
        TrylockValueState EdgeValState = BlockExitValState[PrevBlockID];
        getEdgeLockset(PrevLockset, PrevBlockInfo->ExitSet, *PI, CurrBlock,
                       &EdgeValState.AcquiredTrylockAttrs,
                       &EdgeValState.ConsumedTrylockAttrs);
        constrainValueStateOnEdge(EdgeValState, *PI, CurrBlock, EscapedVars);
        materializeNarrowedTrylocks(PrevLockset, EdgeValState);
        unionIntoValueState(CurrValState, EdgeValState, *ASTCtx);

        if (IsPureBlock) {
          if (BundleOverflow[PrevBlockID]) {
            BundleOverflow[CurrBlockID] = true;
            PureBlockBundles[CurrBlockID].clear();
          } else if (PureExitPathBlocks[PrevBlockID]) {
            for (const TrylockEdgeBundle &SrcBnd :
                 PureBlockBundles[PrevBlockID]) {
              TrylockEdgeBundle NextBnd = SrcBnd;
              constrainValueStateOnEdge(NextBnd.ValState, *PI, CurrBlock,
                                        EscapedVars);
              if (!NextBnd.ValState.Infeasible) {
                materializeNarrowedTrylocks(NextBnd.Lockset, NextBnd.ValState);
                AddOrMergeBundle(CurrBlockID, std::move(NextBnd));
              }
            }
          } else if (!EdgeValState.Infeasible) {
            AddOrMergeBundle(CurrBlockID,
                             {PrevLockset, std::move(EdgeValState)});
          }
        }
      } else {
        getEdgeLockset(PrevLockset, PrevBlockInfo->ExitSet, *PI, CurrBlock);
      }

      if (!LocksetInitialized) {
        CurrBlockInfo->EntrySet = PrevLockset;
        LocksetInitialized = true;
      } else {
        // Surprisingly 'continue' doesn't always produce back edges, because
        // the CFG has empty "transition" blocks where they meet with the end
        // of the regular loop body. We still want to diagnose them as loop.
        if (isa_and_nonnull<ContinueStmt>((*PI)->getTerminatorStmt())) {
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
            if (IsPureBlock) {
              for (const auto &Cap : CurrentTrylockExitCaps)
                TerminatorTrylockCaps.push_back_nodup(Cap);
            } else {
              getTerminatorTrylockCaps(CurrBlock, TerminatorTrylockCaps);
            }
            TerminatorTrylockCapsComputed = true;
          }
          intersectAndWarn(CurrBlockInfo->EntrySet, PrevLockset,
                           CurrBlockInfo->EntryLoc, LEK_LockedSomePredecessors,
                           LEK_LockedSomePredecessors, &TerminatorTrylockCaps,
                           /*RebranchIgnoresDepth=*/IsPureBlock);
        }
      }
    }

    // Skip rest of block if it's not reachable.
    if (!CurrBlockInfo->Reachable)
      continue;

    if (CheckingTrylockBody) {
      if (!UnvisitedBackPreds.empty()) {
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
          for (auto LPI = LB->pred_begin(), LPE = LB->pred_end(); LPI != LPE;
               ++LPI) {
            const CFGBlock *Pred = *LPI;
            if (!Pred || RPOIdx[Pred->getBlockID()] == UINT_MAX)
              continue;
            if (LoopBlocks.insert(Pred).second)
              Worklist.push_back(Pred);
          }
        }

        // A block of an irreducible cycle may be entered from outside the
        // cycle through another block of the cycle. Hence, it is reachable
        // even if all its forward predecessor edges are infeasible. Since
        // its state is not known, start from an empty state.
        if (CurrValState.Infeasible && IrreducibleLoop)
          CurrValState = TrylockValueState();
        auto EraseModifiedVar = [&](const ValueDecl *VD) {
          CurrValState.VarRanges.erase(VD);
          CurrValState.UnmaterializedVarDefs.erase(VD);
        };
        if (IrreducibleLoop) {
          for (const ValueDecl *VD : LoopModifiedVars)
            EraseModifiedVar(VD);
          for (const CFGBlock *B : *SortedGraph)
            for (const ValueDecl *VD : BlockModifiedVars[B->getBlockID()])
              EraseModifiedVar(VD);
        } else {
          llvm::SmallPtrSet<const ValueDecl *, 8> LoopModVars;
          for (const CFGBlock *LB : LoopBlocks)
            for (const ValueDecl *VD : BlockModifiedVars[LB->getBlockID()])
              LoopModVars.insert(VD);

          llvm::SmallPtrSet<const ValueDecl *, 8> CandidateVars;
          for (const ValueDecl *VD : LoopModVars) {
            if (!isTrackableLocalVar(VD, EscapedVars))
              continue;
            if (auto It = CurrValState.VarRanges.find(VD);
                It != CurrValState.VarRanges.end() && !It->second.empty())
              CandidateVars.insert(VD);
          }

          if (!CandidateVars.empty() && CandidateVars.size() <= 8 &&
              LoopBlocks.size() <= 64) {
            SmallVector<const CFGBlock *, 16> OrderedLoopBlocks;
            OrderedLoopBlocks.reserve(LoopBlocks.size());
            for (const CFGBlock *B : *SortedGraph)
              if (LoopBlocks.contains(B))
                OrderedLoopBlocks.push_back(B);

            llvm::DenseMap<unsigned, TrylockValueState> SimExit;
            while (!CandidateVars.empty()) {
              SimExit.clear();
              TrylockValueState HeaderState;
              HeaderState.Infeasible = false;
              for (const auto &[VD, R] : CurrValState.VarRanges)
                if (!LoopModVars.contains(VD) || CandidateVars.contains(VD))
                  HeaderState.VarRanges.try_emplace(VD, R);

              for (const CFGBlock *LB : OrderedLoopBlocks) {
                TrylockValueState LBS;
                if (LB == CurrBlock) {
                  LBS = HeaderState;
                } else {
                  LBS.Infeasible = true;
                  bool HasInnerBackEdge = false;
                  for (auto LPI = LB->pred_begin(), LPE = LB->pred_end();
                       LPI != LPE; ++LPI) {
                    const CFGBlock *Pred = *LPI;
                    if (!Pred || RPOIdx[Pred->getBlockID()] == UINT_MAX ||
                        neverReturns(Pred) || !LoopBlocks.contains(Pred))
                      continue;
                    if (RPOIdx[Pred->getBlockID()] >=
                        RPOIdx[LB->getBlockID()]) {
                      HasInnerBackEdge = true;
                      continue;
                    }
                    auto It = SimExit.find(Pred->getBlockID());
                    if (It == SimExit.end() || It->second.Infeasible)
                      continue;
                    TrylockValueState EdgeS = It->second;
                    constrainValueStateOnEdge(EdgeS, Pred, LB, EscapedVars);
                    unionIntoValueState(LBS, EdgeS, *ASTCtx);
                  }
                  if (!LBS.Infeasible && HasInnerBackEdge) {
                    for (const ValueDecl *MVD : LoopModVars) {
                      LBS.VarRanges.erase(MVD);
                      LBS.UnmaterializedVarDefs.erase(MVD);
                    }
                    LBS.ExprRanges.clear();
                    LBS.ShortCircuitedOps.clear();
                  }
                }

                if (!LBS.Infeasible) {
                  unsigned SimCtxIdx = BlockInfo[LB->getBlockID()].EntryIndex;
                  LocalVarContext SimStmtCtx =
                      BlockInfo[LB->getBlockID()].EntryContext;
                  for (const CFGElement &BI : *LB) {
                    if (std::optional<CFGStmt> CS = BI.getAs<CFGStmt>()) {
                      const Stmt *S = CS->getStmt();
                      updateValueStateForStmt(LBS, S, SimStmtCtx, EscapedVars);
                      SimStmtCtx =
                          LocalVarMap.getNextContext(SimCtxIdx, S, SimStmtCtx);
                    }
                  }
                }
                SimExit.try_emplace(LB->getBlockID(), std::move(LBS));
              }

              SmallVector<const ValueDecl *, 4> FailedVars;
              for (const CFGBlock *BP : UnvisitedBackPreds) {
                if (neverReturns(BP))
                  continue;
                auto It = SimExit.find(BP->getBlockID());
                if (It == SimExit.end() || It->second.Infeasible)
                  continue;
                TrylockValueState BackS = It->second;
                constrainValueStateOnEdge(BackS, BP, CurrBlock, EscapedVars);
                if (BackS.Infeasible)
                  continue;
                for (const ValueDecl *CVD : CandidateVars) {
                  auto BackIt = BackS.VarRanges.find(CVD);
                  auto EntryIt = HeaderState.VarRanges.find(CVD);
                  if (BackIt == BackS.VarRanges.end() ||
                      EntryIt == HeaderState.VarRanges.end() ||
                      !BackIt->second.subsetOfSet(EntryIt->second)) {
                    if (!llvm::is_contained(FailedVars, CVD))
                      FailedVars.push_back(CVD);
                  }
                }
              }

              if (FailedVars.empty())
                break;
              for (const ValueDecl *FVD : FailedVars)
                CandidateVars.erase(FVD);
            }
          } else {
            CandidateVars.clear();
          }

          for (const ValueDecl *VD : LoopModVars) {
            CurrValState.UnmaterializedVarDefs.erase(VD);
            if (!CandidateVars.contains(VD))
              CurrValState.VarRanges.erase(VD);
          }
        }
        CurrValState.ExprRanges.clear();
        CurrValState.ShortCircuitedOps.clear();
      }
      if (IsPureBlock && !BundleOverflow[CurrBlockID] &&
          !PureBlockBundles[CurrBlockID].empty()) {
        FactSet BundleEntrySet = PureBlockBundles[CurrBlockID].front().Lockset;
        for (const TrylockEdgeBundle &Bnd :
             llvm::drop_begin(PureBlockBundles[CurrBlockID]))
          IntersectFactSetsQuietly(BundleEntrySet, Bnd.Lockset);
        CurrBlockInfo->EntrySet = std::move(BundleEntrySet);
      }
    }

    BuildLockset LocksetBuilder(this, *CurrBlockInfo, ExpectedFunctionExitSet);
    unsigned ValCtxIdx = CurrBlockInfo->EntryIndex;
    LocalVarContext ValStmtCtx = CurrBlockInfo->EntryContext;

    // Visit all the statements in the basic block.
    for (const auto &BI : *CurrBlock) {
      switch (BI.getKind()) {
        case CFGElement::Statement: {
          CFGStmt CS = BI.castAs<CFGStmt>();
          const Stmt *S = CS.getStmt();
          if (CheckingTrylockBody) {
            if (isa<ReturnStmt>(S)) {
              PreReturnLocksets[CurrBlockID] = LocksetBuilder.FSet;
              PreReturnValStates[CurrBlockID] = CurrValState;
              PreReturnVarCtx[CurrBlockID] = ValStmtCtx;
            }
            updateValueStateForStmt(CurrValState, S, ValStmtCtx, EscapedVars);
            if (IsPureBlock && !BundleOverflow[CurrBlockID]) {
              for (auto &Bnd : PureBlockBundles[CurrBlockID])
                updateValueStateForStmt(Bnd.ValState, S, ValStmtCtx,
                                        EscapedVars);
            }
            ValStmtCtx = LocalVarMap.getNextContext(ValCtxIdx, S, ValStmtCtx);
          }
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
          if (isa_and_nonnull<ParmVarDecl>(AD.getVarDecl()))
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
    if (CheckingTrylockBody) {
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
              return CurrBlockInfo->EntrySet.findLock(FactMan, Cap) &&
                     !CurrBlockInfo->ExitSet.findLock(FactMan, Cap);
            }))
          CurrValState.ConsumedTrylockAttrs.insert(Key);
      }
      BlockExitValState[CurrBlockID] = std::move(CurrValState);
      if (IsPureBlock && !BundleOverflow[CurrBlockID]) {
        for (auto &Bnd : PureBlockBundles[CurrBlockID])
          applyScopeExitCleanups(Bnd.Lockset, CurrBlock,
                                 /*OnlyAfterReturn=*/false);
      }
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

  if (CheckingTrylockBody) {
    DedupThreadSafetyHandler DedupHandler(Handler);

    for (CFGBlock::const_pred_iterator PI = ExitBlock->pred_begin(),
                                       PE = ExitBlock->pred_end();
         PI != PE; ++PI) {
      const CFGBlock *PredBlock = *PI;
      if (!PredBlock || !VisitedBlocks.alreadySet(PredBlock))
        continue;
      unsigned PredID = PredBlock->getBlockID();
      const CFGBlockInfo &PredInfo = BlockInfo[PredID];
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

      auto VerifyExitOutcome = [&](ReturnEvalOutcome &Outcome) {
        for (const PendingTrylockAcquire &PA : Outcome.PendingAcquires) {
          const auto *Entry = FactMan.createFact<LockableFactEntry>(
              PA.Cap, PA.LK, PA.Loc, FactEntry::Acquired);
          if (Entry->shouldIgnore())
            continue;
          if (!Entry->negative()) {
            CapabilityExpr NegC = !*Entry;
            if (Outcome.Lockset.findLock(FactMan, NegC)) {
              Outcome.Lockset.removeLock(FactMan, NegC);
            } else if (inCurrentScope(*Entry) && !Entry->asserted() &&
                       !Entry->reentrant()) {
              DedupHandler.handleNegativeNotHeld(Entry->getKind(),
                                                 Entry->toString(),
                                                 NegC.toString(), Entry->loc());
            }
          }
          if (!Entry->asserted() && !Entry->declared()) {
            GlobalBeforeSet->checkBeforeAfter(
                Entry->valueDecl(), Outcome.Lockset, *this, Entry->loc(),
                Entry->getKind(), &DedupHandler);
          }
          if (const FactEntry *Cp = Outcome.Lockset.findLock(FactMan, *Entry)) {
            if (!Entry->asserted())
              Cp->handleLock(Outcome.Lockset, FactMan, *Entry, DedupHandler);
          } else {
            Outcome.Lockset.addLock(FactMan, Entry);
          }
        }
        applyScopeExitCleanups(Outcome.Lockset, PredBlock,
                               /*OnlyAfterReturn=*/true);
        checkTrylockExitOutcome(ExpectedFunctionExitSet, Outcome, DiagLoc,
                                DedupHandler);
      };

      // If there are too many paths to track the lock state per path, the
      // joined lock state is too imprecise to verify the postconditions
      // without reporting false positives. Skip the verification instead.
      if (BundleOverflow[PredID])
        continue;

      if (PureExitPathBlocks[PredID]) {
        LocalVarContext EvalCtx =
            RS ? PreReturnVarCtx[PredID] : PredInfo.ExitContext;
        for (const TrylockEdgeBundle &Bnd : PureBlockBundles[PredID]) {
          TrylockValueState EvalState = Bnd.ValState;
          if (!RS) {
            constrainValueStateOnEdge(EvalState, PredBlock, ExitBlock,
                                      EscapedVars);
            if (EvalState.Infeasible)
              continue;
          }
          SmallVector<ReturnEvalOutcome, 2> Outcomes;
          evaluateReturnWithPendingTrylocks(RetVal, Bnd.Lockset, EvalState,
                                            EvalCtx, Outcomes);
          for (ReturnEvalOutcome &Outcome : Outcomes)
            VerifyExitOutcome(Outcome);
        }
      } else if (RS) {
        SmallVector<ReturnEvalOutcome, 2> Outcomes;
        evaluateReturnWithPendingTrylocks(
            RetVal, PreReturnLocksets[PredID], PreReturnValStates[PredID],
            PreReturnVarCtx[PredID], Outcomes);
        for (ReturnEvalOutcome &Outcome : Outcomes)
          VerifyExitOutcome(Outcome);
      } else {
        TrylockValueState FallthroughState = BlockExitValState[PredID];
        constrainValueStateOnEdge(FallthroughState, PredBlock, ExitBlock,
                                  EscapedVars);
        if (!FallthroughState.Infeasible) {
          ReturnEvalOutcome Outcome;
          Outcome.Values = IntRangeSet::full(CurrentTrylockRetDom);
          Outcome.Lockset = PredInfo.ExitSet;
          checkTrylockExitOutcome(ExpectedFunctionExitSet, Outcome, DiagLoc,
                                  DedupHandler);
        }
      }
    }

    Handler.leaveFunction(CurrentFunction);
    return;
  }

  // FIXME: Should we call this function for all blocks which exit the function?
  intersectAndWarn(ExpectedFunctionExitSet, Final.ExitSet, Final.ExitLoc,
                   LEK_LockedAtEndOfFunction, LEK_NotLockedAtEndOfFunction);

  Handler.leaveFunction(CurrentFunction);
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
