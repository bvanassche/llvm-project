//===- ThreadSafetyInternal.h - Thread safety internals ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Declarations of the classes that implement the thread safety
// analysis. They are shared by the source files of the analysis and
// are not part of its public interface.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYINTERNAL_H
#define LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYINTERNAL_H

#include "ThreadSafetyRanges.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/Analysis/Analyses/ThreadSafety.h"
#include "clang/Analysis/Analyses/ThreadSafetyCommon.h"
#include "clang/Analysis/Analyses/ThreadSafetyTIL.h"
#include "clang/Analysis/Analyses/ThreadSafetyUtil.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ImmutableMap.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/TrailingObjects.h"
#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace clang {
namespace threadSafety {

/// A set of CapabilityExpr objects, which are compiled from thread safety
/// attributes on a function.
class LLVM_LIBRARY_VISIBILITY CapExprSet
    : public SmallVector<CapabilityExpr, 4> {
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
class LLVM_LIBRARY_VISIBILITY FactEntry : public CapabilityExpr {
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

  LockKind kind() const { return LKind; }
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
    return (LKind == LK_Exclusive) || (LK == LK_Shared);
  }
};

using FactID = unsigned short;

/// FactManager manages the memory for all facts that are created during
/// the analysis of a single routine.
class LLVM_LIBRARY_VISIBILITY FactManager {
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
class LLVM_LIBRARY_VISIBILITY FactSet {
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
  bool isEmpty(const FactManager &FactMan) const {
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

  bool removeLock(FactManager &FM, const CapabilityExpr &CapE) {
    unsigned n = FactIDs.size();
    if (n == 0)
      return false;

    for (unsigned i = 0; i < n - 1; ++i) {
      if (FM[FactIDs[i]].matches(CapE)) {
        FactIDs[i] = FactIDs[n - 1];
        FactIDs.pop_back();
        return true;
      }
    }
    if (FM[FactIDs[n - 1]].matches(CapE)) {
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

  const FactEntry *findLock(const FactManager &FM,
                            const CapabilityExpr &CapE) const {
    auto I =
        llvm::find_if(*this, [&](FactID ID) { return FM[ID].matches(CapE); });
    return I != end() ? &FM[*I] : nullptr;
  }

  const FactEntry *findLockUniv(const FactManager &FM,
                                const CapabilityExpr &CapE) const {
    auto I = llvm::find_if(
        *this, [&](FactID ID) -> bool { return FM[ID].matchesUniv(CapE); });
    return I != end() ? &FM[*I] : nullptr;
  }

  const FactEntry *findPartialMatch(const FactManager &FM,
                                    const CapabilityExpr &CapE) const {
    auto I = llvm::find_if(*this, [&](FactID ID) -> bool {
      return FM[ID].partiallyMatches(CapE);
    });
    return I != end() ? &FM[*I] : nullptr;
  }

  bool containsMutexDecl(const FactManager &FM, const ValueDecl *Vd) const {
    auto I = llvm::find_if(
        *this, [&](FactID ID) -> bool { return FM[ID].valueDecl() == Vd; });
    return I != end();
  }
};

class BuildLockset;
class ThreadSafetyAnalyzer;
class TrylockBodyVerifier;

/// The body of a trivial inline or constexpr function whose return value can
/// be evaluated in terms of its parameters.
struct TrivialInlineBody {
  const FunctionDecl *DefFD = nullptr;
  const Expr *SingleRet = nullptr;
  const Expr *CondExpr = nullptr;
  const Expr *ThenRet = nullptr;
  const Expr *ElseRet = nullptr;
  llvm::SmallPtrSet<const ValueDecl *, 8> CalleeEscaped;
  mutable std::optional<std::optional<unsigned>> IdentityParam;

  /// The canonical declaration of parameter \p I.
  const ValueDecl *param(unsigned I) const {
    return cast<ValueDecl>(DefFD->getParamDecl(I)->getCanonicalDecl());
  }
};

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

  BeforeInfo *insertAttrExprs(const ValueDecl *Vd,
                              ThreadSafetyAnalyzer &Analyzer);

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

/// Translation-unit-wide cache shared across thread-safety analyses of
/// functions in the same translation unit.
class ThreadSafetyCache {
public:
  BeforeSet BSet;
  llvm::DenseMap<const FunctionDecl *, std::unique_ptr<TrivialInlineBody>>
      InlineBodyCache;
  llvm::DenseMap<const StmtExpr *, const Expr *> PureStmtExprCache;
};

class LocalVariableMap;

using LocalVarContext = llvm::ImmutableMap<const NamedDecl *, unsigned>;

/// A side (entry or exit) of a CFG node.
enum CFGBlockSide { CBS_Entry, CBS_Exit };

/// CFGBlockInfo is a struct which contains all the information that is
/// maintained for each block in the CFG.  See LocalVariableMap for more
/// information about the contexts.
struct LLVM_LIBRARY_VISIBILITY CFGBlockInfo {
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
class LLVM_LIBRARY_VISIBILITY LocalVariableMap {
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

    // Whether this is a reference to a definition of a variable whose value
    // may have been modified through an alias since that definition.
    // lookupValueExpr() does not look through such a reference; lookupExpr()
    // does.
    bool Clobbered = false;

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
  // The local variables that the statements of each CFG block declare or
  // modify directly, indexed by block ID. Only computed on request.
  std::vector<llvm::SmallPtrSet<const ValueDecl *, 4>> BlockModifiedVars;
  // Local variables that may be modified other than by a direct assignment,
  // e.g. because their address is taken; see traverseCFG().
  llvm::SmallPtrSet<const ValueDecl *, 8> EscapedVars;

public:
  LocalVariableMap() {
    // index 0 is a placeholder for undefined variables (aka phi-nodes).
    VarDefinitions.push_back(VarDefinition(nullptr, 0, 0, getEmptyContext()));
  }

  /// Record that \p VD may be modified other than by a direct assignment.
  /// Must be called before traverseCFG().
  void addEscapedVar(const ValueDecl *VD) {
    EscapedVars.insert(cast<ValueDecl>(VD->getCanonicalDecl()));
  }

  /// Return whether the value of \p D can be tracked through its definitions.
  /// This does not hold for variables without local storage, whose
  /// initializer only runs once, nor for volatile and __block variables,
  /// since these may be modified behind the analysis' back, nor for
  /// references to anything but a temporary, since a direct assignment to
  /// the referenced variable modifies them. Variables whose address escapes
  /// are tracked until they may be modified through an alias; see
  /// traverseCFG().
  bool hasTrackableValue(const NamedDecl *D) const {
    const auto *VD = dyn_cast<VarDecl>(D);
    if (!VD || !VD->hasLocalStorage() || VD->getType().isVolatileQualified() ||
        VD->hasAttr<BlocksAttr>())
      return false;
    return !VD->getType()->isReferenceType() ||
           isa_and_nonnull<MaterializeTemporaryExpr>(
               stripNoOpExprWrappers(VD->getInit()));
  }

  /// Look up a definition, within the given context.
  const VarDefinition *lookup(const NamedDecl *D, Context Ctx) {
    const unsigned *i = Ctx.lookup(D);
    if (!i)
      return nullptr;
    assert(*i < VarDefinitions.size());
    return &VarDefinitions[*i];
  }

  /// Look up the definition for D within the given context.  Returns
  /// NULL if the expression is not statically known.  If successful, also
  /// modifies Ctx to hold the context of the return Expr.
  const Expr *lookupExpr(const NamedDecl *D, Context &Ctx) const {
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

  /// Like lookupExpr(), but return null if the value of \p D may differ from
  /// its last definition. Use this when evaluating the value of a variable,
  /// e.g. a trylock result.
  const Expr *lookupValueExpr(const NamedDecl *D, Context &Ctx) const {
    if (Ctx.isEmpty() || !hasTrackableValue(D))
      return nullptr;
    const unsigned *P = Ctx.lookup(D);
    return P && !isClobbered(*P) ? lookupExpr(D, Ctx) : nullptr;
  }

  Context getEmptyContext() { return ContextFactory.getEmptyMap(); }

  Context clearDefinitionIfSet(const NamedDecl *D, Context Ctx) {
    if (const unsigned *DefID = Ctx.lookup(D); DefID && *DefID != 0)
      return clearDefinition(D, Ctx);
    return Ctx;
  }

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
    llvm::errs() << "." << i << " " << ((const void *)Dec);
  }

  /// Dumps an ASCII representation of the variable map to llvm::errs()
  void dump() {
    for (unsigned i = 1, e = VarDefinitions.size(); i < e; ++i) {
      const Expr *Exp = VarDefinitions[i].Exp;
      unsigned Ref = VarDefinitions[i].DirectRef;

      dumpVarDefinitionName(i);
      llvm::errs() << " = ";
      if (Exp)
        Exp->dump();
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

  /// Builds the variable map. If \p RecordModifiedVars is set, also records
  /// the local variables that each block modifies; see
  /// getBlockModifiedVars().
  ///
  /// Since a pointer or reference to a variable recorded by addEscapedVar()
  /// may be stored anywhere, the value of such a variable may change at
  /// every statement that may modify an object through a pointer or
  /// reference or that may run unknown code, e.g. a call. Such a statement
  /// clobbers the definition of the variable until it is assigned a new
  /// value directly; lookupValueExpr() fails for clobbered definitions.
  void traverseCFG(CFG *CFGraph, const PostOrderCFGView *SortedGraph,
                   std::vector<CFGBlockInfo> &BlockInfo,
                   const llvm::SmallPtrSetImpl<const Stmt *> &UnevaluatedStmts,
                   bool RecordModifiedVars = false);

  /// The local variables that the statements of the reachable block
  /// \p BlockID declare or modify by a direct assignment or increment or
  /// decrement. Only available if traverseCFG() was asked to record these.
  const llvm::SmallPtrSetImpl<const ValueDecl *> &
  getBlockModifiedVars(unsigned BlockID) const {
    assert(BlockID < BlockModifiedVars.size() &&
           "traverseCFG() did not record the modified variables");
    return BlockModifiedVars[BlockID];
  }

protected:
  friend class VarMapBuilder;

  // Resolve any definition ID down to its non-reference base ID.
  unsigned getCanonicalDefinitionID(unsigned ID) const {
    while (ID > 0 && VarDefinitions[ID].isReference())
      ID = VarDefinitions[ID].CanonicalRef;
    return ID;
  }

  // Get the current context index
  unsigned getContextIndex() { return SavedContexts.size() - 1; }

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

  // Whether the value of a variable may have been modified through an alias
  // since the last definition that the definition ID refers to.
  bool isClobbered(unsigned ID) const {
    for (; ID > 0 && VarDefinitions[ID].isReference();
         ID = VarDefinitions[ID].DirectRef)
      if (VarDefinitions[ID].Clobbered)
        return true;
    return false;
  }

  // Record that the value of D may have been modified through an alias.
  Context clobberDefinition(const NamedDecl *D, Context Ctx) {
    const unsigned *ID = Ctx.lookup(D);
    if (!ID || *ID == 0 || isClobbered(*ID))
      return Ctx;
    Ctx = addReference(D, *ID, Ctx);
    VarDefinitions.back().Clobbered = true;
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

  // Remove a definition entirely from the context.
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

class LLVM_LIBRARY_VISIBILITY LockableFactEntry final : public FactEntry {
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

struct LLVM_LIBRARY_VISIBILITY UnderlyingCapability {
  CapabilityExpr Cap;
  UnderlyingCapabilityKind Kind;
};

/// The reentrancy depth of \p Fact, or zero if \p Fact is not a lockable
/// fact.
inline unsigned getFactReentrancyDepth(const FactEntry &Fact) {
  if (const auto *LFE = dyn_cast<LockableFactEntry>(&Fact))
    return LFE->getReentrancyDepth();
  return 0;
}

/// Whether to keep \p B instead of \p A when joining two facts for the same
/// capability without a diagnostic: the shared fact subsumes the exclusive
/// fact, and the non-asserted fact is the one to track.
inline bool preferJoinedFact(const FactEntry &A, const FactEntry &B) {
  if (A.kind() != B.kind())
    return B.kind() == LK_Shared;
  return A.asserted() && !B.asserted();
}

class LLVM_LIBRARY_VISIBILITY ScopedLockableFactEntry final
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

/// The maximum number of inline helper expansions per CFG block of the
/// analyzed function. This is the only budget of inline helper expansion:
/// it bounds the cost of analyzing helpers that call other helpers many
/// times without making the analysis of a block depend on the number of
/// conditions in the blocks before it. The nesting depth of expansions is
/// bounded by MaxConstrainExprDepth since each expansion increases the
/// recursion depth of the expression evaluation.
static constexpr unsigned MaxInlineExpansions = 512;

/// The maximum number of intervals of a range that is stored in a value
/// state. Wider ranges are over-approximated such that the cost of copying
/// and joining value states does not grow with the number of conditions.
static constexpr unsigned MaxStateRangeIntervals = 16;
/// The maximum recursion depth of constrainExprComparison().
static constexpr unsigned MaxConstrainExprDepth = 24;
/// The maximum recursion depth of evaluateTrylockRangeCond().
static constexpr unsigned MaxRangeCondDepth = 256;
/// The maximum number of recursive evaluation steps per top-level expression
/// range or condition evaluation.
static constexpr unsigned MaxEvalSteps = 2048;

/// Class which implements the core thread safety analysis routines.
class LLVM_LIBRARY_VISIBILITY ThreadSafetyAnalyzer {
  friend class BuildLockset;
  friend class TrylockBodyVerifier;
  friend class ReturnValueForker;
  friend class BeforeSet;

  llvm::BumpPtrAllocator Bpa;
  til::MemRegionRef Arena;
  SExprBuilder SxBuilder;

  ThreadSafetyHandler &Handler;
  ASTContext *ASTCtx = nullptr;
  const FunctionDecl *CurrentFunction = nullptr;
  LocalVariableMap LocalVarMap;
  // Maps constructed objects to `this` placeholder prior to initialization.
  llvm::SmallDenseMap<const Expr *, til::LiteralPtr *> ConstructedObjects;
  FactManager FactMan;
  std::vector<CFGBlockInfo> BlockInfo;

  ThreadSafetyCache *GlobalCache;

public:
  ThreadSafetyAnalyzer(ThreadSafetyHandler &H, ThreadSafetyCache *Cache)
      : Arena(&Bpa), SxBuilder(Arena), Handler(H), FactMan(Bpa),
        GlobalCache(Cache) {}

  bool inCurrentScope(const CapabilityExpr &CapE);

  void addLock(FactSet &FSet, const FactEntry *Entry, bool ReqAttr = false,
               ThreadSafetyHandler *DiagHandler = nullptr);
  void removeLock(FactSet &FSet, const CapabilityExpr &CapE,
                  SourceLocation UnlockLoc, bool FullyRemove, LockKind Kind);

  template <typename AttrType>
  void getMutexIDs(CapExprSet &Mtxs, AttrType *Attr, const Expr *Exp,
                   const NamedDecl *D, til::SExpr *Self = nullptr);

  /// The capabilities that a call acquires and releases.
  struct CallLockEffects {
    CapExprSet ExclusiveLocksToAdd, SharedLocksToAdd;
    CapExprSet ExclusiveLocksToRemove, SharedLocksToRemove,
        GenericLocksToRemove;
  };
  bool collectLockEffects(const Attr *At, const Expr *Exp, const NamedDecl *D,
                          til::SExpr *Self, CallLockEffects &Effects);

  /// An implicit call at the end of the scope of a variable.
  struct ScopeExitCall {
    const NamedDecl *Callee;
    til::SExpr *Self;
    SourceLocation Loc;
  };
  std::optional<ScopeExitCall> getScopeExitCall(const CFGElement &BI);

  using IntDomain = threadSafety::IntDomain;
  using IntRangeSet = threadSafety::IntRangeSet;

  using AcquiredTrylockKey = std::pair<const CallExpr *, const Attr *>;

  struct TrylockExitSpec {
    CapabilityExpr Cap;
    LockKind LK;
    IntRangeSet SuccessSet;
    SourceLocation Loc;
  };

  /// A trylock result that is no longer stored in any variable, e.g. because
  /// the variable has been overwritten.
  struct OverwrittenTrylockDef {
    const Expr *DefE;
    LocalVarContext Ctx;
    QualType Ty;
    // The values that the variable may have had when it was overwritten, or
    // std::nullopt if unknown.
    std::optional<IntRangeSet> Allowed;
    // Whether the definition may have been executed in an earlier iteration
    // of a loop. Its result then is another result than the one that the
    // same definition yields in the current iteration.
    bool FromEarlierIteration = false;
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
    // Trylock results that are no longer stored in any variable. The
    // capabilities of these calls may still have been acquired.
    SmallVector<OverwrittenTrylockDef, 1> OverwrittenTrylockDefs;
    // Pointer variables that have been dereferenced unconditionally since
    // their last modification. These are assumed to be non-null when
    // evaluating their value, unless a branch condition contradicts that.
    llvm::SmallPtrSet<const ValueDecl *, 4> DerefNonNullVars;
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
    // Whether the capability has only been acquired on some of the paths
    // that have been merged into an outcome. Such a capability may be leaked
    // but does not count as held for the capabilities that are expected.
    bool MayOnly = false;
  };

  struct ReturnEvalOutcome {
    IntRangeSet Values;
    FactSet Lockset;
    SmallVector<PendingTrylockAcquire, 2> PendingAcquires;
  };

  TrylockBodyVerifier *CurrentVerifier = nullptr;

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
  llvm::DenseMap<
      const SwitchStmt *,
      SmallVector<std::pair<IntDomain, std::unique_ptr<SwitchCaseTable>>, 1>>
      SwitchTables;
  /// Return the case table for \p SS in domain \p Dom.
  const SwitchCaseTable &getSwitchCaseTable(const SwitchStmt *SS,
                                            const IntDomain &Dom);

  /// A trylock call that has been executed and whose result has been tested
  /// by a branch condition on the current path. Values are the values that
  /// the call may have returned on the current path. AcquiredAttrs maps the
  /// attributes whose capabilities have been acquired by branching on the
  /// result of the call and are still held to the values that the call may
  /// have returned on the paths on which they are held. These capabilities
  /// are held on every path, except at the entry of a block with several
  /// predecessors until the attributes whose capabilities are not held on
  /// every predecessor have been removed.
  /// ConsumedValues maps the attributes whose capabilities have been
  /// acquired by branching on the result of the call and then released to
  /// the values that the call may have returned on the paths on which they
  /// have been released. Branching on the result of the call again does not
  /// acquire the capabilities of an attribute for these values.
  struct PendingTrylockRange {
    using AttrValueMap = llvm::SmallDenseMap<const Attr *, IntRangeSet, 2>;
    const CallExpr *Call;
    LocalVarContext CallCtx = LocalVarContext(nullptr);
    IntDomain Dom;
    IntRangeSet Values;
    AttrValueMap AcquiredAttrs;
    AttrValueMap ConsumedValues;
  };
  using PendingTrylockRanges = SmallVector<PendingTrylockRange, 1>;

  struct TrylockRangeCondResult {
    const CallExpr *Call = nullptr;
    const NamedDecl *Callee = nullptr;
    LocalVarContext CallCtx = LocalVarContext(nullptr);
    IntDomain Dom;
    IntRangeSet TrueSet;
    IntRangeSet FalseSet;
    /// For the condition of a terminator that is a logical operator, the
    /// values of the call for which its left-hand side short-circuits to the
    /// successor that the right-hand side reaches if it is false (for '&&')
    /// or true (for '||'), bypassing the block with the terminator.
    IntRangeSet ShortCircuitSet = {};
  };

  std::optional<unsigned> getIdentityInlineParamIndex(const CallExpr *CallExp);
  const Expr *skipValuePreservingWrappers(const Expr *E, LocalVarContext *C,
                                          bool IgnoreSideEffects = true);
  const CallExpr *unwrapValuePreservingToCallExpr(const Expr *E,
                                                  LocalVarContext &C);
  const CallExpr *unwrapTrylockValueExpr(const Expr *E, LocalVarContext &C);
  bool isGuaranteedZeroOrOneExpr(const Expr *E, LocalVarContext C);
  TrylockRangeCondResult evaluateInlineCallRangeCond(
      const CallExpr *InlineCall, LocalVarContext C,
      std::optional<std::pair<BinaryOperator::Opcode, llvm::APSInt>> OuterCmp =
          std::nullopt);
  TrylockRangeCondResult evaluateTrylockRangeCond(const Stmt *Cond,
                                                  LocalVarContext C,
                                                  unsigned Depth = 0);
  TrylockRangeCondResult evaluateTrylockRangeCondImpl(const Stmt *Cond,
                                                      LocalVarContext C,
                                                      unsigned Depth);
  /// Helper of evaluateTrylockRangeCondImpl() for comparisons.
  TrylockRangeCondResult evaluateTrylockCmpCond(const BinaryOperator *BOP,
                                                LocalVarContext C,
                                                unsigned Depth);
  /// Helper of evaluateTrylockRangeCondImpl() for logical operators.
  TrylockRangeCondResult evaluateTrylockLogicalOpCond(const BinaryOperator *BOP,
                                                      LocalVarContext C,
                                                      unsigned Depth);
  /// Evaluate \p ConstSide, the operand of the comparison \p BOP that is
  /// compared with a trylock result, as a constant.
  std::optional<llvm::APSInt>
  evaluateTrylockCmpConstSide(const Expr *ConstSide, const BinaryOperator *BOP);
  /// Recognize GNU binary conditional expressions (x ?: false_const) Op K.
  TrylockRangeCondResult
  evaluateTrylockBinaryCondCmp(const Expr *CondSide, const Expr *ConstSide,
                               BinaryOperator::Opcode SideOp, LocalVarContext C,
                               const BinaryOperator *BOP);
  /// Evaluate the equality comparison \p BOP of the boolean trylock
  /// condition \p BoolSide with the constant \p ConstSide.
  TrylockRangeCondResult evaluateTrylockBoolEq(const Expr *BoolSide,
                                               const Expr *ConstSide,
                                               LocalVarContext C,
                                               const BinaryOperator *BOP,
                                               unsigned Depth);
  // Results of evaluateTrylockRangeCond(), keyed by the condition, the root of
  // the local variable context, and whether the inline expansion budget had
  // already been exhausted on entry. Each entry retains its
  // LocalVarContext so the root pointer remains valid for the lifetime of the
  // cache. Memoization keeps the evaluation of chains of logical operators on
  // variables linear instead of exponential.
  llvm::DenseMap<std::tuple<const Stmt *, const void *, unsigned>,
                 std::pair<LocalVarContext, TrylockRangeCondResult>>
      RangeCondCache;
  llvm::DenseMap<std::pair<const CFGBlock *, const void *>,
                 std::pair<LocalVarContext, TrylockRangeCondResult>>
      TerminatorCondCache;
  const PostOrderCFGView *CurrentSortedGraph = nullptr;
  bool HasTrylockCall = false;
  // For each trylock call branched on by a terminator, the last block in
  // CurrentSortedGraph whose terminator branches on that call.
  llvm::DenseMap<const CallExpr *, const CFGBlock *> LastTrylockCondBlock;
  bool BuiltLogicalOpTermBlock = false;
  llvm::DenseMap<const BinaryOperator *, unsigned> LogicalOpTermBlock;
  LocalVarContext getLogicalOpLHSContext(const BinaryOperator *BOP,
                                         LocalVarContext C);
  TrylockRangeCondResult evaluateTerminatorTrylockCond(const Stmt *Cond,
                                                       LocalVarContext C,
                                                       unsigned Depth = 0);
  bool getTerminatorTrylockCond(const CFGBlock *Block,
                                TrylockRangeCondResult &Res,
                                const SwitchCaseTable *&Table,
                                SmallVectorImpl<const CastExpr *> &SwitchCasts);

  void getEdgeLockset(
      FactSet &Result, const FactSet &ExitSet, const CFGBlock *PredBlock,
      const CFGBlock *CurrBlock,
      llvm::SmallDenseSet<AcquiredTrylockKey, 4> *AcquiredAttrs = nullptr,
      const llvm::SmallDenseSet<AcquiredTrylockKey, 4> *ConsumedAttrs = nullptr,
      SmallVectorImpl<OverwrittenTrylockDef> *MixedEdgeCalls = nullptr,
      PendingTrylockRanges *Pending = nullptr);
  void getTrylockMutexIDs(CapExprSet &Mtxs, const Attr *A, const Expr *Exp,
                          const NamedDecl *D);
  bool collectTrylockCaps(const Attr *A, const Expr *CallExp,
                          const NamedDecl *Callee, CapExprSet &ExclusiveCaps,
                          CapExprSet &SharedCaps);
  void addTrylockFacts(FactSet &FSet, const CapExprSet &ExclusiveCaps,
                       const CapExprSet &SharedCaps, SourceLocation Loc);
  std::optional<IntRangeSet> getTrylockSuccessSet(const Attr *A,
                                                  const IntDomain &Dom) const;
  std::optional<IntRangeSet>
  getCombinedTrylockSuccessSet(const Attr *A, const Expr *CallExp,
                               const NamedDecl *Callee, const IntDomain &Dom,
                               bool ExactInt = true);

  void getTerminatorTrylockCaps(const CFGBlock *Block, CapExprSet &Caps,
                                const PendingTrylockRanges *Pending = nullptr);

  std::optional<IntDomain> getScalarDomain(QualType Ty) const;
  IntDomain getTrylockCallDomain(const CallExpr *CallExp) const;
  bool isTrackableLocalVar(
      const ValueDecl *VD,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const;
  const ValueDecl *extractTrackableVarExpr(
      const Expr *E,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars) const;
  /// The context in which the value of an expression is evaluated.
  struct RangeEvalCtx {
    /// The escaped local variables of the function or inline helper whose
    /// body contains the expression. Null outside trylock implementations.
    const llvm::SmallPtrSetImpl<const ValueDecl *> *EscapedVars = nullptr;
    /// Whether a dereferenced pointer may be assumed to be valid. Only set
    /// while evaluating return values, such that null checks after a
    /// dereference remain feasible in branch conditions.
    bool AssumeDerefValid = false;
    /// The expressions whose entries in TrylockValueState::ExprRanges record
    /// the values that these evaluated to while evaluating the expression
    /// that contains them, e.g. the trylock calls, conditions and variable
    /// references that ReturnValueForker has forked on. Modifying a variable
    /// in another operand does not change these values.
    const llvm::SmallPtrSetImpl<const Expr *> *PinnedExprs = nullptr;

    RangeEvalCtx withDeref(bool V) const {
      RangeEvalCtx C = *this;
      C.AssumeDerefValid = V;
      return C;
    }
    RangeEvalCtx
    withEscaped(const llvm::SmallPtrSetImpl<const ValueDecl *> *E) const {
      RangeEvalCtx C = *this;
      C.EscapedVars = E;
      return C;
    }
  };
  std::optional<IntRangeSet>
  evaluatePureExprRange(const Expr *E, const TrylockValueState &State,
                        const RangeEvalCtx &EC, unsigned Depth = 0);
  std::optional<IntRangeSet>
  evaluatePureDeclRefRange(const DeclRefExpr *DRE, const IntDomain &Dom,
                           const TrylockValueState &State,
                           const RangeEvalCtx &EC);
  std::optional<IntRangeSet>
  evaluatePureCastRange(const CastExpr *CE, const IntDomain &Dom,
                        const TrylockValueState &State, const RangeEvalCtx &EC,
                        unsigned Depth);
  std::optional<IntRangeSet>
  evaluatePureCallRange(const CallExpr *CallExp, const IntDomain &Dom,
                        const TrylockValueState &State, const RangeEvalCtx &EC,
                        unsigned Depth);
  std::optional<IntRangeSet>
  evaluatePureUnaryRange(const UnaryOperator *UO, const IntDomain &Dom,
                         const TrylockValueState &State, const RangeEvalCtx &EC,
                         unsigned Depth);
  std::optional<IntRangeSet>
  evaluatePureBinaryRange(const BinaryOperator *BO, const IntDomain &Dom,
                          const TrylockValueState &State,
                          const RangeEvalCtx &EC, unsigned Depth);
  std::optional<IntRangeSet> evaluatePureConditionalRange(
      const AbstractConditionalOperator *COP, const IntDomain &Dom,
      const TrylockValueState &State, const RangeEvalCtx &EC, unsigned Depth);
  bool isValidDerefPointer(const Expr *PtrE, const TrylockValueState &State,
                           const RangeEvalCtx &EC, unsigned Depth);
  bool isValidObjectLValue(const Expr *E, const TrylockValueState &State,
                           const RangeEvalCtx &EC, unsigned Depth);
  bool constrainExprComparison(TrylockValueState &State, const Expr *VarSide,
                               BinaryOperator::Opcode EffectiveOp,
                               const llvm::APSInt &KVal, const RangeEvalCtx &EC,
                               unsigned Depth = 0);
  void constrainLeafCondition(TrylockValueState &State, const Expr *Cond,
                              bool WantTrue, const RangeEvalCtx &EC,
                              unsigned Depth = 0);
  void constrainCastCondition(const CastExpr *CE, TrylockValueState &State,
                              bool WantTrue, const RangeEvalCtx &EC,
                              unsigned Depth);
  void constrainCallCondition(const CallExpr *CallExp, TrylockValueState &State,
                              bool WantTrue, const RangeEvalCtx &EC,
                              unsigned Depth);
  void constrainStmtExprCondition(const StmtExpr *SE, TrylockValueState &State,
                                  bool WantTrue, const RangeEvalCtx &EC,
                                  unsigned Depth);
  void constrainBinaryCondition(const BinaryOperator *BO,
                                TrylockValueState &State, bool WantTrue,
                                const RangeEvalCtx &EC, unsigned Depth);
  void constrainBinaryConditionalCondition(const BinaryConditionalOperator *BCO,
                                           TrylockValueState &State,
                                           bool WantTrue,
                                           const RangeEvalCtx &EC,
                                           unsigned Depth);
  void constrainConditionalCondition(const ConditionalOperator *CO,
                                     TrylockValueState &State, bool WantTrue,
                                     const RangeEvalCtx &EC, unsigned Depth);
  void constrainInlineRetExpr(
      TrylockValueState &S, const Expr *RetE, bool WantTrue,
      const std::optional<std::pair<BinaryOperator::Opcode, llvm::APSInt>>
          &OuterCmp,
      const IntDomain &RetDom, const RangeEvalCtx &CalleeEC,
      unsigned Depth = 0);
  llvm::ArrayRef<const ValueDecl *> getSubtreeModifiedVars(const Stmt *S);
  llvm::ArrayRef<const ValueDecl *> getSubtreeReferencedVars(const Stmt *S);
  bool exprReferencesAnyVar(const Stmt *S,
                            llvm::ArrayRef<const ValueDecl *> Vars);
  bool exprReferencesModifiedVars(const Stmt *RefRoot, const Stmt *ModRoot) {
    return exprReferencesAnyVar(RefRoot, getSubtreeModifiedVars(ModRoot));
  }
  // Subtrees of unevaluated operands, e.g. of noexcept or of the arguments of
  // __builtin_constant_p(). These may be CFG elements but are not executed.
  llvm::SmallPtrSet<const Stmt *, 8> UnevaluatedStmts;
  // The variables declared in these subtrees, e.g. in a statement expression.
  // Their destructors and cleanup functions do not run either.
  llvm::SmallPtrSet<const VarDecl *, 4> UnevaluatedVarDecls;
  void collectUnevaluatedStmts(CFG *CFGraph);

  // Functions that are being expanded inline and the expansion depth. Used to
  // prevent recursive inline expansion and to only cache the results of
  // expansions that are not nested in other expansions.
  llvm::SmallPtrSet<const FunctionDecl *, 4> ActiveInlineCallees;
  unsigned InlineDepth = 0;
  // The number of inline expansions performed for the current CFG block.
  unsigned InlineExpansionCount = 0;
  // The number of recursive steps performed in the current top-level
  // expression or condition evaluation.
  unsigned EvalStepCount = 0;
  // Whether the current inline/condition evaluation hit a depth or expansion
  // budget cutoff and therefore must not be cached.
  mutable bool InlineEvalHitCutoff = false;
  // Results of evaluatePureExprRange() for calls of inline helpers, keyed by
  // profileInlineCallCacheKey(). The result of expanding a helper only depends
  // on the callee and on the ranges of its arguments. Caching it keeps calls
  // that are repeated many times, e.g. in conditions unrelated to the tracked
  // values, from exhausting MaxInlineExpansions.
  llvm::DenseMap<llvm::FoldingSetNodeIDRef, std::optional<IntRangeSet>>
      InlineCallRangeCache;
  // The effect of constrainLeafCondition() on the parameters of an inline
  // helper whose call is used as a condition.
  struct InlineCondResult {
    bool Infeasible = false;
    SmallVector<std::optional<IntRangeSet>, 4> ParamRanges;
  };
  // Results of constrainLeafCondition() for calls of inline helpers, keyed by
  // profileInlineCallCacheKey().
  llvm::DenseMap<llvm::FoldingSetNodeIDRef, InlineCondResult> InlineCondCache;
  // Per-function caches of the variables modified or referenced within a
  // statement subtree, backed by Bpa.
  llvm::DenseMap<llvm::PointerIntPair<const Stmt *, 1, bool>,
                 llvm::ArrayRef<const ValueDecl *>>
      SubtreeModifiedVarsCache;
  llvm::DenseMap<const Stmt *, llvm::ArrayRef<const ValueDecl *>>
      SubtreeReferencedVarsCache;

  /// Marks a function as being expanded inline for the lifetime of this
  /// object, preventing recursive expansion.
  class InlineExpansionScope {
    ThreadSafetyAnalyzer &Analyzer;
    const FunctionDecl *FD;

  public:
    InlineExpansionScope(ThreadSafetyAnalyzer &Analyzer,
                         const TrivialInlineBody &Info)
        : Analyzer(Analyzer), FD(Info.DefFD) {
      Analyzer.ActiveInlineCallees.insert(FD);
      ++Analyzer.InlineDepth;
      ++Analyzer.InlineExpansionCount;
    }
    ~InlineExpansionScope() {
      --Analyzer.InlineDepth;
      Analyzer.ActiveInlineCallees.erase(FD);
    }
    InlineExpansionScope(const InlineExpansionScope &) = delete;
    InlineExpansionScope &operator=(const InlineExpansionScope &) = delete;
  };

  /// If beta warnings are enabled, makes the SExpr builder look up local
  /// variables in a local variable context for the lifetime of this object.
  class LocalVarLookupScope {
    ThreadSafetyAnalyzer &Analyzer;
    bool Active;
    std::function<const Expr *(const NamedDecl *)> Prev;

  public:
    /// Look up local variables in a copy of \p Ctx.
    LocalVarLookupScope(ThreadSafetyAnalyzer &Analyzer, LocalVarContext Ctx)
        : Analyzer(Analyzer), Active(Analyzer.Handler.issueBetaWarnings()) {
      if (Active)
        Prev = Analyzer.SxBuilder.setLookupLocalVarExpr(
            [&Analyzer, Ctx](const NamedDecl *D) mutable -> const Expr * {
              return Analyzer.LocalVarMap.lookupExpr(D, Ctx);
            });
    }
    /// Look up local variables in the context that \p Ctx points to at the
    /// time of each lookup.
    LocalVarLookupScope(ThreadSafetyAnalyzer &Analyzer,
                        const LocalVarContext *Ctx)
        : Analyzer(Analyzer), Active(Analyzer.Handler.issueBetaWarnings()) {
      if (Active)
        Prev = Analyzer.SxBuilder.setLookupLocalVarExpr(
            [&Analyzer, Ctx](const NamedDecl *D) -> const Expr * {
              LocalVarContext LookupCtx = *Ctx;
              return Analyzer.LocalVarMap.lookupExpr(D, LookupCtx);
            });
    }
    ~LocalVarLookupScope() {
      if (Active)
        Analyzer.SxBuilder.setLookupLocalVarExpr(std::move(Prev));
    }
    LocalVarLookupScope(const LocalVarLookupScope &) = delete;
    LocalVarLookupScope &operator=(const LocalVarLookupScope &) = delete;
  };

  const TrivialInlineBody *
  lookupTrivialInlineBody(const CallExpr *CallExp) const;
  SmallVector<std::optional<IntRangeSet>, 4>
  evaluateInlineArgRanges(const CallExpr *CallExp,
                          const TrylockValueState &State,
                          const RangeEvalCtx &EC, unsigned Depth);
  bool profileInlineCallCacheKey(
      llvm::FoldingSetNodeID &ID, const FunctionDecl *DefFD, unsigned Kind,
      ArrayRef<std::optional<IntRangeSet>> ArgRanges) const;
  TrylockValueState
  makeCalleeState(const TrivialInlineBody &Info,
                  ArrayRef<std::optional<IntRangeSet>> ArgRanges) const;
  void forEachInlineReturn(
      const TrivialInlineBody &Info, const TrylockValueState &Init,
      const RangeEvalCtx &EC, unsigned Depth,
      llvm::function_ref<void(const Expr *, const TrylockValueState &)> F);
  void constrainInlineReturns(
      TrylockValueState &State, const TrivialInlineBody &Info,
      const RangeEvalCtx &EC, unsigned Depth,
      llvm::function_ref<void(TrylockValueState &, const Expr *)> F);
  const TrivialInlineBody *
  getCachedTrivialInlineBody(const CallExpr *CallExp) const;
  const Expr *getCachedPureStmtExpr(const StmtExpr *SE) const;

  bool join(const FactEntry &A, const FactEntry &B, SourceLocation JoinLoc,
            LockErrorKind EntryLEK, LockErrorKind ExitLEK,
            bool ReportMissingAcquire, ThreadSafetyHandler &H);

  void intersectAndWarn(
      FactSet &EntrySet, const FactSet &ExitSet, SourceLocation JoinLoc,
      LockErrorKind EntryLEK, LockErrorKind ExitLEK,
      llvm::function_ref<bool(const FactEntry &)> IsIgnored = nullptr,
      bool RebranchIgnoresDepth = false, bool ReportMissingAcquires = false,
      ThreadSafetyHandler *DiagHandler = nullptr);

  void intersectAndWarn(FactSet &EntrySet, const FactSet &ExitSet,
                        SourceLocation JoinLoc, LockErrorKind LEK) {
    intersectAndWarn(EntrySet, ExitSet, JoinLoc, LEK, LEK);
  }

  void
  markEscapedLocalVars(AnalysisDeclContext &AC,
                       llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars);
  void joinPendingTrylockRanges(ArrayRef<PendingTrylockRanges> PredEdgePendings,
                                bool HasUnvisitedPred,
                                PendingTrylockRanges &EntryPending);
  void dropUnheldPendingAcquires(PendingTrylockRanges &EntryPending,
                                 const CFGBlockInfo *CurrBlockInfo);
  void updatePendingTrylockRanges(PendingTrylockRanges &EntryPending,
                                  const CFGBlock *CurrBlock,
                                  const CFGBlockInfo *CurrBlockInfo);
  bool addTrylockExitSpecs(const Attr *Attr, const NamedDecl *D,
                           SmallVectorImpl<TrylockExitSpec> &ExitSpecs,
                           IntDomain &RetDom);
  bool computeEntryLockset(const NamedDecl *D, const CFG &CFGraph,
                           const PostOrderCFGView &SortedGraph,
                           CFGBlockInfo &Initial,
                           CapExprSet &ExclusiveLocksAcquired,
                           CapExprSet &SharedLocksAcquired,
                           CapExprSet &LocksReleased,
                           SmallVectorImpl<TrylockExitSpec> &TrylockExitSpecs,
                           IntDomain &TrylockRetDom,
                           bool &UnmodeledTryAcquireAttr);
  FactSet computeExpectedExitSet(const NamedDecl *D, const FactSet &EntrySet,
                                 const CapExprSet &ExclusiveLocksAcquired,
                                 const CapExprSet &SharedLocksAcquired,
                                 const CapExprSet &LocksReleased);
  void
  joinPredecessors(const CFGBlock *CurrBlock, CFGBlockInfo *CurrBlockInfo,
                   PostOrderCFGView::CFGBlockSet &VisitedBlocks,
                   TrylockBodyVerifier *Verifier,
                   const std::vector<PendingTrylockRanges> &BlockExitPending,
                   PendingTrylockRanges &EntryPending);
  void visitBlockElements(const CFGBlock *CurrBlock,
                          BuildLockset &LocksetBuilder, AnalysisDeclContext &AC,
                          TrylockBodyVerifier *Verifier);
  void checkBackEdgeLocksets(const CFGBlock *CurrBlock,
                             PostOrderCFGView::CFGBlockSet &VisitedBlocks);
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

// Defined in ThreadSafety.cpp.
LLVM_LIBRARY_VISIBILITY Expr *ignoreNoOpCastSingleStep(Expr *E);
LLVM_LIBRARY_VISIBILITY const DeclRefExpr *unwrapDirectLValueDRE(const Expr *E);
LLVM_LIBRARY_VISIBILITY const DeclRefExpr *
unwrapUnconditionalLValueDRE(const Expr *E, unsigned Depth = 0);
LLVM_LIBRARY_VISIBILITY void
collectModifiedLValueDREs(const Expr *E,
                          SmallVectorImpl<const DeclRefExpr *> &DREs,
                          unsigned Depth = 0);
/// If \p E takes the address of an lvalue, possibly through no-op and
/// pointer casts, the right operand of a comma or the arms of a conditional
/// operator, add the variables that the lvalue may designate to \p DREs.
/// Return whether \p E takes the address of an lvalue.
LLVM_LIBRARY_VISIBILITY bool
collectAddrOfDREs(const Expr *E, SmallVectorImpl<const DeclRefExpr *> &DREs,
                  unsigned Depth = 0);
LLVM_LIBRARY_VISIBILITY void forEachInvalidatedCallOrCtorArgDRE(
    const Stmt *S, llvm::function_ref<void(const DeclRefExpr *)> Fn);
LLVM_LIBRARY_VISIBILITY bool
getStaticBooleanValue(const Expr *E, const ASTContext &Ctx, bool &TCond);
/// The value of the integral or enumeration expression \p E if it can be
/// computed without side effects and without undefined behavior when \p E
/// is evaluated at run time, or std::nullopt otherwise. Unlike
/// getIntegralOrEnumConstantExpr(), \p E is not evaluated in a manifestly
/// constant-evaluated context, e.g. __builtin_is_constant_evaluated()
/// evaluates to false, and no diagnostics are emitted.
LLVM_LIBRARY_VISIBILITY std::optional<llvm::APSInt>
evaluateRuntimeIntConstant(const Expr *E, const ASTContext &Ctx);
LLVM_LIBRARY_VISIBILITY bool isTrylockAttr(const Attr *A);
LLVM_LIBRARY_VISIBILITY bool hasTrylockAttr(const Decl *D);
LLVM_LIBRARY_VISIBILITY bool isSharedTrylockAttr(const Attr *A);
LLVM_LIBRARY_VISIBILITY bool trylockAttrAppliesTo(const Attr *A,
                                                  QualType RetTy);
LLVM_LIBRARY_VISIBILITY const NamedDecl *
getTrylockCallee(const CallExpr *CallExp);
LLVM_LIBRARY_VISIBILITY bool
isEvaluatedUnaryExprOrTypeTrait(const UnaryExprOrTypeTraitExpr *TE);
LLVM_LIBRARY_VISIBILITY bool neverReturns(const CFGBlock *B);
LLVM_LIBRARY_VISIBILITY const Expr *unpackConstruction(const Expr *E);

// Defined in ThreadSafetyValueEval.cpp.
LLVM_LIBRARY_VISIBILITY bool isConversionFunctionCast(const CastExpr *CE);
LLVM_LIBRARY_VISIBILITY bool isValuePreservingCast(const CastExpr *CE,
                                                   const ASTContext &Ctx);
LLVM_LIBRARY_VISIBILITY bool isBuiltinExpectCall(const CallExpr *CallExp);
LLVM_LIBRARY_VISIBILITY void
forEachDeclVLAExpr(const DeclStmt *DS, bool IncludeTopLevelVLA,
                   llvm::function_ref<void(const Expr *)> Fn);
/// Call \p Fn for the size expressions of the variable length array types
/// in the type \p QT.
LLVM_LIBRARY_VISIBILITY void
forEachTypeVLAExpr(QualType QT, llvm::function_ref<void(const Expr *)> Fn);
LLVM_LIBRARY_VISIBILITY void
forEachEvaluatedDeclVLAStmt(const DeclStmt *DS, const ASTContext &Ctx,
                            bool IncludeTopLevelVLA,
                            llvm::function_ref<void(const Stmt *)> Fn);
LLVM_LIBRARY_VISIBILITY bool isScopedLockable(const TagDecl *TD);
LLVM_LIBRARY_VISIBILITY bool hasThreadSafetyCallEffects(const NamedDecl *Callee,
                                                        const Expr *CallOrCtor);
LLVM_LIBRARY_VISIBILITY ThreadSafetyAnalyzer::IntRangeSet
validObjectPtrRangeSet(const ThreadSafetyAnalyzer::IntDomain &Dom);
LLVM_LIBRARY_VISIBILITY bool
exprReferencesAnyVar(const Stmt *S,
                     const llvm::SmallPtrSetImpl<const ValueDecl *> &Vars);
LLVM_LIBRARY_VISIBILITY void eraseModifiedVarsFromState(
    ThreadSafetyAnalyzer::TrylockValueState &State,
    llvm::ArrayRef<const ValueDecl *> ModVars,
    const llvm::SmallPtrSetImpl<const Expr *> *PinnedExprs = nullptr);
LLVM_LIBRARY_VISIBILITY bool stmtContainsExpr(const Stmt *Root,
                                              const Expr *Target);
LLVM_LIBRARY_VISIBILITY void
addOverwrittenTrylockDef(ThreadSafetyAnalyzer::TrylockValueState &State,
                         ThreadSafetyAnalyzer::OverwrittenTrylockDef Def,
                         bool CheckUnmaterialized = true);
LLVM_LIBRARY_VISIBILITY ThreadSafetyAnalyzer::OverwrittenTrylockDef
makeOverwrittenTrylockDef(
    const ValueDecl *VD, const std::pair<const Expr *, LocalVarContext> &Def,
    std::optional<ThreadSafetyAnalyzer::IntRangeSet> Allowed);
LLVM_LIBRARY_VISIBILITY void
unionIntoValueState(ThreadSafetyAnalyzer::TrylockValueState &Dst,
                    const ThreadSafetyAnalyzer::TrylockValueState &Src,
                    const ASTContext &Ctx);
LLVM_LIBRARY_VISIBILITY void
restrictVarRange(ThreadSafetyAnalyzer::TrylockValueState &State,
                 const ValueDecl *VD,
                 const ThreadSafetyAnalyzer::IntDomain &Dom,
                 const ThreadSafetyAnalyzer::IntRangeSet &Constraint);

// Defined in ThreadSafetyTrylockCond.cpp.
LLVM_LIBRARY_VISIBILITY std::pair<bool, bool>
getBranchEdgeKinds(const CFGBlock *Pred, const CFGBlock *Succ);
LLVM_LIBRARY_VISIBILITY ThreadSafetyAnalyzer::IntRangeSet
getSwitchEdgeSet(const ThreadSafetyAnalyzer::SwitchCaseTable &Table,
                 const CFGBlock *Succ);

// Defined in ThreadSafetyTrylockVerify.cpp.
LLVM_LIBRARY_VISIBILITY bool
isDiscardedValue(const Expr *E, const ParentMap &PM, const ASTContext &Ctx,
                 llvm::function_ref<bool(const ValueDecl *)> IsTrackedVar,
                 bool *ReachedBranchCond = nullptr);

/// The trylock attributes of \p D in declaration order.
inline auto trylockAttrs(const Decl *D) {
  return llvm::make_filter_range(D->attrs(), isTrylockAttr);
}

/// The maximum number of edge bundles, i.e. distinct lock and value states,
/// that are tracked per block on paths that lead to a function exit.
static constexpr unsigned MaxBundlesPerBlock = 64;

/// Verifies the implementation of a function with a try_acquire attribute
/// while ThreadSafetyAnalyzer::runAnalysis() traverses its CFG: tracks the
/// values of the local variables and, for the blocks on paths to the exit
/// that do not modify the lock state, the lock and value states per path, and
/// checks at each exit of the function that the capabilities that are held
/// match the return value. runAnalysis() calls begin() before and
/// verifyExits() after the traversal, and the remaining public member
/// functions while it visits each block.
class LLVM_LIBRARY_VISIBILITY TrylockBodyVerifier {
  friend class ReturnValueForker;

public:
  using IntDomain = ThreadSafetyAnalyzer::IntDomain;
  using IntRangeSet = ThreadSafetyAnalyzer::IntRangeSet;
  using AcquiredTrylockKey = ThreadSafetyAnalyzer::AcquiredTrylockKey;
  using TrylockExitSpec = ThreadSafetyAnalyzer::TrylockExitSpec;
  using TrylockValueState = ThreadSafetyAnalyzer::TrylockValueState;
  using TrylockEdgeBundle = ThreadSafetyAnalyzer::TrylockEdgeBundle;
  using OverwrittenTrylockDef = ThreadSafetyAnalyzer::OverwrittenTrylockDef;
  using PendingTrylockAcquire = ThreadSafetyAnalyzer::PendingTrylockAcquire;
  using ReturnEvalOutcome = ThreadSafetyAnalyzer::ReturnEvalOutcome;
  using RangeEvalCtx = ThreadSafetyAnalyzer::RangeEvalCtx;
  using LocalVarLookupScope = ThreadSafetyAnalyzer::LocalVarLookupScope;
  using ScopeExitCall = ThreadSafetyAnalyzer::ScopeExitCall;
  using SwitchCaseTable = ThreadSafetyAnalyzer::SwitchCaseTable;

  TrylockBodyVerifier(
      ThreadSafetyAnalyzer &Analyzer, CFG *CFGraph,
      const PostOrderCFGView *SortedGraph,
      PostOrderCFGView::CFGBlockSet &VisitedBlocks,
      const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars,
      SmallVector<TrylockExitSpec, 2> ExitSpecs, IntDomain RetDom)
      : Analyzer(Analyzer), CFGraph(CFGraph), SortedGraph(SortedGraph),
        VisitedBlocks(VisitedBlocks), EscapedVars(EscapedVars),
        ExitBlock(&CFGraph->getExit()), NumBlocks(CFGraph->getNumBlockIDs()),
        CurrentTrylockExitSpecs(std::move(ExitSpecs)),
        CurrentTrylockRetDom(std::move(RetDom)), ValStmtCtx(nullptr) {
    Analyzer.CurrentVerifier = this;
  }
  ~TrylockBodyVerifier() { Analyzer.CurrentVerifier = nullptr; }
  TrylockBodyVerifier(const TrylockBodyVerifier &) = delete;
  TrylockBodyVerifier &operator=(const TrylockBodyVerifier &) = delete;

  /// Compute the information about the CFG that the verification needs.
  void begin(AnalysisDeclContext &AC);

  const llvm::SmallPtrSetImpl<const ValueDecl *> &escapedVars() const {
    return EscapedVars;
  }
  void recordCallCtx(const CallExpr *Call, LocalVarContext Ctx) {
    DiscardedCallCtx.try_emplace(Call, Ctx);
  }

  /// Whether \p B is reachable from the entry of the CFG.
  bool inSortedGraph(const CFGBlock *B) const {
    return RPOIdx[B->getBlockID()] != UINT_MAX;
  }
  /// The capabilities that the function is expected to acquire.
  const CapExprSet &exitCaps() const { return CurrentTrylockExitCaps; }

  /// Visit the exit block, whose info is \p CurrBlockInfo.
  void visitExitBlock(CFGBlockInfo *CurrBlockInfo);
  /// Start visiting block \p B. The following functions up to exitBlock()
  /// refer to this block.
  void beginBlock(const CFGBlock *B);
  /// Whether the current block is on a path to the exit that does not modify
  /// the lock state, i.e. whether its states are tracked per path.
  bool isPureBlock() const { return IsPureBlock; }
  /// Record that the edge from \p Pred to the current block is a back edge.
  void addBackEdgePred(const CFGBlock *Pred) {
    UnvisitedBackPreds.push_back(Pred);
  }
  /// Join the state on the edge from the visited block \p Pred into the
  /// state of the current block and compute the lockset on the edge in
  /// \p PrevLockset.
  void joinPredecessor(const CFGBlock *Pred, FactSet &PrevLockset);
  /// Record \p Lockset, the lockset on an edge into the current block,
  /// which is a pure block.
  void addPurePredLockset(FactSet Lockset) {
    PurePredLocksets.push_back(std::move(Lockset));
  }
  void reportOverflowedJoin(const CFGBlockInfo *CurrBlockInfo);
  /// Compute the state at the entry of the current block, which is
  /// reachable, after all predecessors have been joined.
  void enterBlock(CFGBlockInfo *CurrBlockInfo);
  /// Update the state for statement \p S of the current block. \p FSet is
  /// the lockset before \p S.
  void handleStatement(const Stmt *S, const FactSet &FSet);
  /// Add the capabilities that the trylock calls in the return value of
  /// \p RS, a statement of the current block, acquire on success and that
  /// \p Call, a destructor or cleanup function call after \p RS, releases to
  /// \p FSet.
  void addReturnedTrylockCaps(const ReturnStmt *RS,
                              const ThreadSafetyAnalyzer::ScopeExitCall &Call,
                              FactSet &FSet);
  /// Finish visiting the current block.
  void exitBlock(const CFGBlockInfo *CurrBlockInfo);
  /// Verify the lock state at each exit of the function.
  void verifyExits(const FactSet &ExpectedFunctionExitSet,
                   const CFGBlockInfo &Final);

private:
  /// A predecessor of the exit block and what the verification of the lock
  /// state at that exit needs.
  struct ExitContext {
    const CFGBlock *PredBlock;
    const CFGBlockInfo &PredInfo;
    const ReturnStmt *RS;
    const Expr *RetVal;
    SourceLocation DiagLoc;
    LocalVarContext EvalCtx;
    ThreadSafetyHandler &DedupHandler;
    const FactSet &ExpectedFunctionExitSet;
    bool ReturnsPointer;
    llvm::MapVector<const ReturnStmt *,
                    std::pair<std::optional<FactSet>, LocalVarContext>>
        &PtReturnExpectedSets;
  };

  void getAcquiredTrylockCaps(const AcquiredTrylockKey &Key, CapExprSet &Caps);
  bool isPureExitBlock(const CFGBlock *B, const CapExprSet &TargetCaps);
  void addLockToExpectedSet(FactSet &Set, const CapabilityExpr &Lock,
                            LockKind LK, SourceLocation Loc);
  bool factSetsEquivalent(const FactSet &A, const FactSet &B) const;
  void constrainValueStateOnEdge(TrylockValueState &State,
                                 const CFGBlock *PredBlock,
                                 const CFGBlock *CurrBlock);
  void constrainValueStateOnEdgeImpl(TrylockValueState &State,
                                     const CFGBlock *PredBlock,
                                     const CFGBlock *CurrBlock);
  void pruneOutOfScopeVars(TrylockValueState &State, const CFGBlock *B);
  bool trylockDefMayAcquire(const TrylockValueState &State, const Expr *DefE,
                            LocalVarContext DefCtx, QualType Ty,
                            const IntRangeSet *Allowed);
  void materializeNarrowedTrylocks(FactSet &Lockset, TrylockValueState &State);
  /// If \p PtrE is a trackable local pointer variable, possibly behind
  /// casts, return its canonical declaration.
  const ValueDecl *getDereferencedPtrExprVar(const Expr *PtrE) const;
  /// Return the trackable local pointer variable dereferenced by accessing
  /// the lvalue \p LV, if any.
  const ValueDecl *getAccessedLValuePtrVar(const Expr *LV) const;
  const ValueDecl *getDereferencedPtrInStmt(const Stmt *S) const;
  void recordStmtMetadata(const Stmt *S, LocalVarContext StmtCtx);
  void updateValueStateForStmt(TrylockValueState &State, const Stmt *S,
                               LocalVarContext StmtCtx);
  void updateValueStateForStmtImpl(TrylockValueState &State, const Stmt *S,
                                   LocalVarContext StmtCtx);
  void retireVarDef(TrylockValueState &State, const ValueDecl *VD,
                    const Expr *NewRHS);
  void updateVarFromExpr(TrylockValueState &State, const ValueDecl *VD,
                         const Expr *RHS, LocalVarContext StmtCtx);
  // If \p Calls is set, collect all trylock calls that evaluating \p E may
  // execute into \p Calls instead of stopping at the first one.
  bool exprHasUnmaterializedTrylock(
      const Expr *E, LocalVarContext Ctx, const TrylockValueState &State,
      bool UseStateDefs, bool IncludeMaterialized = false,
      llvm::SmallPtrSetImpl<const CallExpr *> *Calls = nullptr);
  void evaluateReturnWithPendingTrylocks(
      const Expr *RetVal, const FactSet &InLockset,
      const TrylockValueState &State, LocalVarContext Ctx,
      SmallVectorImpl<ReturnEvalOutcome> &Out);
  void collectTrylockAcquires(const Expr *E, LocalVarContext Ctx,
                              const TrylockValueState &State, bool UseStateDefs,
                              SmallVectorImpl<PendingTrylockAcquire> &Out,
                              llvm::SmallPtrSetImpl<const Expr *> &Visited,
                              unsigned Depth = 0);
  void applyScopeExitCleanups(FactSet &StateSet, const CFGBlock *B,
                              bool OnlyAfterReturn = false,
                              const FactSet *PreReturnSet = nullptr,
                              ThreadSafetyHandler *DiagHandler = nullptr);
  void checkTrylockExitOutcome(
      const FactSet &BaseExpectedExitSet, const ReturnEvalOutcome &Outcome,
      SourceLocation DiagLoc, ThreadSafetyHandler &ExitHandler,
      std::optional<FactSet> *NonNullExpectedSet = nullptr,
      const FactSet *MaySet = nullptr);
  void intersectExpectedSets(FactSet &Acc, const FactSet &Other);

  static bool sameUnmaterializedDefs(const TrylockValueState &A,
                                     const TrylockValueState &B);
  static bool sameOverwrittenDefs(const TrylockValueState &A,
                                  const TrylockValueState &B);
  bool sameBundleState(const TrylockEdgeBundle &A, const TrylockEdgeBundle &B);
  bool sameCollapsedBundleState(const TrylockEdgeBundle &A,
                                const TrylockEdgeBundle &B);
  void mergeOrAppendBundle(SmallVectorImpl<TrylockEdgeBundle> &Bundles,
                           TrylockEdgeBundle Candidate);
  void collapseAndMergeBundle(SmallVectorImpl<TrylockEdgeBundle> &Bundles,
                              TrylockEdgeBundle Candidate);
  void addOrMergeBundle(unsigned BlockID, TrylockEdgeBundle Candidate);
  void intersectFactSetsQuietly(FactSet &Acc, const FactSet &Other);
  TrylockValueState getEdgeState(const CFGBlock *Pred, const CFGBlock *Succ,
                                 FactSet &Lockset);
  void forEachEdgeBundle(const CFGBlock *Pred, const CFGBlock *Succ,
                         llvm::function_ref<void(TrylockEdgeBundle)> F);

  /// Compute the state at the entry of the current block, which is the
  /// header of a loop whose back edges have not been visited yet.
  void enterLoopHeader();
  /// Forget the value of \p VD, which a loop modifies.
  void eraseModifiedVar(const ValueDecl *VD);
  void enterIrreducibleCycle();
  /// Compute the state at the entry of the header of a natural loop that
  /// consists of \p LoopBlocks.
  void
  enterNaturalLoop(const llvm::SmallPtrSetImpl<const CFGBlock *> &LoopBlocks);
  /// Add to CurrValState the trylock calls of the loop that consists of
  /// \p LoopBlocks whose results may be discarded or overwritten before they
  /// are tested.
  void addLoopPendingTrylocks(
      const llvm::SmallPtrSetImpl<const CFGBlock *> &LoopBlocks);

  void verifyReturn(const ExitContext &Exit, const FactSet &Lockset,
                    TrylockValueState State);
  /// Verify the lock state at the exit \p Exit for the lockset \p Lockset
  /// and the value state \p State on an edge into Exit.PredBlock.
  void verifyEdgeState(const ExitContext &Exit, FactSet Lockset,
                       TrylockValueState State);

  ThreadSafetyAnalyzer &Analyzer;
  CFG *CFGraph;
  const PostOrderCFGView *SortedGraph;
  PostOrderCFGView::CFGBlockSet &VisitedBlocks;
  const llvm::SmallPtrSetImpl<const ValueDecl *> &EscapedVars;
  const CFGBlock *ExitBlock;
  const unsigned NumBlocks;

  SmallVector<TrylockExitSpec, 2> CurrentTrylockExitSpecs;
  IntDomain CurrentTrylockRetDom;
  CapExprSet CurrentTrylockExitCaps;
  // The parent map of the function whose trylock implementation is verified.
  const ParentMap *CurrentParentMap = nullptr;
  // Logical && / || operators whose boolean result is consumed as a value by a
  // CFGStmt in the current function.
  llvm::DenseSet<const BinaryOperator *> ValueLogicalOps;
  // The statement that encloses the declaration of a local variable, i.e. the
  // scope of the variable.
  llvm::DenseMap<const ValueDecl *, const Stmt *> VarScopes;
  // Trylock calls in the function being verified whose result is discarded.
  llvm::SmallPtrSet<const CallExpr *, 4> DiscardedCalls;
  // The local variable context of each executed call in DiscardedCalls.
  llvm::DenseMap<const CallExpr *, LocalVarContext> DiscardedCallCtx;
  // The number of evaluateReturnOutcomes() calls and unmaterialized-trylock
  // scan steps that may still be performed for the return value that is being
  // verified, and whether that budget or the number of outcomes has been
  // exceeded.
  unsigned ReturnEvalSteps = 0;
  unsigned ReturnScanSteps = 0;
  bool InReturnEval = false;
  bool ReturnEvalExhausted = false;

  std::vector<unsigned> RPOIdx;
  std::vector<bool> PureExitPathBlocks;
  std::vector<TrylockValueState> BlockExitValState;
  std::vector<bool> KeepStateForExit;
  std::vector<SmallVector<TrylockEdgeBundle, 2>> PureBlockBundles;
  std::vector<bool> CollapsedBundles;
  std::vector<bool> BundleOverflow;
  std::vector<FactSet> PreReturnLocksets;
  std::vector<TrylockValueState> PreReturnValStates;
  std::vector<LocalVarContext> PreReturnVarCtx;

  // The state of the block that is being visited.
  const CFGBlock *CurrBlock = nullptr;
  unsigned CurrBlockID = 0;
  bool IsPureBlock = false;
  TrylockValueState CurrValState;
  SmallVector<const CFGBlock *, 2> UnvisitedBackPreds;
  // The locksets on the edges into a pure block.
  SmallVector<FactSet, 2> PurePredLocksets;
  // The local variable context of the next statement of the block.
  unsigned ValCtxIdx = 0;
  LocalVarContext ValStmtCtx;
};

} // namespace threadSafety
} // namespace clang

#endif // LLVM_CLANG_LIB_ANALYSIS_THREADSAFETYINTERNAL_H
