// RUN: %clang_cc1 -std=c++11 %s -verify -Wthread-safety-analysis
// RUN: %clang_cc1 -std=c++20 %s -verify -Wthread-safety-analysis
// RUN: %clang_cc1 -std=c++11 %s -verify=expected,beta -Wthread-safety-analysis -Wthread-safety-beta
// RUN: %clang_cc1 -std=c++20 %s -verify=expected,beta -Wthread-safety-analysis -Wthread-safety-beta

class Mutex {
public:
  void Lock() __attribute__((exclusive_lock_function()));
  void Unlock() __attribute__((unlock_function()));
};

class A {
public:
  Mutex mu1, mu2;

  void foo() __attribute__((exclusive_locks_required(mu1))) __attribute__((exclusive_locks_required(mu2))) {}

  template <class T> void bar() __attribute__((exclusive_locks_required(mu1))) __attribute__((exclusive_locks_required(mu2))) {
    foo();
  }
};

void f() {
  A a;
  a.mu1.Lock();
  a.mu2.Lock();
  a.bar<int>();
  a.mu2.Unlock();
  a.bar<int>(); // expected-warning {{calling function 'bar<int>' requires holding mutex 'a.mu2' exclusively}}
  a.mu1.Unlock();
  a.bar<int>(); // expected-warning {{calling function 'bar<int>' requires holding mutex 'a.mu1' exclusively}} \
                   expected-warning {{calling function 'bar<int>' requires holding mutex 'a.mu2' exclusively}}
}

struct EmptyVariadicTryAcquire {
  template <typename... Mus>
  bool lockAll(Mus &...mus)
      __attribute__((try_acquire_capability(true, mus...))) {
    return true;
  }
};

void testEmptyVariadicTryAcquire(EmptyVariadicTryAcquire &h) {
  if (h.lockAll()) {
  }
}

struct EmptyVariadicCapabilities {
  template <typename... Mus>
  void lockAll(Mus &...mus) __attribute__((acquire_capability(mus...)));
  template <typename... Mus>
  void lockAllShared(Mus &...mus)
      __attribute__((acquire_shared_capability(mus...)));
  template <typename... Mus>
  void unlockAll(Mus &...mus) __attribute__((release_capability(mus...)));
  template <typename... Mus>
  void assertAll(Mus &...mus) __attribute__((assert_capability(mus...)));
};

void testEmptyVariadicCapabilities(EmptyVariadicCapabilities &h) {
  h.lockAll();
  h.lockAllShared();
  h.unlockAll();
  h.assertAll();
}

namespace TryAcquireTemplateTests {

class __attribute__((capability("mutex"))) CapMutex {
public:
  void Lock() __attribute__((acquire_capability()));
  void ReaderLock() __attribute__((acquire_shared_capability()));
  void Unlock() __attribute__((release_capability()));
  void ReaderUnlock() __attribute__((release_shared_capability()));
  bool TryLock() __attribute__((try_acquire_capability(true)));
  bool ReaderTryLock() __attribute__((try_acquire_shared_capability(true)));
};

template <typename T>
class Box {
public:
  CapMutex mu;
  T val __attribute__((guarded_by(mu)));

  bool tryLockValid(bool cond) __attribute__((try_acquire_capability(true, mu))) {
    if (!cond)
      return false;
    mu.Lock();
    return true;
  }

  bool tryLockBad() // beta-note@+1 {{mutex acquired here}}
      __attribute__((try_acquire_capability(true, mu))) {
    return true; // beta-warning {{expecting mutex 'mu' to be held at the end of function}}
  }

  template <int Lo, int Hi>
  int tryRangeValid(bool cond)
      __attribute__((try_acquire_capability_range(Lo, Hi, mu))) {
    if (!cond)
      return Lo - 1;
    mu.Lock();
    return Lo;
  }

  template <int Lo, int Hi>
  int tryRangeBad() // beta-note@+1 {{mutex acquired here}}
      __attribute__((try_acquire_shared_capability_range(Lo, Hi, mu))) {
    return Hi; // beta-warning {{expecting mutex 'mu' to be held at the end of function}}
  }

  template <typename U, U Lo, U Hi>
  U tryRangeUninstantiated(bool cond)
      __attribute__((try_acquire_capability_range(Lo, Hi, mu))) {
    if (!cond)
      return Lo - 1;
    mu.Lock();
    return Lo;
  }
};

void instantiateTemplates(bool cond) {
  Box<int> b;
  if (b.tryLockValid(cond)) {
    b.val = 1;
    b.mu.Unlock();
  }
  if (b.tryLockBad()) { // beta-note {{in instantiation of member function 'TryAcquireTemplateTests::Box<int>::tryLockBad' requested here}}
    b.mu.Unlock();
  }
  if (b.tryRangeValid<0, 0>(cond) == 0) {
    b.val = 2;
    b.mu.Unlock();
  }
  int r = b.tryRangeBad<1, 5>(); // beta-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::Box<int>::tryRangeBad<1, 5>' requested here}}
  if (r >= 1 && r <= 5) {
    int x = b.val;
    (void)x;
    b.mu.ReaderUnlock();
  }
}

CapMutex globalMu;

// Explicit instantiation definitions are verified too.
template <int Lo, int Hi>
int tryRangeBounds(bool cond) // beta-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(Lo, Hi, globalMu))) {
  if (!cond)
    return Hi + 1;
  return Lo; // beta-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeBounds<0, 1>(bool); // beta-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeBounds<0, 1>' requested here}}

// A capability whose type depends on a template parameter.
template <typename Mu>
int tryRangeDepCap(Mu &mu, bool cond) // beta-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  if (cond) {
    mu.Lock();
    return 0;
  }
  return 0; // beta-warning {{expecting mutex 'mu' to be held at the end of function}}
}
template int tryRangeDepCap<CapMutex>(CapMutex &, bool); // beta-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeDepCap<TryAcquireTemplateTests::CapMutex>' requested here}}

// An attribute without dependent arguments on a function template.
template <typename T>
int tryRangeNonDep(bool cond)
    __attribute__((try_acquire_capability_range(0, 0, globalMu))) {
  if (cond) {
    globalMu.Lock();
    return 0;
  }
  return -1;
}
template <typename T>
int tryRangeNonDepBad() // beta-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, globalMu))) {
  return 0; // beta-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeNonDep<int>(bool);
template int tryRangeNonDepBad<int>(); // beta-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeNonDepBad<int>' requested here}}

struct VariadicHelper {
  template <typename... Mus>
  int lockAllRange(Mus &...mus)
      __attribute__((try_acquire_capability_range(0, 0, mus...))) {
    return 0;
  }
  template <typename... Mus>
  bool lockAllBool(Mus &...mus)
      __attribute__((try_acquire_capability(true, mus...))) {
    return true;
  }
  template <typename... Mus>
  bool lockAllSharedBool(Mus &...mus)
      __attribute__((try_acquire_shared_capability(true, mus...))) {
    return true;
  }
};

struct __attribute__((capability("mutex"))) VariadicCapMutex {
  void Unlock() __attribute__((release_capability()));
  template <typename... Mus>
  void LockAll(Mus &...mus) __attribute__((acquire_capability(mus...)));
  template <typename... Mus>
  bool TryAll(Mus &...mus)
      __attribute__((try_acquire_capability(true, mus...)));
};

void testEmptyVariadicPack(VariadicHelper &h, VariadicCapMutex &mu) {
  if (h.lockAllRange() == 0) {
  }
  if (h.lockAllBool()) {
  }
  if (h.lockAllSharedBool()) {
  }
  // The empty packs name no capabilities, also on members of a capability
  // class, rather than the implicit object argument.
  mu.LockAll();
  mu.Unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
  if (mu.TryAll())
    mu.Unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
}

struct __attribute__((scoped_lockable)) ScopedBase {
  ScopedBase();
  ~ScopedBase() __attribute__((release_capability()));
};

// The analysis does not treat a class derived from a scoped_lockable class as
// scoped_lockable. An empty pack on its constructor acquires nothing.
struct DerivedFromScoped : ScopedBase {
  template <typename... Mus>
  DerivedFromScoped(Mus &...mus) __attribute__((acquire_capability(mus...)));
};

// An empty pack on a constructor of a class that is both scoped_lockable and a
// capability does not acquire the constructed object.
struct __attribute__((scoped_lockable, capability("mutex"))) ScopedCapability {
  template <typename... Mus>
  ScopedCapability(Mus &...mus) __attribute__((acquire_capability(mus...)));
  ~ScopedCapability() __attribute__((release_capability()));
};

// Passing a capability that is not a scoped object to a parameter with a
// release_capability attribute releases the named capability without comparing
// it with the underlying capabilities of a scoped object.
struct __attribute__((scoped_lockable, capability("mutex"))) ScopedSelfCapability {
  void LockSelf() __attribute__((acquire_capability()));
};

struct DerivedFromScopedLocking : ScopedBase {
  DerivedFromScopedLocking() __attribute__((acquire_capability()));
};

VariadicCapMutex scopedParamMu;

template <typename T>
void unlockScoped(T &s __attribute__((release_capability(scopedParamMu))));

void testReleaseNonScopedParam(ScopedSelfCapability &s) {
  s.LockSelf(); // expected-note {{mutex acquired here}}
  unlockScoped(s); // expected-warning {{releasing mutex 'scopedParamMu' that was not held}}
} // expected-warning {{mutex 's' is still held at the end of function}}

void testReleaseDerivedFromScopedParam() {
  DerivedFromScopedLocking d; // expected-note {{mutex acquired here}}
  unlockScoped(d); // expected-warning {{releasing mutex 'scopedParamMu' that was not held}}
} // expected-warning {{mutex 'd' is still held at the end of function}}

void testEmptyVariadicPackConstructors(VariadicCapMutex &mu) {
  DerivedFromScoped d;
  ScopedCapability s1;
  ScopedCapability s2(mu);
}

// Empty packs on the defer_lock and adopt_lock constructors of a variadic
// scoped lock keep the attributes, which make the analysis track the scoped
// object that its destructor releases.
struct DeferLockT {};
struct AdoptLockT {};
template <typename... Mus>
struct __attribute__((scoped_lockable)) VariadicDeferAdoptLock {
  VariadicDeferAdoptLock(Mus &...mus) __attribute__((acquire_capability(mus...)));
  VariadicDeferAdoptLock(DeferLockT, Mus &...mus)
      __attribute__((locks_excluded(mus...)));
  VariadicDeferAdoptLock(AdoptLockT, Mus &...mus)
      __attribute__((requires_capability(mus...)));
  ~VariadicDeferAdoptLock() __attribute__((release_capability()));
};

void testEmptyVariadicDeferAdoptLock() {
  VariadicDeferAdoptLock<> g1((DeferLockT()));
  VariadicDeferAdoptLock<> g2((AdoptLockT()));
}

template <typename... Mus>
struct __attribute__((scoped_lockable)) VariadicScopedLock {
  VariadicScopedLock(Mus &...mus) __attribute__((acquire_capability(mus...)));
  ~VariadicScopedLock() __attribute__((release_capability()));
  void relockExtra(Mus &...mus) __attribute__((acquire_capability(mus...)));
  void requireExtra(Mus &...mus) __attribute__((requires_capability(mus...)));
  void excludeExtra(Mus &...mus) __attribute__((locks_excluded(mus...)));
};

void testEmptyScopedLockPack() {
  VariadicScopedLock<> guard;
  guard.relockExtra();
  guard.requireExtra();
  guard.excludeExtra();
}

template <int N>
struct DependentBitFieldHolder {
  unsigned bf : N;
  int tryAssignBitField(bool ok)
      __attribute__((try_acquire_capability(1, globalMu))) {
    if (!ok)
      return (bf = 0);
    globalMu.Lock();
    return (bf = 1);
  }
};

template <typename T>
struct DepBase {
  T x;
};

template <typename T>
struct DepDerived : DepBase<T> {
  DepBase<T> *tryDerivedToBase(bool ok)
      __attribute__((try_acquire_capability(true, globalMu))) {
    if (!ok)
      return nullptr;
    globalMu.Lock();
    return static_cast<DepBase<T> *>(this);
  }
};

#if __cplusplus >= 202002L
template <typename T>
constexpr T kZeroVarTmpl = 0;

template <typename T>
struct ConstexprDtorBox {
  T v;
  constexpr ~ConstexprDtorBox() {}
};

template <typename T>
int tryConstexprDtorRange(bool ok)
    __attribute__((try_acquire_capability_range(kZeroVarTmpl<T>,
                                                ConstexprDtorBox<T>{1}.v,
                                                globalMu))) {
  if (ok) {
    globalMu.Lock();
    return 1;
  }
  return -1;
}

void callConstexprDtorRange() {
  int r = tryConstexprDtorRange<int>(true);
  if (r >= 0 && r <= 1) {
    globalMu.Unlock();
  }
}
#endif

} // namespace TryAcquireTemplateTests
