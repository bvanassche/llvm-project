// RUN: %clang_cc1 -std=c++11 %s -verify -Wthread-safety-analysis
// RUN: %clang_cc1 -std=c++20 %s -verify -Wthread-safety-analysis

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

  bool tryLockBad() // expected-note@+1 {{mutex acquired here}}
      __attribute__((try_acquire_capability(true, mu))) {
    return true; // expected-warning {{expecting mutex 'mu' to be held at the end of function}}
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
  int tryRangeBad() // expected-note@+1 {{mutex acquired here}}
      __attribute__((try_acquire_shared_capability_range(Lo, Hi, mu))) {
    return Hi; // expected-warning {{expecting mutex 'mu' to be held at the end of function}}
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
  if (b.tryLockBad()) { // expected-note {{in instantiation of member function 'TryAcquireTemplateTests::Box<int>::tryLockBad' requested here}}
    b.mu.Unlock();
  }
  if (b.tryRangeValid<0, 0>(cond) == 0) {
    b.val = 2;
    b.mu.Unlock();
  }
  int r = b.tryRangeBad<1, 5>(); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::Box<int>::tryRangeBad<1, 5>' requested here}}
  if (r >= 1 && r <= 5) {
    int x = b.val;
    (void)x;
    b.mu.ReaderUnlock();
  }
}

CapMutex globalMu;

// Explicit instantiation definitions are verified too.
template <int Lo, int Hi>
int tryRangeBounds(bool cond) // expected-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(Lo, Hi, globalMu))) {
  if (!cond)
    return Hi + 1;
  return Lo; // expected-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeBounds<0, 1>(bool); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeBounds<0, 1>' requested here}}

// A capability whose type depends on a template parameter.
template <typename Mu>
int tryRangeDepCap(Mu &mu, bool cond) // expected-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  if (cond) {
    mu.Lock();
    return 0;
  }
  return 0; // expected-warning {{expecting mutex 'mu' to be held at the end of function}}
}
template int tryRangeDepCap<CapMutex>(CapMutex &, bool); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeDepCap<TryAcquireTemplateTests::CapMutex>' requested here}}

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
int tryRangeNonDepBad() // expected-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, globalMu))) {
  return 0; // expected-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeNonDep<int>(bool);
template int tryRangeNonDepBad<int>(); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeNonDepBad<int>' requested here}}

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
};

void testEmptyVariadicPack(VariadicHelper &h) {
  if (h.lockAllRange() == 0) {
  }
  if (h.lockAllBool()) {
  }
}

struct LateSiblingConstexpr {
  CapMutex mu;
  CapMutex otherMu;
  int guarded __attribute__((guarded_by(otherMu)));

  bool tryLate(bool cond) // expected-note@+1 {{mutex acquired here}}
      __attribute__((try_acquire_capability(ok(), mu))) {
    guarded = 1; // expected-warning {{writing variable 'guarded' requires holding mutex 'otherMu' exclusively}}
    mu.Unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
    if (cond)
      return true; // expected-warning {{expecting mutex 'mu' to be held at the end of function}}
    return false;
  }

  void callLate() {
    if (tryLate(false)) {
      mu.Unlock();
    }
  }

  static constexpr bool ok() { return true; }
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
