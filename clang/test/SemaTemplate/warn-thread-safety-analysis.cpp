// RUN: %clang_cc1 -std=c++11 %s -verify -Wthread-safety-analysis

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

  bool tryLockBad() // expected-note {{mutex acquired here}}
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
  int tryRangeBad() // expected-note {{mutex acquired here}}
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
int tryRangeBounds(bool cond) // expected-note {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(Lo, Hi, globalMu))) {
  if (!cond)
    return Hi + 1;
  return Lo; // expected-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeBounds<0, 1>(bool); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeBounds<0, 1>' requested here}}

// A capability whose type depends on a template parameter.
template <typename Mu>
int tryRangeDepCap(Mu &mu, bool cond) // expected-note {{mutex acquired here}}
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
int tryRangeNonDepBad() // expected-note {{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, globalMu))) {
  return 0; // expected-warning {{expecting mutex 'globalMu' to be held at the end of function}}
}
template int tryRangeNonDep<int>(bool);
template int tryRangeNonDepBad<int>(); // expected-note {{in instantiation of function template specialization 'TryAcquireTemplateTests::tryRangeNonDepBad<int>' requested here}}

} // namespace TryAcquireTemplateTests
