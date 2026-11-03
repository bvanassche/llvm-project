// RUN: rm -rf %t
// RUN: split-file %s %t
//
// RUN: %clang_cc1 -std=c++20 -Wthread-safety -emit-module-interface %t/locks.cppm -o %t/locks.pcm
// RUN: %clang_cc1 -std=c++20 -Wthread-safety -fprebuilt-module-path=%t -fsyntax-only -verify %t/use.cpp

// Check that try_acquire_capability_range attributes and the bodies of trivial
// inline helpers are available to the thread safety analysis after importing
// a C++20 module.

//--- locks.cppm
export module locks;

export struct __attribute__((capability("mutex"))) Mutex {
  void Unlock() __attribute__((release_capability()));
};

export Mutex mu;
export int data __attribute__((guarded_by(mu)));

export int try_lock_range() __attribute__((try_acquire_capability_range(0, 0, mu)));
export inline bool is_zero(int r) { return r == 0; }

export template <typename T>
int try_lock_tmpl(T &m) __attribute__((try_acquire_capability_range(0, 0, m)));

//--- use.cpp
import locks;

void caller() {
  if (is_zero(try_lock_range())) {
    data = 1;
    mu.Unlock();
  }
  int r = try_lock_tmpl(mu);
  if (r != 0)
    return;
  data = 2;
  mu.Unlock();
  if (try_lock_range() > 0)
    data = 3; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
}

int impl(int r) __attribute__((try_acquire_capability_range(0, 0, mu))) { // expected-note{{mutex acquired here}}
  if (is_zero(r))
    return 0; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 1;
}
