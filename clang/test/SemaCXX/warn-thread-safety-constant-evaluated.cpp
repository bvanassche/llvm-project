// RUN: %clang_cc1 -fsyntax-only -verify -std=c++20 -Wthread-safety -Wthread-safety-beta %s

// The analysis evaluates trylock checks as they behave at run time, so
// __builtin_is_constant_evaluated() is false in the helpers that it expands,
// and evaluating these helpers does not emit -Wconstant-evaluated warnings.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};
Mutex mu;
int data __attribute__((guarded_by(mu)));
void unlock() __attribute__((release_capability(mu)));
int trylock0() __attribute__((try_acquire_capability_range(0, 0, mu)));

// At run time, only 0 is accepted, so the lock is held.
constexpr bool ok_at_run_time(int r) {
  if (__builtin_is_constant_evaluated())
    return r == 0 || r == 5;
  return r == 0;
}

void accepted_at_run_time() {
  int r = trylock0();
  if (ok_at_run_time(r)) {
    data = 1;
    unlock();
  }
}

// At run time, 5 is accepted too, and the lock is not held for that value.
constexpr bool ok_at_compile_time(int r) {
  if (__builtin_is_constant_evaluated())
    return r == 0;
  return r == 0 || r == 5;
}

void accepted_at_compile_time() {
  int r = trylock0();
  if (ok_at_compile_time(r)) {
    data = 2; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}
