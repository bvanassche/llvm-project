// RUN: %clang_cc1 -fsyntax-only -verify -std=c++11 -Wthread-safety %s
// RUN: %clang_cc1 -fsyntax-only -verify -std=c++20 -Wthread-safety %s

// A trylock function may be a conversion operator that is called implicitly,
// e.g. by testing an object in a condition.

struct __attribute__((capability("mutex"))) Mutex {
  void Unlock() __attribute__((release_capability()));
};
Mutex convMu;
int convData __attribute__((guarded_by(convMu)));

struct TryGuard {
  explicit operator bool() __attribute__((try_acquire_capability(true, convMu)));
};
struct TryInt {
  operator int() __attribute__((try_acquire_capability(1, convMu)));
};

void explicitBool(TryGuard g) {
  if (g) {
    convData = 1;
    convMu.Unlock();
  }
}

void explicitBoolEarlyReturn(TryGuard g) {
  if (!g)
    return;
  convData = 2;
  convMu.Unlock();
}

void implicitInt(TryInt t) {
  if (t) {
    convData = 3;
    convMu.Unlock();
  }
}

void wrongBranch(TryGuard g) {
  if (!g) {
    convData = 4; // expected-warning {{writing variable 'convData' requires holding mutex 'convMu' exclusively}}
    convMu.Unlock(); // expected-warning {{releasing mutex 'convMu' that was not held}}
  } else {
    convMu.Unlock();
  }
}
