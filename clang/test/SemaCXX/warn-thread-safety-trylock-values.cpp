// RUN: %clang_cc1 -fsyntax-only -verify -std=c++17 -Wthread-safety -Wthread-safety-beta %s

// Tests for the values of local variables that hold trylock results.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};

struct Mutex mu;
int data __attribute__((guarded_by(mu)));

void lock(struct Mutex *m) __attribute__((acquire_capability(m)));
void unlock(struct Mutex *m) __attribute__((release_capability(m)));
int try0(void) __attribute__((try_acquire_capability_range(0, 0, mu)));
int trylock(struct Mutex *m) __attribute__((try_acquire_capability(1, m)));
int cond(void);
void set_int(int *p);
void (*set_int_ptr)(int *);
int scan(const char *fmt, ...);

//===----------------------------------------------------------------------===//
// Variables whose value may change behind the analysis' back.
//===----------------------------------------------------------------------===//

// The initializer of a static local only runs once.
void static_local(void) {
  static int r = try0();
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void addr_taken(void) {
  int r = try0();
  int *p = &r;
  *p = 0;
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void escape_through_function_pointer(void) {
  int r = try0();
  set_int_ptr(&r);
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void escape_through_memcpy(void) {
  int r = try0();
  int z = 0;
  __builtin_memcpy(&r, &z, sizeof(r));
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void escape_through_variadic_argument(void) {
  int r = try0();
  scan("%d", &r);
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

// Passing the address of a variable to a function only allows the function to
// modify the variable during the call. Later assignments are still tracked.
void address_passed_before_assignment(const char *buf) {
  int r;
  unsigned v;
  if (scan(buf, &v, &r) < 1)
    return;
  r = try0();
  if (r == 0) {
    data = 1;
    unlock(&mu);
  }
}

void reference_passed_before_assignment() {
  int r = 0;
  auto set = [](int &x) { x = 1; };
  set(r);
  r = try0();
  if (r == 0) {
    data = 1;
    unlock(&mu);
  }
}

void volatile_local(void) {
  volatile int r = try0();
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void bound_to_reference() {
  int r = try0();
  int &ref = r;
  ref = 0;
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void captured_by_reference() {
  int r = try0();
  [&] { r = 0; }();
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

// Variables that do not escape are still tracked.
void not_escaped(void) {
  int r = try0();
  int copy = r;
  set_int(&copy);
  if (r == 0) {
    data = 1;
    unlock(&mu);
  }
}

// Verifying a trylock implementation must not ignore writes through an alias.
int impl_addr_taken(void) __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  int ok = trylock(&mu);
  int *p = &ok;
  *p = 1;
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int impl_captured_by_reference() __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  int ok = trylock(&mu);
  [&] { ok = 1; }();
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int impl_increment_through_alias(void) // expected-note{{mutex acquired here}}
    __attribute__((try_acquire_capability(1, mu))) {
  int r = trylock(&mu);
  int *p = &r;
  ++*p;
  return r; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}
