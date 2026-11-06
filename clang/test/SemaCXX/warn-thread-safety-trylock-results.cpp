// RUN: %clang_cc1 -fsyntax-only -verify=expected,beta -std=c++17 -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify=expected,beta -std=c++20 -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify=expected,nonbeta -std=c++20 -Wthread-safety %s

// Tests for the values of local variables that hold trylock results.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};

struct Mutex mu;
int data __attribute__((guarded_by(mu)));

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

// '__extension__' does not hide a trylock call.
void extension_trylock_cmp(void) {
  if ((__extension__ try0()) == 0) {
    data = 1;
    unlock(&mu);
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

// Passing the address of or a reference to a variable to a function allows the
// function to retain an alias and modify the variable during a later call, but
// not before a later call.
int *global_r_alias;
void keep(int *p) { global_r_alias = p; }
void keep_ref(int &r) { global_r_alias = &r; }
void poke() { *global_r_alias = 0; }

void address_passed_before_assignment_and_poke() {
  int r;
  keep(&r);
  r = try0();
  poke();
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

void reference_passed_before_assignment_and_poke() {
  int r = 1;
  keep_ref(r);
  r = try0();
  poke();
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

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

//===----------------------------------------------------------------------===//
// Reassigned variables on the right-hand side of && and ||.
//===----------------------------------------------------------------------===//

int trylock_zero() __attribute__((try_acquire_capability(0, mu)));

void logical_rhs_reassign_caller() {
  int rc = cond();
  if (rc <= 0 && (rc = trylock_zero()) >= 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
  int rc2 = cond();
  bool ok = (rc2 <= 0 && (rc2 = trylock_zero()) >= 0);
  if (ok) {
    data = 2; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
  int rc3 = cond();
  if (!(rc3 > 0 || (rc3 = trylock_zero()) < 0)) {
    data = 3; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

//===----------------------------------------------------------------------===//
// Unscoped enum promotion, scoped enum class, Derived-to-Base, and wide ints.
//===----------------------------------------------------------------------===//

enum UnscopedStatus { US_OK = 0, US_BUSY = 1 };
UnscopedStatus try_unscoped_zero()
    __attribute__((try_acquire_capability(false, mu)));
UnscopedStatus try_unscoped_pos()
    __attribute__((try_acquire_capability_range(0, 0x7fffffff, mu)));

void test_unscoped_enum_promotion() {
  if (try_unscoped_zero() <= 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
  UnscopedStatus s = try_unscoped_pos();
  if (s < 0)
    return;
  data = 2;
  unlock(&mu);
}

struct BaseObj {
  int a;
};
struct DerivedObj : BaseObj {
  int b;
};
DerivedObj *try_derived_obj() __attribute__((try_acquire_capability(true, mu)));

void test_derived_to_base_caller() {
  BaseObj *p = try_derived_obj();
  if (p) {
    data = 1;
    unlock(&mu);
  }
  BaseObj *q = try_derived_obj();
  if (q != nullptr) {
    data = 2;
    unlock(&mu);
  }
  BaseObj *r = try_derived_obj();
  if (r == nullptr)
    return;
  data = 3;
  unlock(&mu);
}

enum class ScopedStatus { Ok = 0, Busy = 1 };

ScopedStatus try_scoped_status(bool ok)
    __attribute__((try_acquire_capability(false, mu)));

void test_scoped_status_caller(bool ok) {
  if (try_scoped_status(ok) == ScopedStatus::Ok) {
    data = 1;
    unlock(&mu);
  }
  switch (try_scoped_status(ok)) {
  case ScopedStatus::Ok:
    data = 2;
    unlock(&mu);
    break;
  case ScopedStatus::Busy:
    break;
  }
}

_BitInt(65) try_bitint65() __attribute__((try_acquire_capability_range(0, 0, mu)));
_BitInt(128) try_bitint128()
    __attribute__((try_acquire_capability_range((_BitInt(128))1 << 100,
                                                (_BitInt(128))1 << 105, mu)));

void test_bitint_caller() {
  _BitInt(65) a = try_bitint65();
  if (a == 0) {
    data = 1;
    unlock(&mu);
  }
  _BitInt(128) b = try_bitint128();
  if (b == ((_BitInt(128))1 << 100)) {
    data = 2;
    unlock(&mu);
  }
}

#ifdef __SIZEOF_INT128__
__int128 try_int128()
    __attribute__((try_acquire_capability_range((__int128)1 << 100,
                                                (__int128)1 << 105, mu)));

void test_int128_caller() {
  __int128 v = try_int128();
  if (v >= ((__int128)1 << 100) && v <= ((__int128)1 << 105)) {
    data = 1;
    unlock(&mu);
  }
}
#endif

// Chained bijective casts in caller and callee comparisons.
enum HighBitStatus { HB_ERR = 0, HB_OK = 1, HB_HI = 0x80000000U };
HighBitStatus try_hb_status()
    __attribute__((try_acquire_capability_range(HB_OK, HB_OK, mu)));
void test_chained_bijective_cast_caller() {
  int r = try_hb_status();
  if (r == 1U) {
    data = 1;
    unlock(&mu);
  }
}

// Trylock condition on the LHS of && / || with an unrelated RHS.
int trylock_1_to_3() __attribute__((try_acquire_capability_range(1, 3, mu)));
void test_lhs_trylock_in_negated_and(bool unrelated) {
  int r = trylock_1_to_3();
  if (!(r >= 1 && unrelated))
    return;
  if (r > 3)
    return;
  data = 1;
  unlock(&mu);
}

// Pointer-to-member trylock return value compared with nullptr.
struct MemPtrS {
  int x;
};
int MemPtrS::*try_memptr_decl(bool ok)
    __attribute__((try_acquire_capability(true, mu)));
void test_memptr_caller(bool ok) {
  if (try_memptr_decl(ok) != nullptr) {
    data = 1;
    unlock(&mu);
  }
}

//===----------------------------------------------------------------------===//
// Lvalue assignments, call-argument escapes, unevaluated builtins, and StmtExpr.
//===----------------------------------------------------------------------===//

int *id_ptr_alias(int *p) { return p; }
void take_uintptr(__UINTPTR_TYPE__);
void take_const_ptr_ref(int *const &);
void bind(int *);

// Reference-to-pointer parameter.
void bind_ptr_ref(int *&out, int &x) { out = &x; }
void test_caller_ref_to_ptr_escape() {
  int *p = nullptr;
  int r = 1;
  bind_ptr_ref(p, r);
  r = trylock_zero();
  *p = 0;
  if (!r) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }
}

//===----------------------------------------------------------------------===//
// GNU ?:.
//===----------------------------------------------------------------------===//

void gnu_binary_conditional_caller() {
  if ((trylock(&mu) ?: 0) != 0) {
    data = 1;
    unlock(&mu);
  }
}

//===----------------------------------------------------------------------===//
// try_acquire_capability compared with constants other than 0 and 1, switches,
// and reassigned capability pointers.
//===----------------------------------------------------------------------===//

void test_trylock_non_zero_one_constants_and_switch() {
  // For try_acquire_capability(0, mu), comparing with a non-zero constant such
  // as EBUSY (16) leaves other non-zero failure values possible.
  if (trylock_zero() == 16)
    return;
  data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}

  if (trylock_zero() != 16) {
    data = 2; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }

  // For try_acquire_capability(1, m), any non-zero constant is a success value,
  // but != 2 still allows 0.
  if (trylock(&mu) == 2) {
    data = 3;
    unlock(&mu);
  }
  if (trylock(&mu) != 2) {
    data = 4; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }

  switch (trylock_zero()) {
  case 0:
    data = 5;
    unlock(&mu);
    break;
  case 16:
    break;
  default:
    data = 6; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
    break;
  }
}

Mutex mu_reassigned_other;
void test_reassigned_cap_ptr_after_trylock() {
  Mutex *p = &mu_reassigned_other;
  int r = trylock(p); // beta-note{{mutex acquired here}}
  p = &mu;
  if (r) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(p); // beta-warning{{releasing mutex 'mu' that was not held}}
  }

  Mutex *q = &mu; // beta-warning{{mutex 'mu_reassigned_other' is not held on every path through here}}
  int r2 = trylock(q); // nonbeta-note{{mutex acquired here}}
  q = &mu_reassigned_other;
  if (r2) {
    data = 2; // nonbeta-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // nonbeta-warning{{releasing mutex 'mu' that was not held}}
  }
} // nonbeta-warning{{mutex 'q' is not held on every path through here}}
