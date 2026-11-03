// RUN: %clang_cc1 -fsyntax-only -verify -std=c++17 -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify -std=c++20 -Wthread-safety -Wthread-safety-beta %s

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
// The value of the trylock result is unknown, so the call may or may not have
// acquired mu for every return value.
int impl_addr_taken(void) __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  int *p = &ok;
  *p = 1;
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning{{mutex 'mu' is still held at the end of function}}
}

int impl_captured_by_reference() __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  [&] { ok = 1; }();
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning{{mutex 'mu' is still held at the end of function}}
}

int impl_increment_through_alias(void) // expected-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability(1, mu))) {
  int r = trylock(&mu); // expected-note{{mutex acquired here}}
  int *p = &r;
  ++*p;
  return r; // expected-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning{{mutex 'mu' is still held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Trylock results that are overwritten or discarded.
//===----------------------------------------------------------------------===//

#define TRY1 __attribute__((try_acquire_capability(1, mu)))

int overwritten() TRY1 {
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  ok = 0;
  return ok; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int overwritten_conditionally(int c) TRY1 {
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  if (c)
    ok = 0;
  return ok; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int overwritten_before_call(int c) TRY1 {
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  if (c)
    ok = 0;
  cond();
  return ok; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

// The loop invalidates what is known about the value of ok.
int overwritten_in_loop() TRY1 { // expected-note{{mutex acquired here}}
  int ok = trylock(&mu); // expected-note{{mutex acquired here}}
  while (cond())
    ok = 0;
  return ok; // expected-warning{{mutex 'mu' is still held at the end of function}} expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int overwritten_by_trylock() TRY1 {
  int ok;
  ok = trylock(&mu); // expected-note 2{{mutex acquired here}}
  ok = trylock(&mu); // expected-warning{{acquiring mutex 'mu' that is already held}}
  return ok; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

// The overwritten value can only be a failure value.
int overwritten_after_failure() TRY1 {
  int ok = trylock(&mu);
  if (!ok)
    ok = 0;
  return ok;
}

// The result is still stored in another variable.
int overwritten_copy_kept() TRY1 {
  int ok = trylock(&mu);
  int ok2 = ok;
  ok = 5;
  return ok2;
}

int valid_join(void) TRY1 {
  int ret = 1;
  if (cond())
    lock(&mu);
  else
    ret = trylock(&mu);
  cond();
  if (!ret)
    return 0;
  return 1;
}

int discarded_in_unbraced_if(int c) TRY1 {
  if (c)
    trylock(&mu); // expected-note{{mutex acquired here}}
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int discarded_by_comma() TRY1 {
  return (trylock(&mu), 0); // expected-warning{{mutex 'mu' is still held at the end of function}} expected-note{{mutex acquired here}}
}

int discarded_in_initializer() TRY1 {
  int x = (trylock(&mu), 0); // expected-note{{mutex acquired here}}
  return x; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int discarded_in_for_init() TRY1 {
  for (trylock(&mu);;) // expected-note{{mutex acquired here}}
    return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int not_discarded_conditional(int c) TRY1 {
  return c ? trylock(&mu) : 0;
}

//===----------------------------------------------------------------------===//
// More paths to a return statement than can be tracked separately.
//===----------------------------------------------------------------------===//

#define PATH_CASE(n)                                                           \
  if (x == (n)) {                                                              \
    if (trylock(&mu))                                                          \
      goto out;                                                                \
    return 0;                                                                  \
  }
#define PATH_CASE8(b)                                                          \
  PATH_CASE(8 * (b) + 0) PATH_CASE(8 * (b) + 1) PATH_CASE(8 * (b) + 2)         \
  PATH_CASE(8 * (b) + 3) PATH_CASE(8 * (b) + 4) PATH_CASE(8 * (b) + 5)         \
  PATH_CASE(8 * (b) + 6) PATH_CASE(8 * (b) + 7)

// Every path to 'out' holds mu, yet failure is returned.
int too_many_paths(int x) TRY1 {
  PATH_CASE8(0) PATH_CASE8(1) PATH_CASE8(2) PATH_CASE8(3)
  PATH_CASE8(4) PATH_CASE8(5) PATH_CASE8(6) PATH_CASE8(7)
  PATH_CASE(64) // expected-note{{mutex acquired here}}
  return 0;
out:
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int too_many_paths_valid(int x) TRY1 {
  PATH_CASE8(0) PATH_CASE8(1) PATH_CASE8(2) PATH_CASE8(3)
  PATH_CASE8(4) PATH_CASE8(5) PATH_CASE8(6) PATH_CASE8(7)
  PATH_CASE(64)
  return 0;
out:
  return 1;
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

int logical_rhs_reassign_callee() TRY1 { // expected-note{{mutex acquired here}}
  int ok = cond();
  if (!ok && (ok = cond()))
    return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 0;
}

int logical_rhs_reassign_negated() TRY1 { // expected-note{{mutex acquired here}}
  int ok = 0;
  if (!((ok == 1) || ((ok = 1) && cond())))
    return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 0;
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

int delegate_unscoped_enum_pos()
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int s = try_unscoped_pos();
  if (s < 0)
    return -1;
  return 0;
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
    __attribute__((try_acquire_capability(false, mu))) {
  if (ok) {
    lock(&mu);
    return ScopedStatus::Ok;
  }
  return ScopedStatus::Busy;
}

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

#if __cplusplus >= 202002L
namespace std {
struct strong_ordering {
  signed char v;
  static const strong_ordering less;
  static const strong_ordering equal;
  static const strong_ordering greater;
  friend constexpr bool operator==(strong_ordering, strong_ordering) = default;
  friend constexpr bool operator<(strong_ordering a, int) { return a.v < 0; }
};
inline constexpr strong_ordering strong_ordering::less{-1};
inline constexpr strong_ordering strong_ordering::equal{0};
inline constexpr strong_ordering strong_ordering::greater{1};
} // namespace std

int test_spaceship_in_trylock(int a, int b) TRY1 {
  if ((a <=> b) == std::strong_ordering::equal) {
    lock(&mu);
    return 1;
  }
  return 0;
}

int test_requires_unevaluated() TRY1 { // expected-note{{mutex acquired here}}
  int ok = 1;
  bool b = requires {
    { ok = 0 };
  };
  (void)b;
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}
#endif

//===----------------------------------------------------------------------===//
// Lvalue assignments, call-argument escapes, unevaluated builtins, and StmtExpr.
//===----------------------------------------------------------------------===//

int *id_ptr_alias(int *p) { return p; }
void take_uintptr(__UINTPTR_TYPE__);
void take_const_ptr_ref(int *const &);
void bind(int *);

void test_lvalue_and_call_escapes() {
  int r0;
  int *p0 = &(r0 = trylock_zero());
  *p0 = 0;
  if (r0 == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }

  auto set = [](int &x, int val) { x = val; };
  int r1 = trylock_zero();
  set(r1, 0);
  if (r1 == 0) {
    data = 2; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }

  int r2 = 1;
  int *p2 = id_ptr_alias(&r2);
  r2 = trylock_zero();
  *p2 = 0;
  if (!r2) {
    data = 3; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }

  int r3 = trylock_zero();
  take_uintptr((__UINTPTR_TYPE__)&r3);
  if (!r3) {
    data = 4; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }

  int r4 = trylock_zero();
  take_const_ptr_ref(&r4);
  if (!r4) {
    data = 5; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }

  int r5 = trylock_zero();
  bind(&r5);
  if (!r5) {
    data = 6; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  }
}

int test_prefix_inc_on_assignment() TRY1 { // expected-note{{mutex acquired here}}
  int ok = 0;
  ++(ok = 0);
  return ok; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

void test_builtin_constant_p_caller() {
  int r = cond();
  (void)__builtin_constant_p(r = trylock_zero());
  if (r == 0) {
    data = 1; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
  }
}

int test_builtin_constant_p_callee(bool unk)
    __attribute__((try_acquire_capability_range(0, 0, mu))) { // expected-note{{mutex acquired here}}
  int r = cond();
  (void)__builtin_constant_p(r = trylock_zero());
  if (unk)
    (void)__builtin_constant_p((__builtin_unreachable(), r = 0));
  return r; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int test_stmtexpr_last_expr_mutation() TRY1 { // expected-note{{mutex acquired here}}
  return ({ // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
    int d = 0;
    (d = 1, d + 0);
  });
}

int test_stmtexpr_pre_rhs_snapshot() TRY1 { // expected-note{{mutex acquired here}}
  int ok = 0;
  int y = (({
             int s = (ok == 0);
             s;
           }) +
           ((ok = 1), 0));
  return y; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Trylock implementations whose success value depends on a constexpr member
// function that is defined later in the class.
//===----------------------------------------------------------------------===//

struct Mutex mu_other;
int data_other __attribute__((guarded_by(mu_other)));

struct LateConstexpr {
  bool try_late() __attribute__((try_acquire_capability(ok(), mu))) { // expected-note{{mutex acquired here}}
    data_other = 1; // expected-warning{{writing variable 'data_other' requires holding mutex 'mu_other' exclusively}}
    unlock(&mu); // expected-warning{{releasing mutex 'mu' that was not held}}
    return true; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
  }
  static constexpr bool ok() { return true; }
};

//===----------------------------------------------------------------------===//
// Trylock results whose use is not modeled.
//===----------------------------------------------------------------------===//

struct Mutex mu1, mu2;
int trylock1() __attribute__((try_acquire_capability(1, mu1)));
int trylock2() __attribute__((try_acquire_capability(1, mu2)));

int result_stored_in_memory(int *out) TRY1 {
  *out = trylock1(); // expected-note{{mutex acquired here}}
  return 0; // expected-warning{{mutex 'mu1' is still held at the end of function}}
}

int result_stored_in_volatile() TRY1 {
  volatile int v = trylock1(); // expected-note{{mutex acquired here}}
  return 0; // expected-warning{{mutex 'mu1' is still held at the end of function}}
}

int result_in_bitwise_or() TRY1 { // expected-note{{mutex acquired here}}
  return trylock1() | trylock2(); // expected-note 2{{mutex acquired here}} expected-warning{{mutex 'mu1' is still held at the end of function}} expected-warning{{mutex 'mu2' is still held at the end of function}} expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int result_dropped_on_fallthrough(int c) TRY1 { // expected-note{{mutex acquired here}}
  if (c) {
    lock(&mu);
    return 1;
  }
  (void)trylock1(); // expected-note{{mutex acquired here}}
} // expected-warning{{mutex 'mu1' is still held at the end of function}} expected-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning{{non-void function does not return a value in all control paths}}

//===----------------------------------------------------------------------===//
// Paths that are tracked separately until there are too many of them.
//===----------------------------------------------------------------------===//

#define DEREFS                                                                 \
  if (m & 1) s += *p0;                                                         \
  if (m & 2) s += *p1;                                                         \
  if (m & 4) s += *p2;                                                         \
  if (m & 8) s += *p3;                                                         \
  if (m & 16) s += *p4;                                                        \
  if (m & 32) s += *p5;                                                        \
  if (m & 64) s += *p6;

int many_deref_paths_valid(int c, int *p0, int *p1, int *p2, int *p3, int *p4,
                           int *p5, int *p6, unsigned m, int flag)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int ret = 1, s = 0;
  if (c) {
    lock(&mu);
    ret = 0;
  }
  DEREFS
  if (flag)
    s += 1;
  return ret;
}

int many_deref_paths_leak(int c, int *p0, int *p1, int *p2, int *p3, int *p4,
                          int *p5, int *p6, unsigned m, int flag)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int ret = 1, s = 0;
  if (c) {
    lock(&mu); // expected-note{{mutex acquired here}}
    ret = 2;
  }
  DEREFS
  if (flag)
    s += 1;
  return ret; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Irreducible cycles.
//===----------------------------------------------------------------------===//

int irreducible_inner_cycle(int n, int c) TRY1 { // expected-note{{mutex acquired here}}
  int ok = 1, z = 0;
  while (n-- > 0) {
    if (z == 0)
      goto L2;
    else {
    L1:
      ok = 0;
      if (c)
        goto done;
    L2:
      goto L1;
    }
  done:;
  }
  if (!ok)
    return 1; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
  lock(&mu);
  return 1;
}

int irreducible_keeps_pending(int c) TRY1 {
  int z = 0;
  (void)trylock1(); // expected-note{{mutex acquired here}}
  if (z == 0)
    goto B2;
  else {
  B1:
    if (c)
      return 0; // expected-warning{{mutex 'mu1' is still held at the end of function}}
  B2:
    goto B1;
  }
}

//===----------------------------------------------------------------------===//
// More trylock calls than can be tracked separately, overlapping exclusive
// and shared ranges, and the context in which capabilities are resolved.
//===----------------------------------------------------------------------===//

struct Mutex marr[7];
int trylock_at(int i) __attribute__((try_acquire_capability(1, marr[i])));

int seven_discarded() TRY1 {
  (void)trylock(&marr[0]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[1]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[2]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[3]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[4]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[5]); // expected-note{{mutex acquired here}}
  (void)trylock(&marr[6]); // expected-note{{mutex acquired here}}
  // expected-warning-re@+1 7{{mutex 'marr[{{[0-6]}}]' is still held at the end of function}}
  return 0;
}

int dual_range() __attribute__((try_acquire_capability_range(1, 2, mu)))
    __attribute__((try_acquire_shared_capability_range(0, 1, mu)));
int dual_range_wrapper()
    __attribute__((try_acquire_capability_range(1, 2, mu)))
    __attribute__((try_acquire_shared_capability_range(0, 1, mu))) {
  return dual_range();
}

int discarded_resolved_at_call() TRY1 {
  struct Mutex *m = &mu1;
  (void)trylock(m); // expected-note{{mutex acquired here}}
  m = nullptr;
  return 0; // expected-warning{{mutex 'mu1' is still held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Return values that would fork into exponentially many outcomes.
//===----------------------------------------------------------------------===//

#define T6(b)                                                                  \
  (trylock(&marr[(b)]), trylock(&marr[(b) + 1]), trylock(&marr[(b) + 2]),      \
   cond())
int nested_conditionals() TRY1 {
  // expected-note@+2 6{{mutex acquired here}}
  // expected-warning-re@+1 6{{mutex 'marr[{{.*}}]' is still held at the end of function}}
  return T6(0) ? 0 : T6(3) ? 0 : T6(0) ? 0 : T6(3) ? 0 : T6(0) ? 0 : T6(3) ? 0 : 0;
}
