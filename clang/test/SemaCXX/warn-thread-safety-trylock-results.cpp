// RUN: %clang_cc1 -fsyntax-only -verify=expected,beta -std=c++17 -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify=expected,beta -std=c++20 -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify=expected,nonbeta -std=c++20 -Wthread-safety %s

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
// function to retain an alias and modify the variable during a later call,
// but not before a later call.
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

int trylock_shared(struct Mutex *m)
    __attribute__((try_acquire_shared_capability(1, m)));
void unlock_shared(struct Mutex *m)
    __attribute__((release_shared_capability(m)));
static inline bool is_trylock_failure(int r) { return !r; }

void inline_helper_try_acquire_capability() {
  if (!is_trylock_failure(trylock(&mu))) {
    data = 1;
    unlock(&mu);
  }
  int r = trylock(&mu);
  if (is_trylock_failure(r)) {
    data = 2; // expected-warning{{writing variable 'data' requires holding mutex 'mu' exclusively}}
  } else {
    data = 3;
    unlock(&mu);
  }
  if (!is_trylock_failure(trylock_shared(&mu))) {
    int v = data;
    (void)v;
    unlock_shared(&mu);
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
int impl_addr_taken(void) __attribute__((try_acquire_capability(1, mu))) { // beta-note{{mutex acquired here}}
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  int *p = &ok;
  *p = 1;
  return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}} beta-warning{{mutex 'mu' is still held at the end of function}}
}

int impl_captured_by_reference() __attribute__((try_acquire_capability(1, mu))) { // beta-note{{mutex acquired here}}
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  [&] { ok = 1; }();
  return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}} beta-warning{{mutex 'mu' is still held at the end of function}}
}

int impl_increment_through_alias(void) // beta-note@+1 {{mutex acquired here}}
    __attribute__((try_acquire_capability(1, mu))) {
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  int *p = &r;
  ++*p;
  return r; // beta-warning{{expecting mutex 'mu' to be held at the end of function}} beta-warning{{mutex 'mu' is still held at the end of function}}
}


//===----------------------------------------------------------------------===//
// Trylock results that are overwritten or discarded.
//===----------------------------------------------------------------------===//

#define TRY1 __attribute__((try_acquire_capability(1, mu)))

int overwritten() TRY1 {
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  ok = 0;
  return ok; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int overwritten_conditionally(int c) TRY1 {
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  if (c)
    ok = 0;
  return ok; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int overwritten_before_call(int c) TRY1 {
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  if (c)
    ok = 0;
  cond();
  return ok; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// The loop invalidates what is known about the value of ok.
int overwritten_in_loop() TRY1 { // beta-note{{mutex acquired here}}
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  while (cond())
    ok = 0;
  return ok; // beta-warning{{mutex 'mu' is still held at the end of function}} beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int overwritten_by_trylock() TRY1 {
  int ok;
  ok = trylock(&mu); // beta-note 2{{mutex acquired here}}
  ok = trylock(&mu); // beta-warning{{acquiring mutex 'mu' that is already held}}
  return ok; // beta-warning{{mutex 'mu' is still held at the end of function}}
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
    trylock(&mu); // beta-note{{mutex acquired here}}
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int discarded_by_comma() TRY1 {
  return (trylock(&mu), 0); // beta-warning{{mutex 'mu' is still held at the end of function}} beta-note{{mutex acquired here}}
}

int discarded_in_initializer() TRY1 {
  int x = (trylock(&mu), 0); // beta-note{{mutex acquired here}}
  return x; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int discarded_in_for_init() TRY1 {
  for (trylock(&mu);;) // beta-note{{mutex acquired here}}
    return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
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
  PATH_CASE(64) // beta-note{{mutex acquired here}}
  return 0;
out:
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
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

int logical_rhs_reassign_callee() TRY1 { // beta-note{{mutex acquired here}}
  int ok = cond();
  if (!ok && (ok = cond()))
    return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 0;
}

int logical_rhs_reassign_negated() TRY1 { // beta-note{{mutex acquired here}}
  int ok = 0;
  if (!((ok == 1) || ((ok = 1) && cond())))
    return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
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

int test_requires_unevaluated() TRY1 { // beta-note{{mutex acquired here}}
  int ok = 1;
  bool b = requires {
    { ok = 0 };
  };
  (void)b;
  return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}
#endif

// Element-scaled pointer subtraction in evaluatePureExprRange.
int *try_lock_ptr_at_4() __attribute__((try_acquire_capability_range(4, 4, mu)));
__PTRDIFF_TYPE__ test_ptr_sub_scaled_ok()
    __attribute__((try_acquire_capability_range(1, 1, mu))) {
  int *p = try_lock_ptr_at_4();
  if (p == (int *)4)
    return p - (int *)0;
  return 0;
}
__PTRDIFF_TYPE__ test_ptr_sub_scaled_bad()
    __attribute__((try_acquire_capability_range(4, 4, mu))) {
  int *p = try_lock_ptr_at_4(); // beta-note{{mutex acquired here}}
  if (p == (int *)4)
    return p - (int *)0; // beta-warning{{mutex 'mu' is still held at the end of function}}
  return 0;
}

// Pointer subtraction with negative/high-bit address (ERR_PTR).
int test_err_ptr_sub_bad() __attribute__((try_acquire_capability(0, mu))) { // beta-note{{mutex acquired here}}
  int *p = (int *)-4;
  __PTRDIFF_TYPE__ d = p - (int *)0;
  if (d < 0)
    return 0; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  return -1;
}

// Over-wide C++ bit-fields have padding bits and do not widen the type.
struct OverWideBF {
  int x : 64; // expected-warning{{width of bit-field 'x' (64 bits) exceeds the width of its type; value will be truncated to 32 bits}}
};
int test_over_wide_bf_bad(OverWideBF &s, int y)
    __attribute__((try_acquire_capability(0, mu))) { // beta-note{{mutex acquired here}}
  if (y < 0)
    return -1;
  return (s.x = y); // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// Conditional bit-field lvalue assignments and structured-binding
// bit-field assignments.
struct TwoBits {
  unsigned a : 1;
  unsigned b : 1;
};
int test_cond_bf_assign_bad(bool c, TwoBits &s)
    __attribute__((try_acquire_capability(0, mu))) { // beta-note{{mutex acquired here}}
  return ((c ? s.a : s.b) = 2); // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}
int test_binding_bf_assign_bad(TwoBits &s)
    __attribute__((try_acquire_capability(0, mu))) { // beta-note{{mutex acquired here}}
  auto &[a, b] = s;
  (void)b;
  return (a = 2); // expected-warning{{implicit truncation from 'int' to bit-field changes value from 2 to 0}} beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// ConditionalOperator (c ? t : f) in constrainLeafCondition.
int test_cond_op_infeasible_ok(bool c)
    __attribute__((try_acquire_capability(0, mu))) {
  int one = 1;
  if (!(c ? one : one))
    return 0;
  lock(&mu);
  return 0;
}
int test_cond_op_var_narrow_ok(bool c)
    __attribute__((try_acquire_capability(0, mu))) {
  int r = trylock_zero();
  if (!(c ? r != 0 : r != 0))
    return 0;
  return -1;
}

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
int test_chained_bijective_cast_callee()
    __attribute__((try_acquire_capability(1, mu))) {
  int r = try_hb_status();
  if (r == 1U)
    return 1;
  return 0;
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

int test_prefix_inc_on_assignment() TRY1 { // beta-note{{mutex acquired here}}
  int ok = 0;
  ++(ok = 0);
  return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int test_builtin_constant_p_callee(bool unk)
    __attribute__((try_acquire_capability_range(0, 0, mu))) { // beta-note{{mutex acquired here}}
  int r = cond();
  (void)__builtin_constant_p(r = trylock_zero());
  if (unk)
    (void)__builtin_constant_p((__builtin_unreachable(), r = 0));
  return r; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int test_stmtexpr_last_expr_mutation() TRY1 { // beta-note{{mutex acquired here}}
  return ({ // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
    int d = 0;
    (d = 1, d + 0);
  });
}

int test_stmtexpr_pre_rhs_snapshot() TRY1 { // beta-note{{mutex acquired here}}
  int ok = 0;
  int y = (({
             int s = (ok == 0);
             s;
           }) +
           ((ok = 1), 0));
  return y; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// Escaped local declaration initializer in StmtExpr invalidates modified
// outer variables.
static inline int stmtexpr_escaped_init_helper() {
  return ({
    int d = 0;
    int x = (d = 1);
    int *p = &x;
    (void)p;
    d;
  });
}
int test_stmtexpr_escaped_init_bad() TRY1 { // beta-note{{mutex acquired here}}
  return stmtexpr_escaped_init_helper(); // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// C++ (void)r, comma rvalue, and ternary rvalue do not mark local
// variables as escaped.
int test_cpp_void_cast_branch_ok() TRY1 {
  int r1 = trylock(&mu);
  (void)r1;
  if (r1)
    return 1;
  return 0;
}
int test_cpp_void_cast_and_ternary_ok(bool c) TRY1 {
  int r1 = trylock(&mu);
  (void)r1;
  int r2 = (cond(), r1);
  int res = c ? r1 : r2;
  return res;
}

// Non-transient escape in callee body and reference-to-pointer parameter.
int *g_saved_trylock_ptr;
void save_trylock_ptr(int *p) { g_saved_trylock_ptr = p; }
void clobber_saved_trylock_ptr() { *g_saved_trylock_ptr = 1; }
int test_callee_escaped_local_bad() TRY1 { // beta-note{{mutex acquired here}}
  int r = 0;
  save_trylock_ptr(&r);
  r = trylock(&mu); // beta-note{{mutex acquired here}}
  clobber_saved_trylock_ptr();
  if (r)
    return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

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
// Trylock results whose use is not modeled.
//===----------------------------------------------------------------------===//

struct Mutex mu1, mu2;
int trylock1() __attribute__((try_acquire_capability(1, mu1)));
int trylock2() __attribute__((try_acquire_capability(1, mu2)));

int result_stored_in_memory(int *out) TRY1 {
  *out = trylock1(); // beta-note{{mutex acquired here}}
  return 0; // beta-warning{{mutex 'mu1' is still held at the end of function}}
}

int result_stored_in_volatile() TRY1 {
  volatile int v = trylock1(); // beta-note{{mutex acquired here}}
  return 0; // beta-warning{{mutex 'mu1' is still held at the end of function}}
}

int result_in_bitwise_or() TRY1 { // beta-note{{mutex acquired here}}
  return trylock1() | trylock2(); // beta-note 2{{mutex acquired here}} beta-warning{{mutex 'mu1' is still held at the end of function}} beta-warning{{mutex 'mu2' is still held at the end of function}} beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int result_dropped_on_fallthrough(int c) TRY1 { // beta-note{{mutex acquired here}}
  if (c) {
    lock(&mu);
    return 1;
  }
  (void)trylock1(); // beta-note{{mutex acquired here}}
} // beta-warning{{mutex 'mu1' is still held at the end of function}} beta-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning{{non-void function does not return a value in all control paths}}

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
    lock(&mu); // beta-note{{mutex acquired here}}
    ret = 2;
  }
  DEREFS
  if (flag)
    s += 1;
  return ret; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Irreducible cycles.
//===----------------------------------------------------------------------===//

int irreducible_inner_cycle(int n, int c) TRY1 { // beta-note{{mutex acquired here}}
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
    return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  lock(&mu);
  return 1;
}

int irreducible_keeps_pending(int c) TRY1 {
  int z = 0;
  (void)trylock1(); // beta-note{{mutex acquired here}}
  if (z == 0)
    goto B2;
  else {
  B1:
    if (c)
      return 0; // beta-warning{{mutex 'mu1' is still held at the end of function}}
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
  (void)trylock(&marr[0]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[1]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[2]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[3]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[4]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[5]); // beta-note{{mutex acquired here}}
  (void)trylock(&marr[6]); // beta-note{{mutex acquired here}}
  // beta-warning-re@+1 7{{mutex 'marr[{{[0-6]}}]' is still held at the end of function}}
  return 0;
}

int dual_range() __attribute__((try_acquire_capability_range(1, 2, mu)))
    __attribute__((try_acquire_shared_capability_range(3, 4, mu)));
int dual_range_wrapper()
    __attribute__((try_acquire_capability_range(1, 2, mu)))
    __attribute__((try_acquire_shared_capability_range(3, 4, mu))) {
  return dual_range();
}

int discarded_resolved_at_call() TRY1 {
  struct Mutex *m = &mu1;
  (void)trylock(m); // beta-note{{mutex acquired here}}
  m = nullptr;
  return 0; // beta-warning{{mutex 'mu1' is still held at the end of function}}
}

//===----------------------------------------------------------------------===//
// Return values that would fork into exponentially many outcomes.
//===----------------------------------------------------------------------===//

#define T6(b)                                                                  \
  (trylock(&marr[(b)]), trylock(&marr[(b) + 1]), trylock(&marr[(b) + 2]),      \
   cond())
int nested_conditionals() TRY1 {
  // beta-note@+2 6{{mutex acquired here}}
  // beta-warning-re@+1 6{{mutex 'marr[{{.*}}]' is still held at the end of function}}
  return T6(0) ? 0 : T6(3) ? 0 : T6(0) ? 0 : T6(3) ? 0 : T6(0) ? 0 : T6(3) ? 0 : 0;
}

struct AddrS {
  int a;
  int arr[4];
  int &ref;
};

// Pointer-to-data-member literal &AddrS::a is non-null.
int AddrS::*try_memptr_impl(bool ok)
    __attribute__((try_acquire_capability(true, mu))) {
  if (!ok)
    return nullptr;
  lock(&mu);
  return &AddrS::a;
}

//===----------------------------------------------------------------------===//
// Retry loops, irreducible cycles, GNU ?: and non-local assignments.
//===----------------------------------------------------------------------===//

#define TRY0 __attribute__((try_acquire_capability_range(0, 0, mu)))
#define TRY_RANGE(lo, hi) __attribute__((try_acquire_capability_range(lo, hi, mu)))
int tr_1_2() TRY_RANGE(1, 2);

// Loop bodies are not simulated: the values of the variables that a loop
// modifies are not known at the loop header. Hence, the result of a trylock
// call that is retried in a loop is not correlated with the loop exit
// condition, which causes false positives.
int retry_while_not_r() TRY1 { // beta-note{{mutex acquired here}}
  int r = 0;
  while (!r && cond())
    r = trylock(&mu); // beta-note{{mutex acquired here}}
  return r; // beta-warning{{mutex 'mu' is still held at the end of function}} beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int retry_do_while() TRY1 {
  int r;
  int n = 0;
  do {
    r = trylock(&mu); // beta-note{{mutex acquired here}}
  } while (!r && ++n < 3); // beta-warning{{mutex 'mu' is not held on every path through here}}
  return r;
}

// Retrying a trylock call whose result is tested directly is supported.
int retry_tested_in_loop() TRY1 {
  for (int n = 0; n < 3; ++n)
    if (trylock(&mu))
      return 1;
  return 0;
}

// A trylock result that a later iteration overwrites before it is tested may
// still be held when the loop exits.
int overwritten_in_loop_body() TRY1 {
  int r = 0;
  while (cond())
    r = trylock(&mu); // beta-note{{mutex acquired here}}
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int irreducible_cycle_preserves_unmodified() TRY0 {
  int r = try0();
  if (r != 0)
    return r;
  int n = 0;
  if (cond())
    goto b;
a:
  if (++n > 3)
    return r;
b:
  if (cond())
    goto a;
  return r;
}

int gnu_binary_conditional_callee() TRY1 {
  return trylock(&mu) ?: 0;
}

void gnu_binary_conditional_caller() {
  if ((trylock(&mu) ?: 0) != 0) {
    data = 1;
    unlock(&mu);
  }
}

struct NonLocalStore {
  int y;
  unsigned bf : 1;
};

int store_to_member_ret(NonLocalStore *s) TRY_RANGE(1, 2) {
  return s->y = tr_1_2();
}

int store_to_bitfield_trunc(NonLocalStore *s) TRY_RANGE(2, 2) {
  int two = 2;
  lock(&mu); // beta-note{{mutex acquired here}}
  return (s->bf = two); // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int ternary_cond_narrows_arm(int x) TRY1 {
  if (x == 0)
    lock(&mu);
  return (x == 0) ? (x + 1) : 0;
}

int logical_and_narrows_rhs(int x) TRY1 {
  if (x == 1)
    lock(&mu);
  return (x == 1) && (x - 1 == 0);
}

long ptr_diff_element_scale() TRY_RANGE(2, 2) {
  int *p = nullptr;
  int *q = (int *)8;
  if (cond()) {
    lock(&mu);
    return q - p;
  }
  return 0;
}

int negate_int_min_and_sub(int x) TRY1 {
  int r = trylock(&mu);
  if (!r)
    return 0;
  int v = (x ? (-2147483647 - 1) : 1);
  int neg = -v;
  (void)neg;
  return 1 - 0;
}

struct BasePad {
  int pad;
};
struct BaseLock {
  int b;
};
struct DerivedNonZeroOffset : BasePad, BaseLock {};
DerivedNonZeroOffset *try_derived_lock() __attribute__((try_acquire_capability(1, mu)));

BaseLock *derived_to_base_nonzero_offset()
    __attribute__((try_acquire_capability(1, mu))) {
  DerivedNonZeroOffset *d = try_derived_lock();
  if (!d)
    return nullptr;
  return d;
}

struct AliasNode {
  Mutex lock;
};
struct AliasReq {
  AliasNode *head;
};
void load_ptr_by_ref(AliasNode *&out, AliasNode *in);

int trylock_alias_loaded_by_cpp_ref_unresolved(AliasReq *r)
    __attribute__((try_acquire_capability(1, r->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = nullptr;
  load_ptr_by_ref(h, r->head);
  return trylock(&h->lock); // beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'r->head->lock' to be held at the end of function}} beta-note{{mutex acquired here}}
}

int trylock_alias_loaded_by_cpp_ref_bad(AliasReq *r, AliasReq *r2)
    __attribute__((try_acquire_capability(1, r->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = nullptr;
  load_ptr_by_ref(h, r2->head);
  return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'r->head->lock' to be held at the end of function}}
}

// Reassigning a local pointer after a trylock call in a trylock body must
// still resolve the capability against the variable's value at the call site.
int trylock_body_reassigned_ptr_ok(Mutex *m1, Mutex *m2)
    __attribute__((try_acquire_capability(1, *m1))) {
  Mutex *p = m1;
  int r = trylock(p);
  p = m2;
  return r;
}

int trylock_body_reassigned_ptr_wrong_cap_bad(Mutex *m1, Mutex *m2)
    __attribute__((try_acquire_capability(1, *m2))) { // beta-note{{mutex acquired here}}
  Mutex *p = m1;
  int r = trylock(p); // beta-note{{mutex acquired here}}
  p = m2;
  return r; // beta-warning{{mutex 'm1' is still held at the end of function}} beta-warning{{expecting mutex 'm2' to be held at the end of function}}
}

// Capabilities acquired through unresolved local pointers for
// 'this->head->lock' and assignment through a comma lvalue.
struct AliasThisHolder {
  AliasNode *head;

  int trylock_this_head_unresolved()
      __attribute__((try_acquire_capability(1, head->lock))) { // beta-note{{mutex acquired here}}
    AliasNode *h = nullptr;
    load_ptr_by_ref(h, head);
    return trylock(&h->lock); // beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'head->lock' to be held at the end of function}} beta-note{{mutex acquired here}}
  }

  int trylock_this_head_other_bad(AliasReq *other)
      __attribute__((try_acquire_capability(1, head->lock))) { // beta-note{{mutex acquired here}}
    AliasNode *h = nullptr;
    load_ptr_by_ref(h, other->head);
    return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'head->lock' to be held at the end of function}}
  }

  int trylock_comma_lvalue_overwrite_bad(AliasReq *other)
      __attribute__((try_acquire_capability(1, head->lock))) { // beta-note{{mutex acquired here}}
    AliasNode *h = nullptr;
    load_ptr_by_ref(h, head);
    (cond(), h) = other->head;
    return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'head->lock' to be held at the end of function}}
  }
};

// Side-effecting subexpressions in return expressions must not overwrite
// variables read by the condition of ?: or the LHS of && / || / <<.
int return_ternary_arm_modifies_cond_var_bad() TRY0 { // beta-note{{mutex acquired here}}
  int x = 0;
  return (x == 0) ? ((x = 1), 0) : 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int return_logical_rhs_modifies_lhs_var_bad() TRY1 { // beta-note{{mutex acquired here}}
  int x = 0;
  return (x == 0) && ((x = 1), true); // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int return_shift_rhs_modifies_lhs_var_bad() TRY0 {
  int x = 1;
  lock(&mu); // beta-note{{mutex acquired here}}
  return x << ((x = 0), 0); // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// Trylock result assigned to a tracked local variable in a discarded
// comma LHS of a return statement must still be forked and checked.
int leak_comma_assign_in_return() TRY0 {
  int r;
  return (r = trylock_zero(), -1); // beta-note{{mutex acquired here}} beta-warning{{mutex 'mu' is still held at the end of function}}
}

// Overwritten trylock definitions in a loop whose terminator does not
// partition the success set must still be diagnosed as leaked.
int unknown_loop_pred(int);
int test_loop_unknown_pred_leak(int n) TRY1 {
  while (n-- > 0) {
    int r = trylock(&mu); // beta-note{{mutex acquired here}}
    if (unknown_loop_pred(r)) {
    }
  }
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int test_loop_partial_range_leak(int n) TRY0 {
  while (n-- > 0) {
    int r = trylock_zero(); // beta-note{{mutex acquired here}}
    if (r > 0) {
    }
  }
  return 1; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// CXXOperatorCallExpr (lambda/functor) that loads a local pointer and
// StmtExpr with inline assembly.
int test_alias_lambda_overwrite_bad(AliasReq *req, AliasReq *other)
    __attribute__((try_acquire_capability(1, req->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = req->head;
  auto redirect = [&](AliasNode *&p) { p = other->head; };
  redirect(h);
  return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'req->head->lock' to be held at the end of function}}
}

int test_alias_lambda_load_unresolved(AliasReq *req)
    __attribute__((try_acquire_capability(1, req->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = nullptr;
  auto load = [](AliasNode *&dst, AliasNode *src) { dst = src; };
  load(h, req->head);
  return trylock(&h->lock); // beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'req->head->lock' to be held at the end of function}} beta-note{{mutex acquired here}}
}

int test_alias_stmtexpr_asm_other_bad(AliasReq *req, AliasReq *other)
    __attribute__((try_acquire_capability(1, req->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = ({
    if (!req->head)
      return 0;
    AliasNode *tmp;
    asm("" : "=r"(tmp) : "m"(other->head));
    tmp;
  });
  return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'req->head->lock' to be held at the end of function}}
}

// Referencing a local variable that holds a trylock result multiple times in
// a return expression must not re-evaluate the trylock call as a second
// acquisition.
int test_return_ref_twice_bitand() TRY1 {
  int r = trylock(&mu);
  return r & r;
}

int test_return_ref_twice_bitor() TRY1 {
  int r = trylock(&mu);
  return r | r;
}

int test_return_ref_twice_ternary() TRY1 {
  int r = trylock(&mu);
  return r ? r : 0;
}

int test_return_ref_twice_add() TRY1 {
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  return r + r; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

static inline int id_trylock_val(int x) { return x; }

int test_return_ref_twice_inline_add() TRY1 {
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  return id_trylock_val(r) + r; // beta-warning{{mutex 'mu' is still held at the end of function}}
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

// Retry loops that test the stored trylock result in the loop body preserve
// the failure range across back edges when exiting via the loop condition.
int retry_body_break_while_ok() TRY1 {
  int r = 0;
  while (cond()) {
    r = trylock(&mu);
    if (r)
      break;
  }
  return r;
}

int retry_body_break_for_ok() TRY1 {
  int r = 0;
  for (int i = 0; i < 3; ++i) {
    r = trylock(&mu);
    if (r)
      break;
  }
  return r;
}

int retry_body_break_range_ok() TRY0 {
  int err = -1;
  for (int i = 0; i < 3; ++i) {
    err = trylock_zero();
    if (err == 0)
      break;
  }
  return err;
}

int retry_body_break_wrong_init_bad() TRY0 { // beta-note{{mutex acquired here}}
  int err = 0;
  while (cond()) {
    err = trylock_zero();
    if (err == 0)
      break;
  }
  return err; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int loop_multi_decl_untested_trylock_bad() TRY1 {
  for (int i = 0; i < 2; ++i) {
    int dummy = 0, r = trylock(&mu); // beta-note{{mutex acquired here}}
    (void)dummy;
    (void)r;
  }
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// The variable holds a comparison or the negation of the trylock result,
// which is tested on every path back to the loop header.
int retry_cmp_def_tested() TRY0 {
  for (int i = 0; i < 3; ++i) {
    bool ok = (trylock_zero() == 0);
    if (ok)
      return 0;
  }
  return -1;
}

int retry_not_def_tested() TRY0 {
  for (int i = 0; i < 3; ++i) {
    bool ok = !trylock_zero();
    if (ok)
      return 0;
  }
  return -1;
}

int retry_cmp_def_untested_bad() TRY0 {
  for (int i = 0; i < 3; ++i) {
    bool ok = (trylock_zero() == 0); // beta-note{{mutex acquired here}}
    (void)ok;
  }
  return -1; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int stmtexpr_modifies_outer_var_in_cmp_bad() TRY1 {
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  if (({ ok = 0; ok; }) == 0)
    return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
  return ok;
}

int stmtexpr_modifies_local_var_in_cmp_bad() TRY1 {
  int ok = trylock(&mu); // beta-note{{mutex acquired here}}
  if (({ int r = ok; r = 0; r; }) == 0)
    return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
  return ok;
}

int stmtexpr_return_modifies_outer_var_bad() TRY1 {
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  return ({ r = 0; r; }); // beta-warning{{mutex 'mu' is still held at the end of function}}
}

struct __attribute__((scoped_lockable)) ScopedMuGuard {
  ScopedMuGuard(struct Mutex *m) __attribute__((acquire_capability(m)));
  ~ScopedMuGuard() __attribute__((release_capability()));
};

int temp_scoped_guard_in_return_bad() TRY1 { // beta-note{{mutex acquired here}}
  return (ScopedMuGuard(&mu), 1); // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

struct AutoUnlockMu {
  ~AutoUnlockMu() __attribute__((release_capability(mu)));
};

int join_block_dtor_releases_target_bad(int c) TRY1 { // beta-note{{mutex acquired here}}
  AutoUnlockMu u;
  int ok = 0;
  if (c) {
    lock(&mu);
    ok = 1;
  } else {
    lock(&mu);
  }
  return ok; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

struct ExcludesMuDtor {
  ~ExcludesMuDtor() __attribute__((locks_excluded(mu)));
};

int dtor_excludes_lock_acquired_in_return_bad() TRY1 {
  ExcludesMuDtor d;
  return trylock(&mu); // beta-warning{{cannot call function '~ExcludesMuDtor' while mutex 'mu' is held}}
}

int dtor_excludes_lock_dedup_across_outcomes_bad()
    __attribute__((try_acquire_capability_range(1, 2, mu))) {
  ExcludesMuDtor d;
  return tr_1_2(); // beta-warning{{cannot call function '~ExcludesMuDtor' while mutex 'mu' is held}}
}

void inspect_const_ref(const int &v);

int lvalue_conditional_and_const_ref_preserve_range_ok(bool c) TRY1 {
  int x = 1;
  int y = 1;
  inspect_const_ref(x);
  int z = (c ? x : y);
  lock(&mu);
  return x & z;
}

int deref_lhs_modified_on_rhs_not_nonnull_bad(int *p) TRY1 { // beta-note{{mutex acquired here}}
  *p = (p = nullptr, 0);
  if (p) {
    lock(&mu);
    return 1;
  }
  return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int if_ternary_trylock_cond_ok() TRY1 {
  if (trylock(&mu) ? 1 : 0)
    return 1;
  return 0;
}

int asm_conditional_lvalue_output_invalidates_alias_bad(AliasReq *req,
                                                        AliasReq *other,
                                                        bool c)
    __attribute__((try_acquire_capability(1, req->head->lock))) { // beta-note{{mutex acquired here}}
  AliasNode *h = req->head;
  AliasNode *q = other->head;
  asm("" : "=r"(c ? h : q));
  return trylock(&h->lock); // beta-note{{mutex acquired here}} beta-warning{{mutex 'h->lock' is still held at the end of function}} beta-warning{{expecting mutex 'req->head->lock' to be held at the end of function}}
}

int narrowing_cast_in_branch_cond_leaks_bad() TRY1 { // beta-note{{mutex acquired here}}
  if ((char)trylock(&mu)) // beta-note{{mutex acquired here}}
    return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

int switch_on_logical_not_leaks_bad() TRY1 { // beta-note{{mutex acquired here}}
  switch ((int)!trylock(&mu)) { // beta-note{{mutex acquired here}}
  case 0:
    return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
  default:
    return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
  }
}

int consume_int(int x);

int unmodeled_call_with_trylock_arg_bad() TRY1 { // beta-note{{mutex acquired here}}
  return consume_int(trylock(&mu)); // beta-note{{mutex acquired here}} beta-warning{{mutex 'mu' is still held at the end of function}} beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int comma_modifies_var_in_pure_return_bad() TRY1 {
  int x = 1;
  lock(&mu); // beta-note{{mutex acquired here}}
  return (x = 0, x); // beta-warning{{mutex 'mu' is still held at the end of function}}
}

struct __attribute__((scoped_lockable)) ScopedTryTestLock {
  ScopedTryTestLock(Mutex *m) __attribute__((acquire_capability(m)));
  ~ScopedTryTestLock() __attribute__((release_capability()));
};

int sizeof_raii_lock_unevaluated_ok() TRY1 {
  (void)sizeof(({ ScopedTryTestLock l(&mu); 0; }));
  lock(&mu);
  return 1;
}

struct AliasHolderBox {
  Mutex *m;
  void reset();
};

void nonconst_member_call_invalidates_local_struct_alias(Mutex *m1) {
  AliasHolderBox box = {m1};
  box.reset();
  lock(box.m); // expected-note{{mutex acquired here}}
  unlock(m1); // expected-warning{{releasing mutex 'm1' that was not held}}
} // expected-warning{{mutex 'box.m' is still held at the end of function}}

int binary_cond_and_lhs_mod_in_pure_return_bad() TRY1 {
  int x = 1;
  lock(&mu); // beta-note{{mutex acquired here}}
  return ((x ?: 0) && ((x = 0) == 0 && x != 0)) ? 1 : 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// The values of the conditions that the return value forks on are the values
// that these had when they were evaluated. An operand that modifies 's'
// afterwards does not change them.
struct FlagMutexPair {
  bool flag;
  struct Mutex b;
};
bool check_pair(FlagMutexPair *s);

bool fork_cond_not_erased_lnot(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return !check_pair(&s) ? false : trylock(&s.b);
}

bool fork_cond_not_erased_eq(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return (check_pair(&s) == false) ? false : trylock(&s.b);
}

bool fork_cond_not_erased_member(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return s.flag ? trylock(&s.b) : false;
}

bool fork_cond_not_erased_and(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return s.flag && trylock(&s.b);
}

bool fork_stmtexpr_not_erased(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return ({ bool r = trylock(&s.b); r; }) && (check_pair(&s) || true);
}

// 'b' is derived from the result of trylock() that the return value
// refers to. Forking on the trylock() call for 'b' again would combine the
// success of one fork with the failure of the other.
int derived_unused_var() TRY1 {
  int r = trylock(&mu);
  int b = r + 1;
  (void)b;
  return r;
}

int derived_unused_var_bad() TRY1 {
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  int b = r + 1;
  (void)b;
  return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
}

// 't' is forked on before evaluating the return value because 'r' refers to
// it twice. Evaluating 'r' must not fork on 'trylock(&mu)' again.
int multi_ref_non_call_def(bool c) TRY1 {
  int t = trylock(&mu) != 0;
  int r = c ? t : t;
  return r;
}

int trylock_range12() __attribute__((try_acquire_capability_range(1, 2, mu)));

// 'is_one' is derived from 'r', which the return value refers to.
int derived_bool_var_range()
    __attribute__((try_acquire_capability_range(1, 2, mu))) {
  int r = trylock_range12();
  bool is_one = (r == 1);
  if (is_one) {
    data = 42;
    return 1;
  }
  return r;
}

// 'r' is forked on at 'return 0;' because the return value does not refer
// to it. 'b' is derived from the same trylock() call and must not be forked
// on again: that would combine the failure of one fork with the success of
// the other.
int derived_var_after_branch() TRY1 {
  int r = trylock(&mu);
  int b = r + 1;
  (void)b;
  if (r == 0)
    return 0;
  return 1;
}

int derived_var_after_cmp_branch() TRY1 {
  int r = trylock(&mu) != 0;
  int b = r + 1;
  (void)b;
  if (r == 0)
    return 0;
  return 1;
}

int derived_var_after_branch_bad() TRY1 { // beta-note{{mutex acquired here}}
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  int b = r + 1;
  (void)b;
  if (r != 0)
    return 0; // beta-warning{{mutex 'mu' is still held at the end of function}}
  return 1; // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// The overwritten result of trylock() is still referenced through 'saved'.
int overwritten_source_of_derived_var() TRY1 {
  int r = trylock(&mu);
  int saved = !r;
  r = 0;
  return !saved;
}

int overwritten_source_of_derived_var_bad() TRY1 { // beta-note{{mutex acquired here}}
  int r = trylock(&mu); // beta-note{{mutex acquired here}}
  int saved = !r;
  r = 0;
  return saved; // beta-warning{{mutex 'mu' is still held at the end of function}} \
                // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// 't' is initialized by an inline helper that does not return its argument
// unchanged. Evaluating 'r' must not fork on 'trylock(&mu)' again.
static inline int trylock_is_ok(int x) { return x != 0; }

int multi_ref_inline_helper_def(bool c) TRY1 {
  int t = trylock_is_ok(trylock(&mu));
  int r = c ? t : t;
  return r;
}

int multi_ref_inline_helper_def_bad(bool c) TRY1 { // beta-note{{mutex acquired here}}
  int t = trylock_is_ok(trylock(&mu)); // beta-note{{mutex acquired here}}
  int r = c ? t : t;
  return !r; // beta-warning{{mutex 'mu' is still held at the end of function}} \
             // beta-warning{{expecting mutex 'mu' to be held at the end of function}}
}

// The result of trylock() in a statement expression that is only evaluated
// conditionally is forked on before the return value is evaluated. The value
// of the statement expression is the value of 'r' in each fork.
bool btrylock(struct Mutex *m) __attribute__((try_acquire_capability(true, m)));

bool stmtexpr_land_rhs(bool c) __attribute__((try_acquire_capability(true, mu))) {
  return c && ({ bool r = btrylock(&mu); r; });
}

bool stmtexpr_lor_rhs(bool c) __attribute__((try_acquire_capability(true, mu))) {
  return (c && false) || ({ bool r = btrylock(&mu); r; });
}

bool stmtexpr_cond_arm(bool c) __attribute__((try_acquire_capability(true, mu))) {
  return c ? ({ bool r = btrylock(&mu); r; }) : false;
}

bool stmtexpr_land_rhs_bad(bool c) __attribute__((try_acquire_capability(true, mu))) { // beta-note{{mutex acquired here}}
  return c && ({ bool r = btrylock(&mu); !r; }); // beta-warning{{mutex 'mu' is still held at the end of function}} \
                                                 // beta-warning{{expecting mutex 'mu' to be held at the end of function}} \
                                                 // beta-note{{mutex acquired here}}
}

// Modifying 's' does not change the value of a statement expression that
// does not refer to 's'.
bool stmtexpr_not_erased_by_mod(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return (check_pair(&s), (s.flag || true) && trylock(&s.b) &&
                              ({ int v = 1; int y = v; y; }));
}

bool stmtexpr_not_erased_by_mod_bad(FlagMutexPair &s)
    __attribute__((try_acquire_capability(1, s.b))) {
  return (check_pair(&s), (s.flag || true) && trylock(&s.b) && // beta-note{{mutex acquired here}} beta-warning{{mutex 's.b' is still held at the end of function}}
                              ({ int v = 0; int y = v; y; }));
}
