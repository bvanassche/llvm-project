// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta %s
// RUN: %clang_cc1 -fsyntax-only -verify=nobeta -Wthread-safety %s

// Leaked capabilities in the bodies of try_acquire functions that must be
// diagnosed, and correct code that must not be. The bodies of try_acquire
// functions are only checked with -Wthread-safety-beta.
// nobeta-no-diagnostics

struct __attribute__((capability("mutex"))) Mutex { int x; };
extern struct Mutex mu, mu2;
void lock(struct Mutex *m) __attribute__((acquire_capability(m)));
void unlock(struct Mutex *m) __attribute__((release_capability(m)));
int trylock(struct Mutex *m) __attribute__((try_acquire_capability(1, m)));
int cond(void);
int g;

#define TRY1 __attribute__((try_acquire_capability(1, mu)))

// Trylock calls in a loop whose results are discarded or overwritten before
// they are tested must not be forgotten on the edges that leave the loop at
// its header.
int loop_discarded(void) TRY1 {
  while (cond())
    trylock(&mu); // expected-note{{mutex acquired here}}
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int loop_overwritten(void) TRY1 {
  int r = 0;
  for (int i = 0; i < 3; i++)
    r = trylock(&mu2); // expected-note{{mutex acquired here}}
  return trylock(&mu); // expected-warning{{mutex 'mu2' is still held at the end of function}}
}

int loop_global(void) TRY1 {
  while (cond())
    g = trylock(&mu2); // expected-note{{mutex acquired here}}
  return trylock(&mu); // expected-warning{{mutex 'mu2' is still held at the end of function}}
}

int loop_scoped_local(void) TRY1 {
  while (cond()) {
    int t = trylock(&mu2); // expected-note{{mutex acquired here}}
    (void)t;
  }
  return trylock(&mu); // expected-warning{{mutex 'mu2' is still held at the end of function}}
}

int do_while_discarded(void) TRY1 {
  do
    trylock(&mu); // expected-note{{mutex acquired here}}
  while (cond());
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

// The capabilities of a trylock call whose result is tested in a loop are
// tracked in the lockset. Releasing them in the loop is correct.
int loop_released_scoped(void) TRY1 {
  while (cond()) {
    int t = trylock(&mu2);
    if (t)
      unlock(&mu2);
  }
  return trylock(&mu);
}

int loop_released(void) TRY1 {
  int r;
  while (cond()) {
    r = trylock(&mu2);
    if (r)
      unlock(&mu2);
  }
  return trylock(&mu);
}

int loop_released_direct(void) TRY1 {
  while (cond())
    if (trylock(&mu2))
      unlock(&mu2);
  return trylock(&mu);
}

int loop_return_on_success(void) TRY1 {
  for (int i = 0; i < 3; i++)
    if (trylock(&mu))
      return 1;
  return 0;
}

// A result that is only tested on some of the paths back to the loop header
// may leak into the next iteration and out of the loop.
int loop_tested_conditionally(int c1, int c2) TRY1 {
  while (c1) {
    int r = trylock(&mu); // expected-note{{mutex acquired here}}
    if (c2) {
      if (r)
        return 1;
    }
  }
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int loop_continue_before_test(int c1, int c2) TRY1 {
  while (c1) {
    int r = trylock(&mu); // expected-note{{mutex acquired here}}
    if (c2)
      continue;
    if (r)
      return 1;
  }
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int infinite_loop_continue_before_test(int c1, int c2) TRY1 {
  while (1) {
    int r = trylock(&mu); // expected-note{{mutex acquired here}}
    if (c1)
      continue;
    if (r)
      return 1;
    if (c2)
      return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
  }
}

int infinite_loop_tested(int c2) TRY1 {
  while (1) {
    int r = trylock(&mu);
    if (r)
      return 1;
    if (c2)
      return 0;
  }
}

int loop_continue_after_test(int c1) TRY1 {
  while (c1) {
    int r = trylock(&mu);
    if (!r)
      continue;
    return 1;
  }
  return 0;
}

// An edge on which a direct trylock call may return both success and
// failure values may carry the capabilities of the call.
int mixed_eq(void) TRY1 {
  if (trylock(&mu) == 1) // expected-note{{mutex acquired here}}
    return 1;
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int mixed_ne(void) TRY1 {
  if (trylock(&mu) != 1) // expected-note{{mutex acquired here}}
    return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
  return 1;
}

// '__extension__' does not hide a returned trylock call.
int extension_return(void) TRY1 {
  return __extension__ trylock(&mu);
}

int mixed_le(void) TRY1 {
  if (trylock(&mu) <= 5) // expected-note{{mutex acquired here}}
    return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
  return 1;
}

int mixed_switch_default(void) TRY1 {
  switch (trylock(&mu)) { // expected-note{{mutex acquired here}}
  case 1:
    return 1;
  default:
    return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
  }
}

int unmixed_eq(void) TRY1 {
  if (trylock(&mu) == 0)
    return 0;
  return 1;
}

int unmixed_switch(void) TRY1 {
  switch (trylock(&mu)) {
  case 0:
    return 0;
  default:
    return 1;
  }
}

// A long chain of definitions must not make the analysis forget a trylock
// result.
int long_def_chain(void) TRY1 {
  int r = trylock(&mu); // expected-note{{mutex acquired here}}
  r = r + 0; r = r + 0; r = r + 0; r = r + 0; r = r + 0;
  r = r + 0; r = r + 0; r = r + 0; r = r + 0; r = r + 0;
  r = r + 0; r = r + 0; r = r + 0; r = r + 0; r = r + 0;
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int deep_expression(void) TRY1 {
  // expected-warning@+1{{mutex 'mu' is still held at the end of function}}
  return ((((((((((((((((((((((((((trylock(&mu) + 0) + 0) + 0) + 0) + 0) + // expected-note{{mutex acquired here}}
           0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) +
           0) + 0) + 0) + 0) + 0) + 0) + 0) + 0) && 0;
}

// A DAG of definitions must be analyzed in linear time.
int mix(int, int, int, int, int, int, int, int);
#define M(v) mix(v, v, v, v, v, v, v, v)
int definition_dag(int a) TRY1 {
  int b = M(a), c = M(b), d = M(c), e = M(d), f = M(e), h = M(f), i = M(h);
  int j = M(i), k = M(j), l = M(k), m = M(l), n = M(m), o = M(n), p = M(o);
  (void)p;
  return trylock(&mu);
}

// A return value that depends on the results of more trylock calls than the
// number of lock states that are tracked separately. The lock states that
// lead to the same return values are merged. A capability that is only
// acquired on some of the merged paths may leak but does not count as held.
extern struct Mutex m[7];
int merged_outcomes(void) TRY1 { // expected-note{{mutex acquired here}}
  return (((((((trylock(&mu) == trylock(&m[0])) == trylock(&m[1])) == trylock(&m[2])) == trylock(&m[3])) == trylock(&m[4])) == trylock(&m[5])) == trylock(&m[6])) ? 1 : 1; // expected-note 7 {{mutex acquired here}} expected-warning{{expecting mutex 'mu' to be held at the end of function}} expected-warning-re 7 {{mutex 'm[{{[0-6]}}]' is still held at the end of function}}
}

// Passing the addresses of two members or elements of the same object to the
// trylock calls in a return value must not make the analysis forget the
// result of the first call. Both functions only leak the first capability,
// if the second trylock call fails.
struct MutexPair { struct Mutex a, b; } pair;
struct Mutex marr[2];
int member_pair(void) __attribute__((try_acquire_capability(1, pair.a, pair.b))) {
  return trylock(&pair.a) ? trylock(&pair.b) : 0; // expected-note{{mutex acquired here}} expected-warning{{mutex 'pair.a' is still held at the end of function}}
}
int array_pair(void) __attribute__((try_acquire_capability(1, marr[0], marr[1]))) {
  return trylock(&marr[0]) && trylock(&marr[1]); // expected-note{{mutex acquired here}} expected-warning{{mutex 'marr[0]' is still held at the end of function}}
}

// The return type cannot represent every success value: a success value
// of trylock(), e.g. 256, may be truncated to the failure value 0.
char narrowed_return(void) TRY1 {
  return trylock(&mu); // expected-note{{mutex acquired here}} expected-warning{{mutex 'mu' is still held at the end of function}}
}

struct TypedItem {
  int x;
};
struct TypedItem *get_typed_locked(void)
    __attribute__((try_acquire_capability_range(1, (__UINTPTR_TYPE__)-4096, mu)));
static inline int is_err_ptr(const void *p) {
  return (__UINTPTR_TYPE__)p >= (__UINTPTR_TYPE__)-4095;
}

int implicit_cast_two_step(void)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  void *p = get_typed_locked();
  if (!p)
    return -12;
  if (is_err_ptr(p))
    return -14;
  return 0;
}

int trylock_shared(struct Mutex *m)
    __attribute__((try_acquire_shared_capability(1, *m)));
int sink7(int, int, int, int, int, int, int);

// The return value of sink7() does not depend on the values of the trylock
// calls in its arguments, so the outcomes of these calls are merged instead
// of exceeding the outcome limit. Returning 1 with 'mu' held shared violates
// TRY1.
int merged_outcomes_excl_vs_shared(int c) TRY1 { // expected-note{{the other acquisition of mutex 'mu' is here}}
  return sink7(trylock(&m[0]), trylock(&m[1]), trylock(&m[2]), // expected-note 3 {{mutex acquired here}} expected-warning-re 6 {{mutex 'm[{{[0-5]}}]' is still held at the end of function}}
               trylock(&m[3]), trylock(&m[4]), trylock(&m[5]), c) // expected-note 3 {{mutex acquired here}}
             ? trylock(&mu)
             : trylock_shared(&mu); // expected-warning{{mutex 'mu' is acquired exclusively and shared in the same scope}}
}

int multi_range_same_cap(void)
    __attribute__((try_acquire_capability_range(1, 2, mu)))
    __attribute__((try_acquire_capability_range(4, 5, mu)));

int multi_range_same_cap_body(void)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int r = multi_range_same_cap();
  if (r < 1)
    return -1;
  if (r == 3)
    return -1;
  if (r > 5)
    return -1;
  return 0;
}

// A trylock result that is only referenced by a subexpression of the return
// value that is not evaluated must not be forgotten.
int short_circuited_result_ref(void) TRY1 {
  int r = trylock(&mu); // expected-note{{mutex acquired here}}
  return (0 && r == 1) ? 1 : 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int short_circuited_result_ref_param(int err) TRY1 {
  int r = trylock(&mu); // expected-note{{mutex acquired here}}
  if (err)
    return (!err && r == 1) ? 1 : 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
  return r;
}

int unevaluated_result_ref(void) TRY1 {
  int r = trylock(&mu); // expected-note{{mutex acquired here}}
  return sizeof(r) == 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

// A trylock call that is the value of a statement expression with side
// effects must not be forgotten.
int stmt_expr_with_side_effect_unused(void) TRY1 {
  int r = ({ g++; trylock(&mu); }); // expected-note{{mutex acquired here}}
  (void)r;
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}

int stmt_expr_with_side_effect_returned(void) TRY1 {
  int r = ({ g++; trylock(&mu); });
  return r;
}

// The lock state at the exit of a trylock function whose return value cannot
// be modeled is not checked.
void unmodeled_return_type(int c) TRY1 {
  if (c) {
    lock(&mu);
    return;
  }
}

// A cleanup function that releases the capability acquired by the trylock
// call in the return value leaves the capability unheld for the caller. Only
// report that once.
void unlock_mu_cleanup(int *p) __attribute__((release_capability(mu)));
int cleanup_releases_returned_trylock(void) TRY1 { // expected-note{{mutex acquired here}}
  int x __attribute__((cleanup(unlock_mu_cleanup))) = 0;
  return trylock(&mu); // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}
