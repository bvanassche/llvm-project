// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DMANY_BRANCHES %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DNESTED_COMPARISONS %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DDISTINCT_MUTEXES %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DMANY_SCOPES %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DOUTCOME_BUDGET %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DFORK_LIMIT %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DSEQUENTIAL_TRYLOCKS %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DEARLY_RETURNS %s

// Verifying the implementation of a trylock function must take neither
// quadratic time in the size of the function nor exponential time in the
// number of trylock calls in a return value.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};
struct Mutex mu;
void lock(struct Mutex *m) __attribute__((acquire_capability(m)));
void unlock(struct Mutex *m) __attribute__((release_capability(m)));
int trylock(struct Mutex *m) __attribute__((try_acquire_capability(1, m)));
int get_value(void);
void use_value(int v);

#define REP4(x) x x x x
#define REP16(x) REP4(REP4(x))
#define REP1024(x) REP4(REP16(REP16(x)))

#ifdef MANY_BRANCHES
// expected-no-diagnostics

// Each branch narrows the range of a local variable and the join after the
// branch widens it again to its whole domain. Keeping such ranges in the
// value state would make the analysis quadratic in the number of branches.
int many_branches(void)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  REP1024({
    int v = get_value();
    if (v > 0)
      use_value(v);
  })
  lock(&mu);
  return 0;
}
#endif

#ifdef MANY_SCOPES
// expected-no-diagnostics

// Each block declares a variable with its own scope and has an edge to the
// same label. Keeping the ranges of variables that are out of scope or the
// value states of all blocks would make the memory use quadratic in the
// number of blocks.
int many_scopes(int x)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int v = 0;
  if (!trylock(&mu))
    return -1;
  REP1024({
    int a = get_value();
    if (a == x) {
      v = a;
      goto out;
    }
  })
out:
  use_value(v);
  return 0;
}
#endif

#ifdef NESTED_COMPARISONS
// Without merging the return outcomes that only differ in their values, the
// number of outcomes would double with every trylock call.
#define CMP(x) ((x) == trylock(&mu))
#define CMP2(x) CMP(CMP(x))
#define CMP4(x) CMP2(CMP2(x))
#define CMP8(x) CMP4(CMP4(x))
#define CMP16(x) CMP8(CMP8(x))
#define CMP32(x) CMP16(CMP16(x))

int nested_comparisons(void) __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  // When the return value is too complex to track its outcomes separately,
  // the analysis assumes that every trylock call in it may have acquired its
  // capabilities for every return value. Such a capability is reported if
  // it is not expected to be held and does not count as held otherwise.
  return CMP32(trylock(&mu)); // expected-warning{{mutex 'mu' is still held at the end of function}} expected-note{{mutex acquired here}} expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}
#endif

#ifdef DISTINCT_MUTEXES
// When there are too many outcomes, the capabilities acquired by the trylock
// calls in the return value must not be forgotten.
struct Mutex m[7];
int distinct_mutexes(void) __attribute__((try_acquire_capability(1, mu))) {
  // expected-warning-re@+4 7{{mutex 'm[{{[0-6]}}]' is still held at the end of function}}
  // expected-note@+3 3{{mutex acquired here}}
  // expected-note@+3 3{{mutex acquired here}}
  // expected-note@+3 {{mutex acquired here}}
  return ((((((trylock(&m[0]) == trylock(&m[1])) == trylock(&m[2])) ==
             trylock(&m[3])) == trylock(&m[4])) == trylock(&m[5])) ==
          trylock(&m[6])) && 0;
}
#endif

#ifdef OUTCOME_BUDGET
// When the return value has too many outcomes, a capability that is only
// acquired on some paths must not satisfy the capability that is expected to
// be held: if trylock() fails, r is 0 and the function returns 1 without
// holding mu.
int cond(int i);
#define BRANCH(i)                                                              \
  int x##i;                                                                    \
  if (cond(0##i))                                                              \
    x##i = r;                                                                  \
  else                                                                         \
    x##i = 2 * r;
#define BRANCH8(a)                                                             \
  BRANCH(a##0) BRANCH(a##1) BRANCH(a##2) BRANCH(a##3) BRANCH(a##4)             \
  BRANCH(a##5) BRANCH(a##6) BRANCH(a##7)
#define AND(i) x##i &&
#define AND8(a)                                                                \
  AND(a##0) AND(a##1) AND(a##2) AND(a##3) AND(a##4) AND(a##5) AND(a##6)        \
  AND(a##7)
int missing_acquire(void) __attribute__((try_acquire_capability(1, mu))) { // expected-note{{mutex acquired here}}
  int r = trylock(&mu);
  BRANCH8(0) BRANCH8(1) BRANCH8(2) BRANCH8(3)
  BRANCH8(4) BRANCH8(5) BRANCH8(6) BRANCH8(7)
  return (AND8(0) AND8(1) AND8(2) AND8(3) AND8(4) AND8(5) AND8(6) AND8(7) 1) + 1; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}
#endif

#ifdef FORK_LIMIT
// The return value of six_calls() has 2^6 = 64 outcomes, the maximum number
// that is tracked separately, so only the capabilities that leak if some of
// the trylock calls fail are reported. The return value of seven_calls() has
// 128 outcomes. The analysis then assumes that every trylock call may have
// acquired its capability for every return value, so these capabilities do
// not count as held for the success value either.
struct Mutex m0, m1, m2, m3, m4, m5, m6;
#define TRY_VAL(m, v) (trylock(&m) ? (v) : 0)
int six_calls(void)
    __attribute__((try_acquire_capability_range(63, 63, m0, m1, m2, m3, m4, m5))) {
  // expected-warning-re@+2 6{{mutex 'm{{[0-5]}}' is still held at the end of function}}
  // expected-note@+1 4{{mutex acquired here}}
  return TRY_VAL(m0, 1) + TRY_VAL(m1, 2) + TRY_VAL(m2, 4) + TRY_VAL(m3, 8) +
         TRY_VAL(m4, 16) + TRY_VAL(m5, 32); // expected-note 2{{mutex acquired here}}
}
int seven_calls(void) __attribute__((
    try_acquire_capability_range(127, 127, m0, m1, m2, m3, m4, m5, m6))) { // expected-note 7{{mutex acquired here}}
  // expected-warning-re@+3 7{{mutex 'm{{[0-6]}}' is still held at the end of function}}
  // expected-warning-re@+2 7{{expecting mutex 'm{{[0-6]}}' to be held at the end of function}}
  // expected-note@+1 4{{mutex acquired here}}
  return TRY_VAL(m0, 1) + TRY_VAL(m1, 2) + TRY_VAL(m2, 4) + TRY_VAL(m3, 8) +
         TRY_VAL(m4, 16) + TRY_VAL(m5, 32) + TRY_VAL(m6, 64); // expected-note 3{{mutex acquired here}}
}
#endif

#ifdef SEQUENTIAL_TRYLOCKS
// expected-no-diagnostics

// The result of each trylock call is materialized by the branch on it and
// released or returned. Forking on the materialized results at every return
// statement would make the analysis cubic in the number of trylock calls.
int sequential_trylocks(void) __attribute__((try_acquire_capability(1, mu))) {
  REP1024({
    int r = trylock(&mu);
    if (r) {
      if (get_value())
        return r;
      unlock(&mu);
    }
  })
  return 0;
}
#endif

#ifdef EARLY_RETURNS
// The result of each trylock call is stored in a variable whose scope ends
// on the failure path of the branch on it. Keeping such results in the value
// state and forking on these at every subsequent return statement would make
// the analysis cubic in the number of trylock calls and would exceed the
// budget for evaluating a return value, which reports a false positive.
int early_returns(void) __attribute__((try_acquire_capability(1, mu))) {
  REP1024({
    int r = (trylock(&mu) != 0);
    if (r)
      return 1;
  })
  return 0;
}

// A result that may still be held when its scope ends is not dropped.
int early_returns_leak(void) __attribute__((try_acquire_capability(1, mu))) {
  REP16({
    int r = (trylock(&mu) != 0);
    if (r)
      return 1;
  })
  {
    int r = (trylock(&mu) != 0); // expected-note{{mutex acquired here}}
    (void)r;
  }
  return 0; // expected-warning{{mutex 'mu' is still held at the end of function}}
}
#endif
