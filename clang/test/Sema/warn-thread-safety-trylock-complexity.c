// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -DMANY_BRANCHES %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -DNESTED_COMPARISONS %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -DDISTINCT_MUTEXES %s
// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -DMANY_SCOPES %s

// Verifying the implementation of a trylock function must take neither
// quadratic time in the size of the function nor exponential time in the
// number of trylock calls in a return value.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};
struct Mutex mu;
void lock(struct Mutex *m) __attribute__((acquire_capability(m)));
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

int nested_comparisons(void) __attribute__((try_acquire_capability(1, mu))) {
  // When the return value is too complex to track its outcomes separately,
  // the analysis assumes that every trylock call in it has acquired its
  // capabilities for every return value.
  return CMP32(trylock(&mu)); // expected-warning{{mutex 'mu' is still held at the end of function}} expected-note{{mutex acquired here}}
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

