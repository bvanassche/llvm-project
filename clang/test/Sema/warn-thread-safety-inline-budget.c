// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety %s

// Each CFG block has its own inline expansion budget. A trylock check that
// is expanded through a chain of inline helpers must still be recognized
// after many such checks in the same function.

// expected-no-diagnostics

struct __attribute__((capability("mutex"))) Mutex { int x; };
struct Mutex mu;
int data __attribute__((guarded_by(mu)));
void unlock(void) __attribute__((release_capability(mu)));

#define MAX_ERRNO 4095
static inline int is_err_value(unsigned long x) {
  return x >= (unsigned long)-MAX_ERRNO;
}
static inline int is_err(const void *ptr) {
  return is_err_value((unsigned long)ptr);
}
static inline int is_ok(const void *ptr) { return !is_err(ptr); }

void *get_locked(void)
    __attribute__((try_acquire_capability_range(1, -(unsigned long)MAX_ERRNO - 1, mu)));

#define CHECK                                                                  \
  {                                                                            \
    void *p = get_locked();                                                    \
    if (!p || !is_ok(p))                                                       \
      return;                                                                  \
    data = 1;                                                                  \
    unlock();                                                                  \
  }
#define CHECK10 CHECK CHECK CHECK CHECK CHECK CHECK CHECK CHECK CHECK CHECK
#define CHECK100                                                               \
  CHECK10 CHECK10 CHECK10 CHECK10 CHECK10 CHECK10 CHECK10 CHECK10 CHECK10 CHECK10

void many_checks(void) {
  CHECK100
  CHECK100
}
