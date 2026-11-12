// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -fsyntax-only -verify -Wthread-safety -Wthread-safety-pointer -Wthread-safety-beta %s
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -fsyntax-only -verify -Wthread-safety -Wthread-safety-pointer -Wthread-safety-beta -fexperimental-late-parse-attributes -DLATE_PARSING %s
// RUN: %clang_cc1 -triple i686-unknown-linux-gnu -fsyntax-only -verify -Wthread-safety -Wthread-safety-pointer -Wthread-safety-beta %s
// RUN: %clang_cc1 -triple x86_64-pc-windows-msvc -fsyntax-only -verify -Wthread-safety -Wthread-safety-pointer -Wthread-safety-beta %s

#define LOCKABLE            __attribute__ ((lockable))
#define REENTRANT_CAPABILITY __attribute__ ((reentrant_capability))
#define SCOPED_LOCKABLE     __attribute__ ((scoped_lockable))
#define GUARDED_BY(...)     __attribute__ ((guarded_by(__VA_ARGS__)))
#define GUARDED_VAR         __attribute__ ((guarded_var))
#define PT_GUARDED_BY(...)  __attribute__ ((pt_guarded_by(__VA_ARGS__)))
#define PT_GUARDED_VAR      __attribute__ ((pt_guarded_var))
#define ACQUIRED_AFTER(...) __attribute__ ((acquired_after(__VA_ARGS__)))
#define ACQUIRED_BEFORE(...) __attribute__ ((acquired_before(__VA_ARGS__)))
#define EXCLUSIVE_LOCK_FUNCTION(...)    __attribute__ ((exclusive_lock_function(__VA_ARGS__)))
#define SHARED_LOCK_FUNCTION(...)       __attribute__ ((shared_lock_function(__VA_ARGS__)))
#define ASSERT_EXCLUSIVE_LOCK(...)      __attribute__ ((assert_exclusive_lock(__VA_ARGS__)))
#define ASSERT_SHARED_LOCK(...)         __attribute__ ((assert_shared_lock(__VA_ARGS__)))
#define EXCLUSIVE_TRYLOCK_FUNCTION(...) __attribute__ ((exclusive_trylock_function(__VA_ARGS__)))
#define SHARED_TRYLOCK_FUNCTION(...)    __attribute__ ((shared_trylock_function(__VA_ARGS__)))
#define UNLOCK_FUNCTION(...)            __attribute__ ((unlock_function(__VA_ARGS__)))
#define LOCK_RETURNED(x)    __attribute__ ((lock_returned(x)))
#define LOCKS_EXCLUDED(...) __attribute__ ((locks_excluded(__VA_ARGS__)))
#define EXCLUSIVE_LOCKS_REQUIRED(...) \
  __attribute__ ((exclusive_locks_required(__VA_ARGS__)))
#define SHARED_LOCKS_REQUIRED(...) \
  __attribute__ ((shared_locks_required(__VA_ARGS__)))
#define NO_THREAD_SAFETY_ANALYSIS  __attribute__ ((no_thread_safety_analysis))

#define __READ_ONCE(x)        (*(const volatile __typeof__(x) *)&(x))
#define __WRITE_ONCE(x, val)  do { *(volatile __typeof__(x) *)&(x) = (val); } while (0)

// Define the mutex struct.
// Simplified only for test purpose.
struct LOCKABLE Mutex {};

struct Task {
  struct Mutex mu;
};

struct Foo {
  struct Mutex *mu_;
  int  a_value GUARDED_BY(mu_);

  struct Bar {
    struct Mutex *other_mu ACQUIRED_AFTER(mu_); // Note: referencing the parent structure is convenient here, but this should probably be disallowed if the child structure is re-used outside of the parent.
    struct Mutex *third_mu ACQUIRED_BEFORE(other_mu);
  } bar;

  int* a_ptr PT_GUARDED_BY(bar.other_mu);

  struct Task *task;
  int  b_value GUARDED_BY(&task->mu);
  int* b_ptr PT_GUARDED_BY(&task->mu);
};

struct LOCKABLE Lock {};
struct A {
        struct Lock lock;
        union {
                int b __attribute__((guarded_by(lock))); // Note: referencing the parent structure is convenient here, but this should probably be disallowed if the child is re-used outside of the parent.
        };
};

// Declare mutex lock/unlock functions.
int mutex_exclusive_trylock(struct Mutex *mu) EXCLUSIVE_TRYLOCK_FUNCTION(1, mu);
void mutex_exclusive_lock(struct Mutex *mu) EXCLUSIVE_LOCK_FUNCTION(mu);
void mutex_shared_lock(struct Mutex *mu) SHARED_LOCK_FUNCTION(mu);
void mutex_unlock(struct Mutex *mu) UNLOCK_FUNCTION(mu);
void mutex_shared_unlock(struct Mutex *mu) __attribute__((release_shared_capability(mu)));
void mutex_exclusive_unlock(struct Mutex *mu) __attribute__((release_capability(mu)));

// Define global variables.
struct Mutex mu1;
struct Mutex mu2 ACQUIRED_AFTER(mu1);
struct Foo foo_ = {&mu1};
int a_ GUARDED_BY(foo_.mu_);
int *b_ PT_GUARDED_BY(foo_.mu_) = &a_;
int c_ GUARDED_VAR;
int *d_ PT_GUARDED_VAR = &c_;

// Define test functions.
int Foo_fun1(int i) SHARED_LOCKS_REQUIRED(mu2) EXCLUSIVE_LOCKS_REQUIRED(mu1) {
  return i;
}

int Foo_fun2(int i) EXCLUSIVE_LOCKS_REQUIRED(mu2) SHARED_LOCKS_REQUIRED(mu1) {
  return i;
}

int Foo_func3(int i) LOCKS_EXCLUDED(mu1, mu2) {
  return i;
}

static int Bar_fun1(int i) EXCLUSIVE_LOCKS_REQUIRED(mu1) {
  return i;
}

void set_value(int *a, int value) EXCLUSIVE_LOCKS_REQUIRED(foo_.mu_) {
  *a = value;
}

int get_value(int *p) SHARED_LOCKS_REQUIRED(foo_.mu_){
  return *p;
}

void unlock_scope(struct Mutex *const *mu) __attribute__((release_capability(**mu)));
void unlock_scope_type_erased(int **priv) __attribute__((release_capability(*(struct Mutex **)priv)));

// Verify late parsing:
#ifdef LATE_PARSING
struct LateParsing {
  int a_value_defined_before GUARDED_BY(a_mutex_defined_late);
  int *a_ptr_defined_before PT_GUARDED_BY(a_mutex_defined_late);
  struct Mutex *a_mutex_defined_early
    ACQUIRED_BEFORE(a_mutex_defined_late);
  struct Mutex *a_mutex_defined_late
    ACQUIRED_AFTER(a_mutex_defined_very_late);
  struct Mutex *a_mutex_defined_very_late;
} late_parsing;
#endif

int main(void) {

  Foo_fun1(1); // expected-warning{{calling function 'Foo_fun1' requires holding mutex 'mu2'}} \
                  expected-warning{{calling function 'Foo_fun1' requires holding mutex 'mu1' exclusively}}

  mutex_exclusive_lock(&mu1); // expected-note{{mutex acquired here}}
  mutex_shared_lock(&mu2);
  Foo_fun1(1);

  mutex_shared_lock(&mu1); // expected-warning{{acquiring mutex 'mu1' that is already held}} \
                              expected-warning{{mutex 'mu1' must be acquired before 'mu2'}}
  mutex_unlock(&mu1);
  mutex_unlock(&mu2);
  mutex_shared_lock(&mu1);
  mutex_exclusive_lock(&mu2);
  Foo_fun2(2);

  mutex_unlock(&mu2);
  mutex_unlock(&mu1);
  mutex_exclusive_lock(&mu1);
  Bar_fun1(3);
  mutex_unlock(&mu1);

  mutex_exclusive_lock(&mu1);
  Foo_func3(4);  // expected-warning{{cannot call function 'Foo_func3' while mutex 'mu1' is held}}
  mutex_unlock(&mu1);

  Foo_func3(5);

  set_value(&a_, 0); // expected-warning{{calling function 'set_value' requires holding mutex 'foo_.mu_' exclusively}}
                     // expected-warning@-1{{passing pointer to variable 'a_' requires holding mutex 'foo_.mu_'}}
  get_value(b_); // expected-warning{{calling function 'get_value' requires holding mutex 'foo_.mu_'}}
                 // expected-warning@-1{{passing pointer 'b_' requires holding mutex 'foo_.mu_'}}
  mutex_exclusive_lock(foo_.mu_);
  set_value(&a_, 1);
  mutex_unlock(foo_.mu_);
  mutex_shared_lock(foo_.mu_);
  (void)(get_value(b_) == 1);
  mutex_unlock(foo_.mu_);

  a_ = 0; // expected-warning{{writing variable 'a_' requires holding mutex 'foo_.mu_'}}
  __WRITE_ONCE(a_, 0); // expected-warning{{writing variable 'a_' requires holding mutex 'foo_.mu_'}}
  (void)(a_ == 0); // expected-warning{{reading variable 'a_' requires holding mutex 'foo_.mu_'}}
  (void)(__READ_ONCE(a_) == 0); // expected-warning{{reading variable 'a_' requires holding mutex 'foo_.mu_'}}
  *b_ = 0; // expected-warning{{writing the value pointed to by 'b_' requires holding mutex 'foo_.mu_' exclusively}}
  __WRITE_ONCE(*b_, 0); // expected-warning{{writing the value pointed to by 'b_' requires holding mutex 'foo_.mu_' exclusively}}
  (void)(*b_ == 0); // expected-warning{{reading the value pointed to by 'b_' requires holding mutex 'foo_.mu_'}}
  (void)(__READ_ONCE(*b_) == 0); // expected-warning{{reading the value pointed to by 'b_' requires holding mutex 'foo_.mu_'}}
  c_ = 0; // expected-warning{{writing variable 'c_' requires holding any mutex exclusively}}
  (void)(*d_ == 0); // expected-warning{{reading the value pointed to by 'd_' requires holding any mutex}}
  mutex_exclusive_lock(foo_.mu_);
  a_ = 0;
  __WRITE_ONCE(a_, 0);
  (void)(a_ == 0);
  (void)(__READ_ONCE(a_) == 0);
  *b_ = 0;
  __WRITE_ONCE(*b_, 0);
  (void)(*b_ == 0);
  (void)(__READ_ONCE(*b_) == 0);
  c_ = 1;
  (void)(*d_ == 1);
  mutex_unlock(foo_.mu_);

  mutex_exclusive_lock(&mu1);    // expected-note {{mutex acquired here}}
  mutex_shared_unlock(&mu1);     // expected-warning {{releasing mutex 'mu1' using shared access, expected exclusive access}}
                                 // expected-note@-1{{mutex released here}}
  mutex_exclusive_unlock(&mu1);  // expected-warning {{releasing mutex 'mu1' that was not held}}

  mutex_shared_lock(&mu1);      // expected-note {{mutex acquired here}}
  mutex_exclusive_unlock(&mu1); // expected-warning {{releasing mutex 'mu1' using exclusive access, expected shared access}}
                                // expected-note@-1{{mutex released here}}
  mutex_shared_unlock(&mu1);    // expected-warning {{releasing mutex 'mu1' that was not held}}

  /// Cleanup functions
  {
    struct Mutex* const __attribute__((cleanup(unlock_scope))) scope = &mu1;
    mutex_exclusive_lock(scope);  // Lock through scope works.
    // Cleanup happens automatically -> no warning.
  }
  {
    struct Mutex* const __attribute__((unused, cleanup(unlock_scope))) scope = &mu1;
    mutex_exclusive_lock(&mu1);  // With basic alias analysis lock through mu1 also works.
  }
  {
    int i = 0;
    mutex_exclusive_lock(&mu1);
    struct Mutex* const __attribute__((unused, cleanup(unlock_scope))) scope = &mu1;
    i++;
  }
  // Cleanup through cast alias pointer in a for-loop; a variant of this pattern
  // appears in the Linux kernel for generic scoped guard macros.
  for (int i = (mutex_exclusive_lock(foo_.mu_), 0),
       *priv __attribute__((cleanup(unlock_scope_type_erased))) = (int *)(__UINTPTR_TYPE__)(foo_.mu_);
       !i; i++) {
    a_ = 42;
  }

  foo_.a_value = 0; // expected-warning {{writing variable 'a_value' requires holding mutex 'foo_.mu_' exclusively}}
  *foo_.a_ptr = 1; // expected-warning {{writing the value pointed to by 'a_ptr' requires holding mutex 'foo_.bar.other_mu' exclusively}}
  foo_.b_value = 0; // expected-warning {{writing variable 'b_value' requires holding mutex 'foo_.task->mu' exclusively}}
  *foo_.b_ptr = 1; // expected-warning {{writing the value pointed to by 'b_ptr' requires holding mutex 'foo_.task->mu' exclusively}}

  mutex_exclusive_lock(foo_.bar.other_mu);
  *foo_.a_ptr = 1;
  mutex_exclusive_lock(foo_.bar.third_mu); // expected-warning{{mutex 'third_mu' must be acquired before 'other_mu'}}
  mutex_exclusive_lock(foo_.mu_); // expected-warning{{mutex 'mu_' must be acquired before 'other_mu'}}
  mutex_exclusive_unlock(foo_.mu_);
  mutex_exclusive_unlock(foo_.bar.other_mu);
  mutex_exclusive_unlock(foo_.bar.third_mu);

  mutex_exclusive_lock(&foo_.task->mu);
  foo_.b_value = 0;
  *foo_.b_ptr = 1;
  mutex_exclusive_unlock(&foo_.task->mu);

#ifdef LATE_PARSING
  late_parsing.a_value_defined_before = 1; // expected-warning{{writing variable 'a_value_defined_before' requires holding mutex 'late_parsing.a_mutex_defined_late' exclusively}}
  late_parsing.a_ptr_defined_before = 0;
  set_value(&late_parsing.a_value_defined_before, 0); // expected-warning{{calling function 'set_value' requires holding mutex 'foo_.mu_' exclusively}}
                                                      // expected-warning@-1{{passing pointer to variable 'a_value_defined_before' requires holding mutex 'late_parsing.a_mutex_defined_late'}}
  mutex_exclusive_lock(late_parsing.a_mutex_defined_late);
  mutex_exclusive_lock(late_parsing.a_mutex_defined_early); // expected-warning{{mutex 'a_mutex_defined_early' must be acquired before 'a_mutex_defined_late'}}
  mutex_exclusive_unlock(late_parsing.a_mutex_defined_early);
  mutex_exclusive_unlock(late_parsing.a_mutex_defined_late);
  mutex_exclusive_lock(late_parsing.a_mutex_defined_late);
  mutex_exclusive_lock(late_parsing.a_mutex_defined_very_late); // expected-warning{{mutex 'a_mutex_defined_very_late' must be acquired before 'a_mutex_defined_late'}}
  mutex_exclusive_unlock(late_parsing.a_mutex_defined_very_late);
  mutex_exclusive_unlock(late_parsing.a_mutex_defined_late);
#endif

  return 0;
}

/*** Reentrancy test ***/
struct LOCKABLE REENTRANT_CAPABILITY ReentrantMutex {};
void reentrant_mutex_lock(struct ReentrantMutex *mu) EXCLUSIVE_LOCK_FUNCTION(mu);
void reentrant_mutex_unlock(struct ReentrantMutex *mu) UNLOCK_FUNCTION(mu);

struct ReentrantMutex rmu;
int r_ GUARDED_BY(&rmu);

void test_reentrant(void) {
  reentrant_mutex_lock(&rmu);
  r_ = 1;
  reentrant_mutex_lock(&rmu);
  r_ = 1;
  reentrant_mutex_unlock(&rmu);
  r_ = 1;
  reentrant_mutex_unlock(&rmu);
  r_ = 1; // expected-warning{{writing variable 'r_' requires holding mutex 'rmu' exclusively}}
}

// In C code, object construction may want to initialize guarded members
// alongside a capability (initialization implies exclusive access); to do so,
// we can assert a capability as part of its initialization. To permit immediate
// use of the capability, it is necessarily to "promote" the type to a reentrant
// capability for the rest of the scope. While this avoids the false positive
// warning on member initialization and immediate use, it does pose the danger
// of false negatives (no warning on actual double-lock in the same function).
void mutex_init(struct Mutex *mu) ASSERT_EXCLUSIVE_LOCK((struct ReentrantMutex *)mu);

struct TestInit {
  struct Mutex mu;
  int a GUARDED_BY(&mu);
};

struct TestInit test_init(void) {
  struct TestInit foo;

  mutex_init(&foo.mu); // initialize capability before guarded members
  foo.a = 0;           // initialize guarded members normally

  // It should be allowed to immediately use the capability in the same
  // function, such as after spawning a thread.
  mutex_exclusive_lock(&foo.mu);
  mutex_exclusive_unlock(&foo.mu);

  return foo;
}

// Function pointer struct members.
struct FPOps {
  struct Mutex mu;
  int a GUARDED_BY(&mu);
  void (*lock)(void) EXCLUSIVE_LOCK_FUNCTION(&mu);
  void (*unlock)(void) UNLOCK_FUNCTION(&mu);
  void (*requires_mu)(void) EXCLUSIVE_LOCKS_REQUIRED(&mu);
};

void test_fp_ops(struct FPOps *ops) {
  ops->lock();
  ops->a = 42;
  ops->requires_mu();
  ops->unlock();
}

void test_fp_ops_fail(struct FPOps *ops) {
  ops->a = 42; // expected-warning {{writing variable 'a' requires holding mutex '&FPOps::mu' exclusively}}
  ops->requires_mu(); // expected-warning {{calling function 'requires_mu' requires holding mutex '&FPOps::mu' exclusively}}
}

// An attribute on a member of an anonymous struct/union may name a field of
// the enclosing record, and vice versa.
struct AnonMembers {
  struct Mutex mu;
  union {
    int a GUARDED_BY(mu);
  };
  struct {
    struct Mutex inner;
    int c GUARDED_BY(inner);
    struct Also {
      int az GUARDED_BY(inner);
    } al;
  };
  int e GUARDED_BY(inner);
  struct {
    struct {
      struct Mutex deep;
      int f GUARDED_BY(mu);
    };
    int g GUARDED_BY(deep);
  };
  int h GUARDED_BY(deep);
  union { struct Mutex um; };
  union { int i GUARDED_BY(um); };
  int j GUARDED_BY(&um); // the wildcard, any object's um
  struct Mutex after ACQUIRED_AFTER(inner);
};

void test_anon_members(struct AnonMembers *s, struct AnonMembers *other) {
  mutex_exclusive_lock(&s->mu);
  s->a = 1;
  s->f = 6;
  mutex_unlock(&s->mu);
  mutex_exclusive_lock(&s->inner);
  s->c = 3;
  s->e = 5;
  s->al.az = 10;
  mutex_unlock(&s->inner);
  mutex_exclusive_lock(&s->deep);
  s->g = 7;
  s->h = 8;
  mutex_unlock(&s->deep);
  mutex_exclusive_lock(&s->um);
  s->i = 9;
  s->j = 10;
  mutex_unlock(&s->um);
  mutex_exclusive_lock(&other->um);
  s->j = 10;
  mutex_unlock(&other->um);
  mutex_exclusive_lock(&other->mu);
  s->j = 10; // expected-warning {{writing variable 'j' requires holding mutex '&AnonMembers::um' exclusively}}
  s->a = 1; // expected-warning {{writing variable 'a' requires holding mutex 's->mu' exclusively}} \
            // expected-note {{found near match 'other->mu'}}
  s->e = 5; // expected-warning {{writing variable 'e' requires holding mutex 's->inner' exclusively}}
  s->al.az = 10; // expected-warning {{writing variable 'az' requires holding mutex 's->inner' exclusively}}
  s->f = 6; // expected-warning {{writing variable 'f' requires holding mutex 's->mu' exclusively}} \
            // expected-note {{found near match 'other->mu'}}
  s->g = 7; // expected-warning {{writing variable 'g' requires holding mutex 's->deep' exclusively}}
  s->h = 8; // expected-warning {{writing variable 'h' requires holding mutex 's->deep' exclusively}}
  s->i = 9; // expected-warning {{writing variable 'i' requires holding mutex 's->um' exclusively}}
  mutex_unlock(&other->mu);
}

void test_anon_members_value(struct AnonMembers s) {
  mutex_exclusive_lock(&s.deep);
  s.g = 7;
  s.h = 8;
  mutex_unlock(&s.deep);
  s.h = 8; // expected-warning {{writing variable 'h' requires holding mutex 's.deep' exclusively}}
}

void test_anon_members_order(struct AnonMembers *s) {
  mutex_exclusive_lock(&s->after);
  mutex_exclusive_lock(&s->inner); // expected-warning {{mutex 'inner' must be acquired before 'after'}}
  mutex_unlock(&s->inner);
  mutex_unlock(&s->after);
}

// A field of a named nested record may be guarded by a field of an enclosing
// record, resolved on the nearest enclosing object, and vice versa.
struct NamedNesting {
  struct Mutex mu;
  union { struct Mutex amu; };
  struct Named {
    struct Mutex nmu;
    int nx GUARDED_BY(nmu);
    int ny GUARDED_BY(mu);
    int nv GUARDED_BY(amu);
    struct NamedIn {
      int nix GUARDED_BY(nmu);
    } nin;
  } n, narr[2], *np, *pa[2];
  struct {
    struct Inner {
      struct Mutex imu;
      int w GUARDED_BY(mu);
    } in;
  };
  int y GUARDED_BY(n.nmu);
  int z GUARDED_BY(in.imu);
};

void test_named_nesting(struct NamedNesting *m, struct NamedNesting *o) {
  mutex_exclusive_lock(&m->mu);
  m->n.ny = 1;
  m->in.w = 2;
  m->narr[1].ny = 3;
  m->narr->ny = 3;
  (&m->n)->ny = 5;
  m->np->ny = 4; // expected-warning {{writing variable 'ny' requires holding mutex 'm->np->NamedNesting::mu' exclusively}} \
                 // expected-note {{found near match 'm->mu'}}
  mutex_unlock(&m->mu);
  mutex_exclusive_lock(&o->mu);
  m->n.ny = 1; // expected-warning {{writing variable 'ny' requires holding mutex 'm->mu' exclusively}} \
               // expected-note {{found near match 'o->mu'}}
  m->in.w = 2; // expected-warning {{writing variable 'w' requires holding mutex 'm->mu' exclusively}} \
               // expected-note {{found near match 'o->mu'}}
  mutex_unlock(&o->mu);
  mutex_exclusive_lock(&m->n.nmu);
  mutex_exclusive_lock(&m->in.imu);
  m->y = 1;
  m->z = 2;
  o->y = 1; // expected-warning {{writing variable 'y' requires holding mutex 'o->n.nmu' exclusively}} \
            // expected-note {{found near match 'm->n.nmu'}}
  o->z = 2; // expected-warning {{writing variable 'z' requires holding mutex 'o->in.imu' exclusively}} \
            // expected-note {{found near match 'm->in.imu'}}
  mutex_unlock(&m->in.imu);
  mutex_unlock(&m->n.nmu);
}

// An array of records accessed through its decayed pointer is still an object
// of its element type, whose own field may be named.
void test_named_nesting_array(struct NamedNesting *m, struct Named narr[2]) {
  mutex_exclusive_lock(&m->narr->nmu);
  m->narr->nx = 1;
  m->narr->nin.nix = 2;
  m->narr[1].nx = 3; // expected-warning {{writing variable 'nx' requires holding mutex 'm->narr[1].nmu' exclusively}} \
                     // expected-note {{found near match 'm->narr->nmu'}}
  mutex_unlock(&m->narr->nmu);
  m->narr->nx = 1; // expected-warning {{writing variable 'nx' requires holding mutex 'm->narr->nmu' exclusively}}
  m->narr->nin.nix = 2; // expected-warning {{writing variable 'nix' requires holding mutex 'm->narr->nmu' exclusively}}
  mutex_exclusive_lock(&narr->nmu);
  narr->nx = 1;
  narr->nin.nix = 2;
  mutex_unlock(&narr->nmu);
  // Pointer arithmetic is spelled as written, and is not a subscript.
  mutex_exclusive_lock(&(m->narr + 1)->nmu);
  (m->narr + 1)->nx = 1;
  m->narr[1].nx = 3; // expected-warning {{writing variable 'nx' requires holding mutex 'm->narr[1].nmu' exclusively}} \
                     // expected-note {{found near match '(m->narr + 1)->nmu'}}
  mutex_unlock(&(m->narr + 1)->nmu);
  (m->np + 1)->nx = 1; // expected-warning {{writing variable 'nx' requires holding mutex '(m->np + 1)->nmu' exclusively}}
  // An element of an array of pointers is a pointer.
  mutex_exclusive_lock(&m->pa[1]->nmu);
  m->pa[1]->nx = 1;
  m->pa[0]->nx = 1; // expected-warning {{writing variable 'nx' requires holding mutex 'm->pa[0]->nmu' exclusively}} \
                    // expected-note {{found near match 'm->pa[1]->nmu'}}
  mutex_unlock(&m->pa[1]->nmu);
}

// With only the nested object at hand, its enclosing record's field cannot be
// reached; the requirement is spelled with the field's record.
void test_unreachable(struct NamedNesting *o, struct Named *inner) {
  mutex_exclusive_lock(&o->mu);
  mutex_exclusive_lock(&o->amu);
  o->n.nv = 1;
  inner->ny = 1; // expected-warning {{writing variable 'ny' requires holding mutex 'inner->NamedNesting::mu' exclusively}} \
                 // expected-note {{found near match 'o->mu'}}
  inner->nv = 2; // expected-warning {{writing variable 'nv' requires holding mutex 'inner->NamedNesting::amu' exclusively}} \
                 // expected-note {{found near match 'o->amu'}}
  mutex_unlock(&o->amu);
  mutex_unlock(&o->mu);
}

// An unqualified name is the innermost record's field.
struct Shadowed {
  struct Mutex mu;
  struct Shadowing {
    struct Mutex mu;
    int ny GUARDED_BY(mu);
    struct Deeper {
      int dz GUARDED_BY(mu);
    } d;
  } n;
};

void test_shadowed(struct Shadowed *o) {
  mutex_exclusive_lock(&o->mu);
  o->n.ny = 1;   // expected-warning {{writing variable 'ny' requires holding mutex 'o->n.mu' exclusively}}
  o->n.d.dz = 1; // expected-warning {{writing variable 'dz' requires holding mutex 'o->n.mu' exclusively}}
  mutex_unlock(&o->mu);
  mutex_exclusive_lock(&o->n.mu);
  o->n.ny = 2;
  o->n.d.dz = 2;
  mutex_unlock(&o->n.mu);
}

// Function pointer parameters. The attributes constrain the function reached
// through the pointer, so they are checked where the pointer is called, and
// must not be mistaken for requirements of the enclosing function's callers
// (nor for scoped-lockable parameter annotations). SemaCXX's
// warn-thread-safety-analysis.cpp covers the C++ spellings of this.
typedef void (*visit_fn)(int);

void visit_cb(int x) EXCLUSIVE_LOCKS_REQUIRED(mu1);
void visit_all(visit_fn visit EXCLUSIVE_LOCKS_REQUIRED(mu1), int n);
void visit_all_locked_fp(visit_fn visit EXCLUSIVE_LOCKS_REQUIRED(mu1), int n)
    EXCLUSIVE_LOCKS_REQUIRED(mu1) {
  visit(n);
}
void visit_all_unlocked_fp(visit_fn visit EXCLUSIVE_LOCKS_REQUIRED(mu1), int n) {
  visit(n); // expected-warning {{calling function 'visit' requires holding mutex 'mu1' exclusively}}
}

// Passing an annotated callee is not itself a use of the capability, so these
// calls do not require mu1 to be held here.
void test_fp_param(int n) {
  visit_all(visit_cb, n);
  visit_all(&visit_cb, n);
  visit_all_unlocked_fp(visit_cb, n);
  // Only visit_all_locked_fp's own attribute requires mu1.
  visit_all_locked_fp(visit_cb, n); // expected-warning {{calling function 'visit_all_locked_fp' requires holding mutex 'mu1' exclusively}}
}

// Acquire/release on a function pointer parameter likewise describe the pointee,
// so calling the enclosing function neither acquires nor releases mu1.
void call_locker(void (*lock)(void) EXCLUSIVE_LOCK_FUNCTION(mu1));
void test_fp_param_acquire(void) {
  call_locker(0);
  mutex_exclusive_lock(&mu1);
  mutex_exclusive_unlock(&mu1);
}

// Function pointer attributes referring to parameters.
struct BDev {
  struct Mutex lock;
  int a GUARDED_BY(&lock);
};

struct BDevOps {
  void (*lock)(struct BDev *bdev) EXCLUSIVE_LOCK_FUNCTION(bdev->lock);
  void (*unlock)(struct BDev *bdev) UNLOCK_FUNCTION(bdev->lock);
};

void test_bdev_ops(struct BDevOps *ops, struct BDev *bdev) {
  ops->lock(bdev);
  bdev->a = 42;
  ops->unlock(bdev);
}

void test_bdev_ops_fail(struct BDevOps *ops, struct BDev *bdev) {
  ops->unlock(bdev); // expected-warning {{releasing mutex 'bdev->lock' that was not held}}
}

// lock_returned on a function pointer, naming the pointee's parameter.
struct Mutex *(*bdev_lock_of)(struct BDev *bdev) LOCK_RETURNED(&bdev->lock);
struct BDevLockOps {
  struct Mutex *(*lock_of)(struct BDev *bdev) LOCK_RETURNED(&bdev->lock);
};

void test_bdev_lock_of(struct BDevLockOps *ops, struct BDev *bdev) {
  mutex_exclusive_lock(bdev_lock_of(bdev));
  bdev->a = 42;
  mutex_exclusive_unlock(ops->lock_of(bdev));
  mutex_exclusive_lock(ops->lock_of(bdev));
  mutex_exclusive_unlock(&bdev->lock);
}

void test_bdev_lock_of_fail(struct BDevLockOps *ops, struct BDev *bdev) {
  mutex_exclusive_lock(&mu1);
  mutex_exclusive_unlock(ops->lock_of(bdev)); // expected-warning {{releasing mutex 'bdev->lock' that was not held}}
  mutex_exclusive_unlock(&mu1);
}

void test_lock_of_param(struct BDev *bdev,
                        struct Mutex *(*lock_of)(struct BDev *) LOCK_RETURNED(&bdev->lock)) {
  mutex_exclusive_lock(lock_of(bdev));
  bdev->a = 42;
  mutex_exclusive_unlock(&bdev->lock);
}

// A function pointer field may name a sibling member, which is resolved
// against the object the field was reached through.
struct BDevSelf {
  struct Mutex lock;
  int a GUARDED_BY(lock);
  struct Mutex *(*lock_of)(void) LOCK_RETURNED(lock);
  void (*unlock)(void) UNLOCK_FUNCTION(lock);
};

void test_bdev_self(struct BDevSelf *bdev) {
  mutex_exclusive_lock(bdev->lock_of());
  bdev->a = 42;
  bdev->unlock();
}

void test_bdev_self_fail(struct BDevSelf *bdev, struct BDevSelf *other) {
  mutex_exclusive_lock(other->lock_of());
  bdev->a = 42; // expected-warning {{writing variable 'a' requires holding mutex 'bdev->lock' exclusively}} \
                // expected-note {{found near match 'other->lock'}}
  mutex_exclusive_unlock(bdev->lock_of()); // expected-warning {{releasing mutex 'bdev->lock' that was not held}}
  other->unlock();
}

// The field may also be called through an explicit dereference.
void test_bdev_self_deref(struct BDevSelf *bdev, struct BDevSelf *other) {
  mutex_exclusive_lock((*bdev->lock_of)());
  bdev->a = 42;
  (*bdev->unlock)();
  mutex_exclusive_lock((**other->lock_of)());
  other->a = 42;
  bdev->a = 42; // expected-warning {{writing variable 'a' requires holding mutex 'bdev->lock' exclusively}} \
                // expected-note {{found near match 'other->lock'}}
  mutex_exclusive_unlock((*other->lock_of)());
}

// A pointee parameter shadows a member of the same name, in both modes: the
// release is of the argument, not of 'ops->mu'.
struct ShadowOps {
  void (*unlock)(struct Mutex *mu) UNLOCK_FUNCTION(mu);
  struct Mutex mu;
};

void test_shadow_ops(struct ShadowOps *ops, struct Mutex *m) {
  ops->unlock(m); // expected-warning {{releasing mutex 'm' that was not held}}
}

// Likewise a later parameter of the same name: 'release' releases its own
// argument, leaving the enclosing function's 'mu' held.
void shadow_param(void (*release)(struct Mutex *mu) UNLOCK_FUNCTION(mu),
                  struct Mutex *mu) EXCLUSIVE_LOCKS_REQUIRED(mu) {
  release(&mu1); // expected-warning {{releasing mutex 'mu1' that was not held}}
}

// guarded_by describes the pointer itself, not a call through it, so a pointee
// parameter of the same name does not shadow the member: reading 'cb' is
// guarded by 'ops->mu', in both modes.
struct GuardedOps {
  struct Mutex mu;
  void (*cb)(struct Mutex *mu) GUARDED_BY(mu);
};

void test_guarded_ops(struct GuardedOps *ops, struct Mutex *m) {
  ops->cb(m); // expected-warning {{reading variable 'cb' requires holding mutex 'ops->mu'}}
  mutex_exclusive_lock(&ops->mu);
  ops->cb(m);
  mutex_exclusive_unlock(&ops->mu);
}

#ifdef LATE_PARSING
// Likewise when the member is declared after the field.
struct GuardedOpsLater {
  void (*cb)(struct Mutex *mu) GUARDED_BY(mu);
  struct Mutex mu;
};

void test_guarded_ops_later(struct GuardedOpsLater *ops, struct Mutex *m) {
  ops->cb(m); // expected-warning {{reading variable 'cb' requires holding mutex 'ops->mu'}}
  mutex_exclusive_lock(&ops->mu);
  ops->cb(m);
  mutex_exclusive_unlock(&ops->mu);
}
#endif

#ifdef LATE_PARSING
// A requirement on a parameter may name another parameter declared later. The
// deferred attribute has to end up on the parameter it was written on and stay
// live, so check that the call through it is really honored rather than merely
// accepted: the release consumes the lock, making the second one unheld.
void late_param_cb(void (*release)(struct Mutex *) UNLOCK_FUNCTION(mu),
                   struct Mutex *mu) EXCLUSIVE_LOCKS_REQUIRED(mu) { // expected-note {{mutex acquired here}}
  release(mu); // expected-note {{mutex released here}}
  mutex_exclusive_unlock(mu); // expected-warning {{releasing mutex 'mu' that was not held}}
} // expected-warning {{expecting mutex 'mu' to be held at the end of function}}

// It names 'mu', not the neighbouring parameter: only 'mu' is consumed.
void late_param_other(void (*release)(struct Mutex *) UNLOCK_FUNCTION(mu),
                      struct Mutex *other, struct Mutex *mu)
    EXCLUSIVE_LOCKS_REQUIRED(mu, other) { // expected-note {{mutex acquired here}}
  release(mu);
} // expected-warning {{expecting mutex 'mu' to be held at the end of function}}
#endif

// Test unusual trylock patterns
void do_some_work(void);
int work_data GUARDED_BY(mu1);

void test_trylock_conditional(void) {
  if (({ int do_work = !!(!mutex_exclusive_trylock(&mu1));
         if (__builtin_expect(do_work, 0))
           do_some_work();
         __builtin_expect(do_work, 0); }))
    return;
  work_data = 1;
  mutex_unlock(&mu1);
}

// How glibc before 2.32 spells assert(): a void conditional operator whose
// false arm does not return. There is no result to branch on later, so the
// try-lock is acquired on the branch itself.
void assert_fail(void) __attribute__((noreturn));
#define assert_trylock(e) ((e) ? (void)0 : assert_fail())

void test_trylock_void_conditional(void) {
  assert_trylock(mutex_exclusive_trylock(&mu1));
  work_data = 1;
  mutex_unlock(&mu1);
}

void test_trylock_void_conditional_via_var(void) {
  int got = mutex_exclusive_trylock(&mu1);
  assert_trylock(got);
  work_data = 1;
  mutex_unlock(&mu1);
}

int mutex_trylock_errno(struct Mutex *mu)
    __attribute__((try_acquire_capability_range(0, __INT_MAX__, mu)));
int mutex_shared_trylock_errno(struct Mutex *mu)
    __attribute__((try_acquire_shared_capability_range(0, __INT_MAX__, mu)));
int mutex_trylock_zero(struct Mutex *mu)
    __attribute__((try_acquire_capability_range(0, 0, mu)));
int mutex_trylock_1_to_10(struct Mutex *mu)
    __attribute__((try_acquire_capability_range(1, 10, mu)));

struct Task *next_task(void);

// Incrementing or decrementing a local variable must keep BuildLockset's
// LocalVariableMap context synchronized for subsequent local aliases.
void test_incdec_preserves_local_var_ctx(int count) {
  int local = count;
  local--;
  --local;
  ++local;
  {
    mutex_exclusive_lock(&mu1);
    struct Mutex *guard __attribute__((cleanup(unlock_scope))) = &mu1;
    (void)guard;
    work_data = 1;
  }

  int n = 0;
  struct Task *t;
  while (n < count) {
    n++;
    t = next_task();
    mutex_exclusive_lock(&t->mu);
    if (n == 1)
      do_some_work();
    mutex_unlock(&t->mu);
  }
}

void test_trylock_range_c(void) {
  int err;
  if ((err = mutex_trylock_errno(&mu1)) < 0)
    return;
  work_data = 1;
  mutex_unlock(&mu1);

  if (__builtin_expect(mutex_trylock_zero(&mu1) != 0, 0))
    return;
  work_data = 2;
  mutex_unlock(&mu1);

  if (!mutex_trylock_zero(&mu1)) {
    work_data = 3;
    mutex_unlock(&mu1);
  }

  if (mutex_shared_trylock_errno(&mu1) >= 0) {
    int v = work_data;
    (void)v;
    work_data = 4; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1);
  }

  switch (mutex_trylock_1_to_10(&mu1)) {
  case 1 ... 10:
    work_data = 5;
    mutex_unlock(&mu1);
    break;
  default:
    work_data = 6; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    break;
  }

  // Signed-to-unsigned conversion wraps negative values to positive, so >= 0U
  // is tautologically true and must not acquire the capability.
  if (mutex_trylock_errno(&mu1) >= 0U) {
    work_data = 7; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }

  // Narrowing conversion may truncate non-zero failure codes to 0.
  signed char narrow = mutex_trylock_zero(&mu1);
  if (narrow == 0) {
    work_data = 8; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }

  // Bit-field assignments truncate the stored value.
  struct { int bf : 2; } s;
  if ((s.bf = mutex_trylock_zero(&mu1)) == 0) {
    work_data = 9; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
}

// Trivial inline helpers (IS_ERR, PTR_ERR, PTR_ERR_OR_ZERO).
void trace_branch_hit(int val);
#define TEST_UNLIKELY_STMTEXPR(x)                                              \
  ({                                                                           \
    long __r = __builtin_expect(!!(x), 0);                                     \
    trace_branch_hit((int)__r);                                                \
    __r;                                                                       \
  })

static inline _Bool c_is_err_value(__UINTPTR_TYPE__ x) {
  return TEST_UNLIKELY_STMTEXPR(x >= (__UINTPTR_TYPE__)-4095);
}

static inline _Bool c_is_err(const void *ptr) {
  return c_is_err_value((__UINTPTR_TYPE__)(void *)((__UINTPTR_TYPE__)ptr));
}

static inline __INTPTR_TYPE__ c_ptr_err(const void *ptr) {
  return (__INTPTR_TYPE__)ptr;
}

static inline int c_ptr_err_or_zero(const void *ptr) {
  if (c_is_err(ptr))
    return c_ptr_err(ptr);
  else
    return 0;
}

// Branch conditions that call inline helpers with arguments that are
// unrelated to the tracked values must not use up the inline expansion
// budget of the analyzed function (MaxInlineExpansions).
static inline int c_unrelated_helper(int v) { return v + 1; }
int c_unrelated_data;
#define C_REP4(x) x x x x
#define C_REP16(x) C_REP4(C_REP4(x))
#define C_REP256(x) C_REP16(C_REP16(x))
#define C_REP1024(x) C_REP4(C_REP256(x))

// Pointer return types on try_acquire_[shared_]capability_range.
#define TEST_IS_ERR_VALUE_MACRO(x)                                             \
  __builtin_expect(                                                            \
      !!((__UINTPTR_TYPE__)(void *)(x) >= (__UINTPTR_TYPE__)-4095), 0)

struct CGroupObj {
  int id;
};

struct CGroupObj *c_ptr_range_lock_live(int ok)
    __attribute__((try_acquire_capability_range(0, (__UINTPTR_TYPE__)-4096, mu1)));

struct CGroupObj *c_ptr_range_shared_nonnull(int mode)
    __attribute__((try_acquire_shared_capability_range(1, (__UINTPTR_TYPE__)-4096, mu1)));

void *c_ptr_range_map_or_failed(void)
    __attribute__((try_acquire_capability_range(0, (__UINTPTR_TYPE__)-2, mu1)));

void test_ptr_range_callers_c(int ok, int mode) {
  struct CGroupObj *cgrp = c_ptr_range_lock_live(ok);
  if (TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)cgrp))
    return;
  work_data = 1;
  mutex_unlock(&mu1);

  if (!TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)c_ptr_range_lock_live(ok))) {
    work_data = 2;
    mutex_unlock(&mu1);
  }

  // Range [1, -4096]: both NULL and ERR_PTR indicate failure.
  struct CGroupObj *sc = c_ptr_range_shared_nonnull(mode);
  if (sc && !TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)sc)) {
    int v = work_data;
    (void)v;
    mutex_unlock(&mu1);
  }

  // Missing NULL check when 0 is outside [1, -4096].
  struct CGroupObj *sc2 = c_ptr_range_shared_nonnull(mode);
  if (!TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)sc2)) {
    int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
    (void)v;
  }

  // MAP_FAILED ((void *)-1) sentinel comparison.
  void *mapped = c_ptr_range_map_or_failed();
  if (mapped != (void *)(__INTPTR_TYPE__)-1) {
    work_data = 3;
    mutex_unlock(&mu1);
  }

  // Switch on uintptr_t cast of pointer range trylock.
  switch ((__UINTPTR_TYPE__)c_ptr_range_lock_live(ok)) {
  case (__UINTPTR_TYPE__)-4095 ... (__UINTPTR_TYPE__)-1:
    work_data = 4; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    break;
  default:
    work_data = 5;
    mutex_unlock(&mu1);
    break;
  }
}

// Inline helper expansion (IS_ERR, IS_ERR_OR_NULL, PTR_ERR, PTR_ERR_OR_ZERO,
// ERR_CAST) in caller-side range trylock conditions.
static inline _Bool c_is_err_or_null(const void *ptr) {
  return TEST_UNLIKELY_STMTEXPR(!ptr) ||
         c_is_err_value((__UINTPTR_TYPE__)ptr);
}

static inline void *c_err_cast(const void *ptr) {
  return (void *)ptr;
}

static inline int c_is_err_int(const void *ptr) {
  return (__UINTPTR_TYPE__)ptr >= (__UINTPTR_TYPE__)-4095;
}

static inline _Bool c_recursive_ptr_helper(const void *ptr) {
  if (c_recursive_ptr_helper(ptr))
    return 1;
  return c_recursive_ptr_helper(ptr);
}

_Bool c_opaque_is_err(const void *ptr);

void test_inline_helper_range_callers_c(int ok, int mode) {
  // Direct call passed to IS_ERR() (matches Linux debug_populate()).
  if (c_is_err(c_ptr_range_lock_live(ok)))
    return;
  work_data = 10;
  mutex_unlock(&mu1);

  // Local variable passed to IS_ERR() (matches Linux cgroup_masks_read()).
  struct CGroupObj *cgrp = c_ptr_range_lock_live(ok);
  if (!c_is_err(cgrp)) {
    work_data = 11;
    mutex_unlock(&mu1);
  }

  // Wrong branch of IS_ERR() must warn.
  struct CGroupObj *cgrp_bad = c_ptr_range_lock_live(ok);
  if (c_is_err(cgrp_bad)) {
    work_data = 12; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  } else {
    mutex_unlock(&mu1);
  }

  // IS_ERR_OR_NULL() on [1, -4096].
  struct CGroupObj *sc = c_ptr_range_shared_nonnull(mode);
  if (!c_is_err_or_null(sc)) {
    int v = work_data;
    (void)v;
    mutex_unlock(&mu1);
  }

  // IS_ERR() alone is insufficient when NULL (0) is outside [1, -4096].
  struct CGroupObj *sc_bad = c_ptr_range_shared_nonnull(mode);
  if (!c_is_err(sc_bad)) {
    int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
    (void)v;
  }

  // ERR_CAST() identity wrapper in both direct and local-variable forms.
  if (!c_is_err(c_err_cast(c_ptr_range_lock_live(ok)))) {
    work_data = 13;
    mutex_unlock(&mu1);
  }
  void *ec = c_err_cast(c_ptr_range_lock_live(ok));
  if (!c_is_err(ec)) {
    work_data = 14;
    mutex_unlock(&mu1);
  }

  // PTR_ERR_OR_ZERO() in boolean and comparison contexts, including SSA
  // tracking when the pointer variable is reassigned before the branch.
  if (!c_ptr_err_or_zero(c_ptr_range_lock_live(ok))) {
    work_data = 15;
    mutex_unlock(&mu1);
  }
  struct CGroupObj *reassigned = c_ptr_range_lock_live(ok);
  int err = c_ptr_err_or_zero(reassigned);
  reassigned = 0;
  if (err == 0) {
    work_data = 16;
    mutex_unlock(&mu1);
  }
  if (c_ptr_err_or_zero(c_ptr_range_lock_live(ok)) >= 0) {
    work_data = 17;
    mutex_unlock(&mu1);
  }

  // PTR_ERR() signed intptr_t comparison and int-returning predicate == 0.
  __INTPTR_TYPE__ pe = c_ptr_err(c_ptr_range_lock_live(ok));
  if (!(pe >= -4095 && pe < 0)) {
    work_data = 18;
    mutex_unlock(&mu1);
  }
  if (c_is_err_int(c_ptr_range_lock_live(ok)) == 0) {
    work_data = 19;
    mutex_unlock(&mu1);
  }

  // Opaque and recursive helpers must not falsely acquire the capability.
  if (!c_opaque_is_err(c_ptr_range_lock_live(ok))) {
    work_data = 20; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  if (!c_recursive_ptr_helper(c_ptr_range_lock_live(ok))) {
    work_data = 21; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
}

// A null check followed by a separate IS_ERR() check decides the result of a
// call that returns NULL or an error pointer on failure.
void test_split_null_and_err_checks_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  if (c_is_err(p))
    return;
  int v = work_data;
  (void)v;
  mutex_unlock(&mu1);
}

void test_split_err_and_null_checks_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (c_is_err(p))
    return;
  if (!p)
    return;
  int v = work_data;
  (void)v;
  mutex_unlock(&mu1);
}

// The null check alone does not decide the result.
void test_split_null_check_only_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
  (void)v;
}

// Each iteration executes the call again.
void test_split_checks_in_loop_c(int mode, int n) {
  for (int i = 0; i < n; i++) {
    struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
    if (!p)
      continue;
    if (c_is_err(p))
      continue;
    int v = work_data;
    (void)v;
    mutex_unlock(&mu1);
  }
}

void test_split_checks_irreducible_bypass_c(int mode, int check_null) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!check_null) {
    goto Z;
  } else {
    if (!p)
      return;
  }
Y:
  if (c_is_err(p)) {
Z:
    if (mode)
      goto Y;
    return;
  }
  int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
  (void)v;
  mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
}

void test_split_checks_diamond_rebranch_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  if (!c_is_err(p))
    do_some_work();
  if (!c_is_err(p)) {
    int v = work_data;
    (void)v;
    mutex_unlock(&mu1);
  }
}

void test_split_checks_unlock_then_rebranch_bad_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  if (!c_is_err(p))
    mutex_unlock(&mu1);
  if (!c_is_err(p))
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
}

int c_trylock_two_ranges(struct Mutex *m1, struct Mutex *m2)
    __attribute__((try_acquire_capability_range(1, 2, *m1)))
    __attribute__((try_acquire_capability_range(2, 2, *m2)));

void test_split_checks_multi_attr_c(void) {
  int r = c_trylock_two_ranges(&mu1, &mu2);
  if (r < 1 || r > 2)
    return;
  if (r < 2) {
    mutex_unlock(&mu1);
    return;
  }
  work_data = 1;
  mutex_unlock(&mu2);
  mutex_unlock(&mu1);
}

int c_trylock_only_three(void)
    __attribute__((try_acquire_capability_range(3, 3, mu1)));

void test_split_checks_stacked_switch_cases_c(void) {
  int r = c_trylock_only_three();
  switch (r) {
  case 1:
  case 2 ... 3:
    if (r != 3)
      return;
    work_data = 1;
    mutex_unlock(&mu1);
    break;
  default:
    break;
  }
}

int c_multi_range_same_cap(void)
    __attribute__((try_acquire_capability_range(1, 2, mu1)))
    __attribute__((try_acquire_capability_range(4, 5, mu1)));

void test_multi_range_same_cap_caller_c(void) {
  int r = c_multi_range_same_cap();
  if (r < 1)
    return;
  if (r == 3)
    return;
  if (r > 5)
    return;
  work_data = 1;
  mutex_unlock(&mu1);
}

// A contradictory branch on a previously narrowed trylock variable must not
// overwrite the variable's pending range on the reachable branch, nor falsely
// acquire the capability on the dead branch.
void test_split_checks_contradictory_rebranch_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (p)
    return;
  if (p) {
    int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
    (void)v;
  }
  if (!c_is_err(p)) {
    int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
    (void)v;
  }
}

void test_split_checks_unrelated_lhs_and_trylock_rhs_c(int ok, int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  if (ok && c_is_err(p))
    return;
  int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
  (void)v;
}

// The capability is not acquired on the short-circuit confluence edge of
// '&&' or '||' if the left-hand side may also reach the successor without
// deciding the result of the call.
struct CGroupObj *c_ptr_range_nonnull(int mode)
    __attribute__((try_acquire_capability_range(1, (__UINTPTR_TYPE__)-4096, mu1)));

void test_short_circuit_and_unrelated_operand_c(int ok, int mode) {
  struct CGroupObj *p = c_ptr_range_nonnull(mode);
  if (p && ok && TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)p))
    return;
  if (!p || TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)p))
    return;
  work_data = 1;
  mutex_unlock(&mu1);
}

void test_short_circuit_or_unrelated_operand_c(int ok, int mode) {
  struct CGroupObj *p = c_ptr_range_nonnull(mode);
  if (!p || !ok || !TEST_IS_ERR_VALUE_MACRO((__UINTPTR_TYPE__)p))
    return;
}

// Short-circuit confluence, partial else join, and loop back-edge must
// not retain a narrowed PendingTrylockRange from only one predecessor.
void test_split_checks_short_circuit_or_c(int cond, int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (cond || p) {
    if (!c_is_err(p)) {
      int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
      (void)v;
    }
  }
}

void test_split_checks_else_join_c(int cond, int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p) {
    if (cond)
      return;
  }
  if (c_is_err(p))
    return;
  int v = work_data; // expected-warning{{reading variable 'work_data' requires holding mutex 'mu1'}}
  (void)v;
}

// Partial capability acquisition joined with a path that did not acquire
// the capability must clear AcquiredAttrs when the capability is not in
// EntrySet, and retain AcquiredAttrs when it is held in EntrySet.
struct CGroupObj *c_ptr_partial_two_locks(int mode)
    __attribute__((try_acquire_capability_range(1, (__UINTPTR_TYPE__)-1, mu1)))
    __attribute__((try_acquire_capability_range(1, (__UINTPTR_TYPE__)-4096, mu2)));

void test_split_checks_partial_acquire_join_c(int cond, int mode) {
  struct CGroupObj *p = c_ptr_partial_two_locks(mode); // expected-note{{mutex acquired here}}
  if (!p)
    return;
  if (cond) {
    mutex_unlock(&mu1);
  }
  if (c_is_err(p)) { // expected-warning{{mutex 'mu1' is not held on every path through here}}
    return;
  }
  work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  mutex_unlock(&mu2);
}

// 3.3 & 3.4: ConsumedAttrs across loop back-edges, 3-predecessor joins with
// partial EntryPending, and conditional unlock before re-branching.
void test_split_checks_consumed_in_loop_c(int n, int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (!p)
    return;
  for (int i = 0; i < n; ++i) {
    if (!c_is_err(p)) {
      mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
    }
  }
}

void test_three_preds_partial_entry_pending_c(int mode, int bypass_null_check) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode); // expected-note{{mutex acquired here}}
  if (!bypass_null_check) {
    if (!p)
      return;
    if (!c_is_err(p)) {
      int v = work_data;
      (void)v;
    }
  }
  if (!c_is_err(p)) { // expected-warning{{mutex 'mu1' is not held on every path through here}}
  }
}

void test_cond_unlock_before_rebranch_c(int cond) {
  int r = mutex_exclusive_trylock(&mu1); // expected-note{{mutex acquired here}}
  if (r) {
    if (cond)
      mutex_unlock(&mu1);
  }
  if (r) { // expected-warning{{mutex 'mu1' is not held on every path through here}}
  }
}

void test_cond_unlock_logical_and_before_rebranch_c(int c) {
  int r = mutex_exclusive_trylock(&mu1); // expected-note{{mutex acquired here}}
  int done = 0;
  if (r && c) {
    work_data = 1;
    mutex_unlock(&mu1);
    done = 1;
  }
  if (r && !done) { // expected-warning{{mutex 'mu1' is not held on every path through here}}
  }
}

// Releasing a capability on all paths that acquired it before joining with a
// path where the trylock was not tested prevents a later check from acquiring
// the capability, even if that check is only reached on the latter path,
// because the analysis does not track the correlation with 'c'.
void test_untested_branch_join_after_unlock_c(int c) {
  int r = mutex_exclusive_trylock(&mu1);
  if (c) {
    if (r) {
      work_data = 1;
      mutex_unlock(&mu1);
    }
  }
  if (!c) {
    if (r) {
      work_data = 2; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
      mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
    }
  }
}

// A capability that has been released on a path must not be acquired again
// after joining with a path on which the result has not been tested.
void test_consumed_on_one_branch_c(int c) {
  int r = mutex_exclusive_trylock(&mu1);
  if (c) {
    if (r) {
      work_data = 1;
      mutex_unlock(&mu1);
    }
  }
  if (r) {
    work_data = 2; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

// A capability that has not been released must still be acquired after
// joining with a path on which the result has not been tested.
void test_untested_branch_join_without_unlock_c(int c) {
  int r = mutex_exclusive_trylock(&mu1);
  if (c) {
    if (!r)
      return;
    work_data = 1;
  }
  if (r) {
    work_data = 2;
    mutex_unlock(&mu1);
  }
}

// As above, the analysis does not track the correlation between 'done' and
// whether the capability has been released.
void test_short_circuit_join_after_unlock_c(int c) {
  int r = mutex_exclusive_trylock(&mu1);
  int done = 0;
  if (c && r) {
    work_data = 1;
    mutex_unlock(&mu1);
    done = 1;
  }
  if (!done && r) {
    work_data = 2; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

int c_trylock_one_or_two(void)
    __attribute__((try_acquire_capability_range(1, 2, mu1)));

void test_disjoint_range_checks_after_unlock_c(void) {
  int r = c_trylock_one_or_two();
  if (r == 1) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  if (r == 2) {
    work_data = 2;
    mutex_unlock(&mu1);
  }
}

// A capability that has been released on some paths must not be acquired
// again by a later branch on the result of the trylock call for the values
// that the call returned on these paths, neither after a join at which the
// result may have any value nor after a loop.
void test_rebranch_after_unlock_join_c(void) {
  int r = mutex_exclusive_trylock(&mu1);
  if (r)
    mutex_unlock(&mu1);
  if (r) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

int c_trylock_1_to_100(void)
    __attribute__((try_acquire_capability_range(1, 100, mu1)));

void test_rebranch_after_unlock_and_loop_c(int n) {
  int r = c_trylock_1_to_100();
  if (r < 0)
    return;
  if (r >= 1 && r <= 100)
    mutex_unlock(&mu1);
  for (int i = 0; i < n; ++i) {
  }
  if (r >= 1 && r <= 100) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

void test_disjoint_range_checks_after_unlock_and_loop_c(int n) {
  int r = c_trylock_one_or_two();
  if (r == 1) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  for (int i = 0; i < n; ++i) {
  }
  if (r == 2) {
    work_data = 2;
    mutex_unlock(&mu1);
  }
}

void c_side_effect(void);

// A capability that is held on every path at a join must be recorded as
// released by a later unlock, even if it has been released and acquired
// again on one of the paths.
void test_unlock_after_relock_join_c(int c) {
  int r = mutex_exclusive_trylock(&mu1);
  if (!r)
    return;
  if (r == 1) {
    mutex_unlock(&mu1);
    if (c)
      c_side_effect();
    mutex_exclusive_lock(&mu1);
  }
  mutex_unlock(&mu1); // expected-note{{mutex released here}}
  if (r == 2) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

// Releasing a capability for some values of the result must not prevent
// branching on the result again from acquiring it for the other values.
void test_split_unlock_c(void) {
  int r = mutex_exclusive_trylock(&mu1);
  if (!r)
    return;
  if (r == 1) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  if (r != 1) {
    work_data = 2;
    mutex_unlock(&mu1);
  }
}

void test_split_unlock_range_c(void) {
  int r = c_trylock_one_or_two();
  if (r < 1 || r > 2)
    return;
  if (r == 1) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  if (r == 2) {
    work_data = 2;
    mutex_unlock(&mu1);
  }
}

void test_rebranch_disjoint_from_consumed_c(void) {
  int r = c_trylock_one_or_two();
  if (r == 1) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  if (r == 2)
    work_data = 2;
  if (r == 2)
    mutex_unlock(&mu1);
}

void test_rebranch_on_subset_of_range_c(void) {
  int r = c_trylock_one_or_two();
  if (r == 2)
    work_data = 2;
  if (r == 2)
    mutex_unlock(&mu1);
}

int work_data2 GUARDED_BY(mu2);
int c_trylock_overlapping_ranges(void)
    __attribute__((try_acquire_capability_range(1, 2, mu1)))
    __attribute__((try_acquire_capability_range(2, 3, mu2)));

// The values for which the capabilities of one attribute have been released
// do not affect the capabilities of another attribute.
void test_consumed_per_attribute_c(void) {
  int r = c_trylock_overlapping_ranges();
  if (r == 3) {
    work_data2 = 1;
    mutex_unlock(&mu2);
  }
  if (r >= 1 && r <= 2) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  if (r == 2) {
    work_data2 = 2;
    mutex_unlock(&mu2);
  }
}

// A capability that is released on a path on which the result has the same
// values as on a path that still holds it is not held on every path.
void test_split_unlock_rebranch_mismatch_c(int c) {
  int r = c_trylock_one_or_two(); // expected-note{{mutex acquired here}}
  if (r == 1) {
    if (c)
      mutex_unlock(&mu1);
  }
  if (r == 1) { // expected-warning{{mutex 'mu1' is not held on every path through here}}
  }
}

// Many sequential trylock checks whose results are not tested again in later
// blocks.
void test_many_sequential_trylocks_c(void) {
#define TRYLOCK_STEP(i)                                                        \
  struct Mutex m##i;                                                           \
  int t##i = mutex_exclusive_trylock(&m##i);                                   \
  if (!t##i)                                                                   \
    goto out##i;
#define UNLOCK_STEP(i)                                                         \
  mutex_unlock(&m##i);                                                         \
  out##i:;
#define TRYLOCK_GROUP8(base)                                                   \
  TRYLOCK_STEP(base##0)                                                        \
  TRYLOCK_STEP(base##1)                                                        \
  TRYLOCK_STEP(base##2)                                                        \
  TRYLOCK_STEP(base##3)                                                        \
  TRYLOCK_STEP(base##4)                                                        \
  TRYLOCK_STEP(base##5)                                                        \
  TRYLOCK_STEP(base##6)                                                        \
  TRYLOCK_STEP(base##7)
#define UNLOCK_GROUP8(base)                                                    \
  UNLOCK_STEP(base##7)                                                         \
  UNLOCK_STEP(base##6)                                                         \
  UNLOCK_STEP(base##5)                                                         \
  UNLOCK_STEP(base##4)                                                         \
  UNLOCK_STEP(base##3)                                                         \
  UNLOCK_STEP(base##2)                                                         \
  UNLOCK_STEP(base##1)                                                         \
  UNLOCK_STEP(base##0)

  TRYLOCK_GROUP8(a)
  TRYLOCK_GROUP8(b)
  TRYLOCK_GROUP8(c)
  TRYLOCK_GROUP8(d)
  TRYLOCK_GROUP8(e)
  TRYLOCK_GROUP8(f)
  TRYLOCK_GROUP8(g)
  TRYLOCK_GROUP8(h)

  UNLOCK_GROUP8(h)
  UNLOCK_GROUP8(g)
  UNLOCK_GROUP8(f)
  UNLOCK_GROUP8(e)
  UNLOCK_GROUP8(d)
  UNLOCK_GROUP8(c)
  UNLOCK_GROUP8(b)
  UNLOCK_GROUP8(a)

#undef UNLOCK_GROUP8
#undef TRYLOCK_GROUP8
#undef UNLOCK_STEP
#undef TRYLOCK_STEP
}

// Multi-parameter inline helper partitioning splits disconnected failure
// intervals ({0} and [MAX-4094, MAX]).
static inline int c_both_null(const void *a, const void *b) {
  return !a && !b;
}
void test_multi_param_inline_disconnected_failure_c(int mode) {
  struct CGroupObj *p = c_ptr_range_shared_nonnull(mode);
  if (c_both_null(p, p))
    return;
  if (c_is_err(p))
    return;
  int v = work_data;
  (void)v;
  mutex_unlock(&mu1);
}

// Conditions that call helpers that are unrelated to range trylocks must not
// use up the inline expansion budget of the analyzed function.
void test_inline_budget_unrelated_calls_c(int ok) {
  C_REP1024(if (c_unrelated_helper(c_unrelated_data)) c_unrelated_data = 0;)
  C_REP1024(if (c_unrelated_helper(c_unrelated_data) == 0) c_unrelated_data = 1;)
  struct CGroupObj *cgrp = c_ptr_range_lock_live(ok);
  if (c_is_err(cgrp))
    return;
  work_data = 30;
  mutex_unlock(&mu1);
}

// Multiple arguments of one helper that are derived from range trylocks.
static inline _Bool c_both_err(const void *a, const void *b) {
  return c_is_err(a) && c_is_err(b);
}

static inline _Bool c_err_and_not_err(const void *a, const void *b) {
  return c_is_err(a) && !c_is_err(b);
}

static inline _Bool c_both_err_mixed(const void *a, __UINTPTR_TYPE__ b) {
  return c_is_err(a) && c_is_err_value(b);
}

void test_inline_helper_multi_trylock_args_c(int ok) {
  // The results of two different trylock calls are not tracked.
  if (!c_both_err(c_ptr_range_lock_live(ok), c_ptr_range_lock_live(ok))) {
    work_data = 31; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  // The same trylock result passed twice: the false branch of a && b only
  // implies that a or b is not an error pointer, and since a == b, that the
  // capability is held.
  struct CGroupObj *p = c_ptr_range_lock_live(ok);
  if (!c_both_err(p, p)) {
    work_data = 32;
    mutex_unlock(&mu1);
  }
  // Also for parameters of different types.
  struct CGroupObj *q = c_ptr_range_lock_live(ok);
  if (!c_both_err_mixed(q, (__UINTPTR_TYPE__)q)) {
    work_data = 33;
    mutex_unlock(&mu1);
  }
  // c_err_and_not_err(r, r) is always false, which says nothing about r.
  struct CGroupObj *r = c_ptr_range_lock_live(ok);
  if (!c_err_and_not_err(r, r)) {
    work_data = 34; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
}

// Signed pointer comparisons, e.g. (long)ptr < 0, in callers.
void test_signed_ptr_cmp_callers_c(int ok) {
  if ((__INTPTR_TYPE__)c_ptr_range_lock_live(ok) < 0)
    return;
  work_data = 33;
  mutex_unlock(&mu1);

  struct CGroupObj *p = c_ptr_range_lock_live(ok);
  if (0 <= (__INTPTR_TYPE__)p) {
    work_data = 34;
    mutex_unlock(&mu1);
  }

  // [-4096, INTPTR_MAX] includes the error pointers [-4095, -1].
  if ((__INTPTR_TYPE__)c_ptr_range_lock_live(ok) >= -4096) {
    work_data = 35; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  } else {
    work_data = 36;
    mutex_unlock(&mu1);
  }
}

// Value-changing argument conversions must not be looked through.
long long c_llong_range_lock(void)
    __attribute__((try_acquire_capability_range(0, 0, mu1)));
static inline int c_is_zero_int(int v) { return v == 0; }
static inline int c_is_zero_llong(long long v) { return v == 0; }

void test_narrowing_helper_arg_c(void) {
  // Truncation to int may map a nonzero value to zero.
  if (c_is_zero_int(c_llong_range_lock())) {
    work_data = 37; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  long long r = c_llong_range_lock();
  if (c_is_zero_int(r)) {
    work_data = 38; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  if (c_is_zero_llong(c_llong_range_lock())) {
    work_data = 39;
    mutex_unlock(&mu1);
  }
}

// A recursive helper does not return its argument unchanged.
static inline void *c_recursive_identity(const void *p) {
  return c_recursive_identity(p);
}

void test_recursive_identity_helper_c(int ok) {
  if (!c_is_err(c_recursive_identity(c_ptr_range_lock_live(ok)))) {
    work_data = 40; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
}

// _Generic controlling and unselected expressions are unevaluated.
void test_generic_unevaluated_c(int unk) {
  int r = unk;
  (void)_Generic((r = mutex_exclusive_trylock(&mu1)), int: 0, default: 1); // expected-warning{{expression with side effects has no effect in an unevaluated context}}
  if (r) {
    work_data = 41; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  int r2 = unk;
  (void)_Generic(0, double: (r2 = mutex_exclusive_trylock(&mu1)), default: 0);
  if (r2) {
    work_data = 42; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  }
  (void)_Generic(work_data, int: 0, default: 1);
  (void)_Generic(0, double: work_data, default: 0);
}

// sizeof on a VLA type evaluates the array bound, whereas sizeof on a pointer
// to a VLA type and __alignof__ on a VLA type do not.
void test_sizeof_vla_type_unevaluated_c(int unk) {
  int r1 = unk;
  (void)sizeof(int (*)[(r1 = mutex_exclusive_trylock(&mu1)) + 1]);
  if (r1)
    work_data = 43; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  int r2 = unk;
  (void)__alignof__(int[(r2 = mutex_exclusive_trylock(&mu1)) + 1]);
  if (r2)
    work_data = 44; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  int r3 = unk;
  (void)sizeof(int[(r3 = mutex_exclusive_trylock(&mu1)) + 1]);
  if (r3) {
    work_data = 45;
    mutex_unlock(&mu1);
  }
}

// The cleanup functions of variables declared in a statement expression in an
// unevaluated operand do not run and the size expressions of the variable
// length arrays declared in such a statement expression are not evaluated.
void test_unevaluated_stmt_expr_decls_c(int unk) {
  (void)__builtin_constant_p(({
    struct Mutex *const __attribute__((unused, cleanup(unlock_scope))) s = &mu1;
    0;
  }));
  int r = unk;
  (void)__builtin_constant_p(({
    int a[(r = mutex_exclusive_trylock(&mu1)) + 1];
    a[0];
  }));
  if (r)
    work_data = 46; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
  // The CFG represents a declaration of more than one variable with one
  // synthetic declaration per variable.
  int r2 = mutex_exclusive_trylock(&mu1);
  (void)__builtin_constant_p(({
    int(*p)[(r2 = 0) + 1], q;
    0;
  }));
  if (r2) {
    work_data = 47;
    mutex_unlock(&mu1);
  }
}

// Combining an unrelated condition with a trylock variable check in && or ||
// only narrows the trylock variable on the branch where both (for &&) or
// neither (for ||) hold.
void test_unrelated_lhs_and_trylock_rhs_c(int ok) {
  int r = mutex_exclusive_trylock(&mu1);
  if (ok && !r)
    return;
  work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
}

// The size expressions of variable length array types in pointer
// declarations and casts are evaluated at run time but are not part of the
// CFG. A variable whose address escapes in them may be modified by any later
// call.
int *escaped_int_ptr;
static inline int keep_int_ptr(int *p) {
  escaped_int_ptr = p;
  return 4;
}
static inline void poke_escaped_int(void) { *escaped_int_ptr = 1; }
static inline int clobber_int(int *p) {
  *p = 1;
  return 4;
}

void test_vla_ptr_decl_escape_c(void) {
  int r = 1;
  int (*p)[keep_int_ptr(&r)] = 0;
  (void)p;
  r = mutex_trylock_zero(&mu1);
  poke_escaped_int();
  if (r == 0) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

void test_vla_cast_escape_c(void) {
  int r = mutex_trylock_zero(&mu1);
  void *p = (int (*)[clobber_int(&r)])0;
  (void)p;
  if (r == 0) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

void test_vla_cast_assign_c(void) {
  int r = mutex_trylock_zero(&mu1);
  void *p = (int (*)[r = 1])0;
  (void)p;
  if (r == 0) {
    work_data = 1; // expected-warning{{writing variable 'work_data' requires holding mutex 'mu1' exclusively}}
    mutex_unlock(&mu1); // expected-warning{{releasing mutex 'mu1' that was not held}}
  }
}

void test_vla_escape_after_branch_c(void) {
  int r = mutex_trylock_zero(&mu1);
  if (r == 0) {
    work_data = 1;
    mutex_unlock(&mu1);
  }
  void *p = (int (*)[clobber_int(&r)])0;
  (void)p;
}

// We had a problem where we'd skip all attributes that follow a late-parsed
// attribute in a single __attribute__.
void run(void) __attribute__((guarded_by(mu1), guarded_by(mu1))); // expected-warning 2{{only applies to non-static data members and global variables}}

int value_with_multiple_guarded_args GUARDED_BY(mu1, mu2);

int *ptr_with_multiple_guarded_args PT_GUARDED_BY(mu1, mu2);

int value_with_no_open_brace __attribute__((guarded_by)); // expected-error{{'guarded_by' attribute takes at least 1 argument}}
int *ptr_with_no_open_brace __attribute__((pt_guarded_by)); // expected-error{{'pt_guarded_by' attribute takes at least 1 argument}}

int value_with_no_open_brace_on_acquire_after __attribute__((acquired_after)); // expected-error{{'acquired_after' attribute takes at least 1 argument}}
int value_with_no_open_brace_on_acquire_before __attribute__((acquired_before)); // expected-error{{'acquired_before' attribute takes at least 1 argument}}

int value_with_bad_expr GUARDED_BY(bad_expr); // expected-error{{use of undeclared identifier 'bad_expr'}}
int *ptr_with_bad_expr PT_GUARDED_BY(bad_expr); // expected-error{{use of undeclared identifier 'bad_expr'}}

int value_with_bad_expr_on_acquire_after __attribute__((acquired_after(other_bad_expr))); //  expected-error{{use of undeclared identifier 'other_bad_expr'}}
int value_with_bad_expr_on_acquire_before __attribute__((acquired_before(other_bad_expr))); //  expected-error{{use of undeclared identifier 'other_bad_expr'}}

int a_final_expression = 0;
