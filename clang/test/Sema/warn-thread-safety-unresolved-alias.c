// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta %s

// Local pointer variables whose value the analysis cannot resolve, e.g.
// because the value has been loaded by inline assembly as in the arm64
// implementation of smp_load_acquire().

struct __attribute__((capability("spinlock"))) spinlock {
  int x;
};
struct wq {
  struct spinlock lock;
  int data __attribute__((guarded_by(lock)));
};
struct req {
  struct wq *head;
};
struct holder {
  struct wq *wq;
};
void spin_lock(struct spinlock *l) __attribute__((acquire_capability(l)));
void spin_unlock(struct spinlock *l) __attribute__((release_capability(l)));
int busy(struct req *r);

#define load_acquire_asm(p)                                                    \
  ({                                                                           \
    union {                                                                    \
      __typeof__(*(p)) __val;                                                  \
      char __c[1];                                                             \
    } __u;                                                                     \
    __typeof__(p) __p = (p);                                                   \
    asm volatile("" : "=r"(*(unsigned long *)__u.__c) : "m"(*__p));            \
    (__typeof__(*(p)))__u.__val;                                               \
  })

// Do not name the capability after a variable that is declared inside the
// statement expression.
void name_of_alias(struct req *r) {
  struct wq *head = load_acquire_asm(&r->head);
  spin_lock(&head->lock); // expected-note{{spinlock acquired here}}
} // expected-warning{{spinlock 'head->lock' is still held at the end of function}}

// The analysis cannot tell whether head->lock is r->head->lock.
int trylock_through_alias(struct req *r)
    __attribute__((try_acquire_capability(1, &r->head->lock))) {
  struct wq *head = load_acquire_asm(&r->head);
  if (head) {
    spin_lock(&head->lock);
    if (!busy(r))
      return 1;
    spin_unlock(&head->lock);
  }
  return 0;
}

// But a capability that is held on a failure path is still reported.
int trylock_through_alias_bad(struct req *r)
    __attribute__((try_acquire_capability(1, &r->head->lock))) {
  struct wq *head = load_acquire_asm(&r->head);
  if (head) {
    spin_lock(&head->lock); // expected-note{{spinlock acquired here}}
    if (!busy(r))
      return 0; // expected-warning{{spinlock 'head->lock' is still held at the end of function}}
    spin_unlock(&head->lock);
  }
  return 0;
}

// Statement expressions appearing as subexpressions of a local pointer
// initializer must also fall back to the local variable name rather than
// collapsing distinct capabilities onto '#undefined'.
void subexpr_stmt_expr_distinct(struct holder **p1, struct holder **p2) {
  struct wq *a = load_acquire_asm(p1)->wq;
  struct wq *b = load_acquire_asm(p2)->wq;
  spin_lock(&a->lock); // expected-note{{spinlock acquired here}}
  b->data = 42;        // expected-warning{{writing variable 'data' requires holding spinlock 'b->lock' exclusively}}
  // expected-note@-1{{found near match 'a->lock'}}
  spin_unlock(&b->lock); // expected-warning{{releasing spinlock 'b->lock' that was not held}}
} // expected-warning{{spinlock 'a->lock' is still held at the end of function}}

void nested_stmt_expr_distinct(struct holder **p1, struct holder **p2) {
  struct wq *a = ({
    struct holder *__h = load_acquire_asm(p1);
    __h->wq;
  });
  struct wq *b = ({
    struct holder *__h = load_acquire_asm(p2);
    __h->wq;
  });
  spin_lock(&a->lock); // expected-note{{spinlock acquired here}}
  spin_unlock(&b->lock); // expected-warning{{releasing spinlock 'b->lock' that was not held}}
} // expected-warning{{spinlock 'a->lock' is still held at the end of function}}
