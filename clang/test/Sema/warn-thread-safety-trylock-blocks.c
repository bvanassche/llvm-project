// RUN: %clang_cc1 -fsyntax-only -verify -fblocks -Wthread-safety -Wthread-safety-beta %s

// A block may modify the __block variables it captures.

struct __attribute__((capability("mutex"))) Mutex {
  int x;
};

struct Mutex mu;

void lock(struct Mutex *m) __attribute__((acquire_capability(m)));

int modified_by_block(void) // expected-note{{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  __block int r = -11;
  void (^blk)(void) = ^{
    r = 0;
  };
  blk();
  return r; // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
}

int modified_by_block_in_stmt_expr(void) // expected-note{{mutex acquired here}}
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  return ({ // expected-warning{{expecting mutex 'mu' to be held at the end of function}}
    __block int r = -11;
    ^{
      r = 0;
    }();
    r;
  });
}

// A block that captures a variable by value cannot modify it.
int captured_by_value(void)
    __attribute__((try_acquire_capability_range(0, 0, mu))) {
  int r = -11;
  void (^blk)(void) = ^{
    (void)r;
  };
  blk();
  return r;
}
