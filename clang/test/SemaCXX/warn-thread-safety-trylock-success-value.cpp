// RUN: %clang_cc1 -std=c++17 -fsyntax-only -verify -Wthread-safety %s
// RUN: %clang_cc1 -std=c++20 -fsyntax-only -verify -Wthread-safety %s

// Success values of try_acquire_capability and try_acquire_shared_capability
// that are integer or boolean constant expressions other than literals.

struct __attribute__((capability("mutex"))) Mutex {
  void Unlock() __attribute__((release_capability()));
};

Mutex mu;
int data __attribute__((guarded_by(mu)));
void unlock() __attribute__((release_capability(mu)));
void unlock_shared() __attribute__((release_shared_capability(mu)));

namespace ConstantSuccessValues {

enum Result { Failure, Success };
constexpr bool kTrue = true;
constexpr int kZero = 0;
constexpr bool success() { return true; }
constexpr int failure() { return 0; }

bool try_enum() __attribute__((try_acquire_capability(Success, mu)));
bool try_enum_fail() __attribute__((try_acquire_capability(Failure, mu)));
bool try_var() __attribute__((try_acquire_capability(kTrue, mu)));
bool try_var_fail() __attribute__((try_acquire_capability(kZero, mu)));
bool try_fn() __attribute__((try_acquire_shared_capability(success(), mu)));
bool try_fn_fail() __attribute__((try_acquire_capability(failure(), mu)));
bool try_sizeof() __attribute__((try_acquire_capability(sizeof(char), mu)));
bool try_cast() __attribute__((try_acquire_capability((bool)2, mu)));
bool try_expr() __attribute__((try_acquire_capability(kZero + 1 == 1, mu)));

void use() {
  if (try_enum()) {
    data = 1;
    unlock();
  }
  if (!try_enum_fail()) {
    data = 1;
    unlock();
  }
  if (try_var()) {
    data = 1;
    unlock();
  }
  if (!try_var_fail()) {
    data = 1;
    unlock();
  }
  if (try_fn()) {
    (void)data;
    unlock_shared();
  }
  if (!try_fn_fail()) {
    data = 1;
    unlock();
  }
  if (try_sizeof()) {
    data = 1;
    unlock();
  }
  if (try_cast()) {
    data = 1;
    unlock();
  }
  if (try_expr()) {
    data = 1;
    unlock();
  }
}

// The success value of a trylock function is a boolean. Other values are
// treated as 'true'.
bool try_two() __attribute__((try_acquire_capability(2, mu))); // expected-warning {{'try_acquire_capability' attribute success value 2 is treated as 'true'}}
bool try_minus_one() __attribute__((try_acquire_shared_capability(-1, mu))); // expected-warning {{'try_acquire_shared_capability' attribute success value -1 is treated as 'true'}}
bool try_sizeof_int() __attribute__((try_acquire_capability(sizeof(int) * 2, mu))); // expected-warning {{'try_acquire_capability' attribute success value 8 is treated as 'true'}}
enum Big { BigValue = 42 };
bool try_big_enum() __attribute__((try_acquire_capability(BigValue, mu))); // expected-warning {{'try_acquire_capability' attribute success value 42 is treated as 'true'}}

void use_non_binary() {
  if (try_two()) {
    data = 1;
    unlock();
  }
  if (try_big_enum()) {
    data = 1;
    unlock();
  }
}

// A success value that is not a constant expression is ignored.
int non_constant;
const int non_constant_const = non_constant;
bool try_non_constant() __attribute__((try_acquire_capability(non_constant, mu))); // expected-warning {{'try_acquire_capability' attribute success value is not a constant expression; ignoring the attribute}}
bool try_non_constant_const() __attribute__((try_acquire_capability(non_constant_const, mu))); // expected-warning {{'try_acquire_capability' attribute success value is not a constant expression; ignoring the attribute}}
constexpr int divide(int x) { return 1 / x; }
bool try_div_zero() __attribute__((try_acquire_capability(divide(0), mu))); // expected-warning {{'try_acquire_capability' attribute success value is not a constant expression; ignoring the attribute}}

void use_non_constant() {
  if (try_non_constant())
    unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
  if (try_div_zero())
    unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
}

// Template-dependent success values are checked when instantiated.
template <int N> struct TrylockTmpl {
  bool trylock() __attribute__((try_acquire_capability(N, mu))); // expected-warning {{'try_acquire_capability' attribute success value 3 is treated as 'true'}}
};

template <bool B> bool try_dep() __attribute__((try_acquire_capability(B, mu)));
template <typename T> bool try_dep_sizeof()
    __attribute__((try_acquire_capability(sizeof(T) == 1, mu)));

void use_dependent() {
  TrylockTmpl<1> t1;
  if (t1.trylock()) {
    data = 1;
    unlock();
  }
  TrylockTmpl<0> t0;
  if (!t0.trylock()) {
    data = 1;
    unlock();
  }
  TrylockTmpl<3> t3; // expected-note {{in instantiation of template class 'ConstantSuccessValues::TrylockTmpl<3>' requested here}}
  (void)t3;
  if (try_dep<true>()) {
    data = 1;
    unlock();
  }
  if (!try_dep<false>()) {
    data = 1;
    unlock();
  }
  if (try_dep_sizeof<char>()) {
    data = 1;
    unlock();
  }
  if (!try_dep_sizeof<int>()) {
    data = 1;
    unlock();
  }
}

} // namespace ConstantSuccessValues

namespace ReferencedDeclarations {

// Functions and variable templates referenced by a success value are
// instantiated if they are needed to evaluate it, and only then.
template <typename T> constexpr T one() { return T(1); }
template <typename T> bool nonconstexpr() { return T::nonexistent; }
template <typename T> constexpr int var_tmpl = 1;
static bool undefined_helper();

#if __cplusplus >= 202002L
bool try_lambda() __attribute__((try_acquire_capability([] { return one<bool>(); }(), mu)));
#endif
bool try_sizeof() __attribute__((try_acquire_capability(sizeof(nonconstexpr<int>()) == 1, mu)));
bool try_noexcept() __attribute__((try_acquire_capability(noexcept(nonconstexpr<long>()) ? 0 : var_tmpl<char>, mu)));
bool try_undefined() __attribute__((try_acquire_capability(sizeof(undefined_helper()), mu)));

void use() {
#if __cplusplus >= 202002L
  if (try_lambda()) {
    data = 1;
    unlock();
  }
#endif
  if (try_sizeof()) {
    data = 1;
    unlock();
  }
  if (try_noexcept()) {
    data = 1;
    unlock();
  }
  if (try_undefined()) {
    data = 1;
    unlock();
  }
}

} // namespace ReferencedDeclarations

namespace LaterDeclaredMembers {

// Trylock attributes may reference static constexpr data members that are
// declared later in the class.
struct Later {
  bool trylock_fail() __attribute__((try_acquire_capability(kFail, mu)));

  void caller() {
    if (!trylock_fail()) {
      data = 1;
      unlock();
    }
  }

  static constexpr bool kFail = false;
};

void use_later(Later &l) {
  if (!l.trylock_fail()) {
    data = 1;
    unlock();
  }
}

} // namespace LaterDeclaredMembers

namespace TypeDependentSuccessValues {

// A type-dependent success value is checked when the template is
// instantiated.
template <typename T>
bool trylock_dep() __attribute__((try_acquire_capability(T::value, mu))); // expected-error {{'try_acquire_capability' attribute requires parameter 1 to be int or bool}}

struct TrueValue {
  static constexpr bool value = true;
};
struct ZeroValue {
  static constexpr int value = 0;
};
struct PointerValue {
  static constexpr int *value = nullptr;
};

void use_dep() {
  if (trylock_dep<TrueValue>()) {
    data = 1;
    unlock();
  }
  if (!trylock_dep<ZeroValue>()) {
    data = 1;
    unlock();
  }
  trylock_dep<PointerValue>(); // expected-note {{in instantiation of function template specialization 'TypeDependentSuccessValues::trylock_dep<TypeDependentSuccessValues::PointerValue>' requested here}}
}

} // namespace TypeDependentSuccessValues
