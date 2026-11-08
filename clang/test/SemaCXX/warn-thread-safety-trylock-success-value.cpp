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

namespace Redeclarations {

bool conflict_value() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
bool conflict_value() __attribute__((try_acquire_capability(false, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

bool conflict_shared() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
bool conflict_shared() __attribute__((try_acquire_shared_capability(true, mu))); // expected-warning {{'try_acquire_shared_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

enum Result { Failure, Success };
constexpr bool kFalse = false;
bool conflict_constant() __attribute__((try_acquire_capability(Success, mu))); // expected-note {{previous attribute is here}}
bool conflict_constant() __attribute__((try_acquire_capability(kFalse, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

bool conflict_param(Mutex *m) __attribute__((try_acquire_capability(0, m))); // expected-note {{previous attribute is here}}
bool conflict_param(Mutex *p) __attribute__((try_acquire_capability(1, p))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

// Matching redeclarations.
bool match_value() __attribute__((try_acquire_capability(1, mu)));
bool match_value() __attribute__((try_acquire_capability(true, mu)));
bool match_constant() __attribute__((try_acquire_shared_capability(Success, mu)));
bool match_constant() __attribute__((try_acquire_shared_capability(!kFalse, mu)));
bool match_param(Mutex *m) __attribute__((try_acquire_capability(false, m)));
bool match_param(Mutex *p) __attribute__((try_acquire_capability(Failure, p)));

// A redeclaration must repeat the trylock attributes of the previous
// declaration, also for other capabilities.
Mutex mu2;
bool other_cap() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
bool other_cap() __attribute__((try_acquire_capability(true, mu2))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

// The order of the capability arguments does not matter.
bool match_order() __attribute__((try_acquire_capability(true, mu, mu2)));
bool match_order() __attribute__((try_acquire_capability(true, mu2, mu)));

void use() {
  if (conflict_value()) {
    data = 1;
    unlock();
  }
  if (conflict_constant()) {
    data = 1;
    unlock();
  }
  if (match_value()) {
    data = 1;
    unlock();
  }
  if (match_constant()) {
    (void)data;
    unlock_shared();
  }
  if (!match_param(&mu)) {
    data = 1;
    unlock();
  }
}

// Conflicts between redeclarations of templates are detected when the
// success values are known.
template <typename T>
bool tmpl_conflict() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
template <typename T>
bool tmpl_conflict() __attribute__((try_acquire_capability(false, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

template <typename T>
bool tmpl_match() __attribute__((try_acquire_capability(true, mu)));
template <typename T>
bool tmpl_match() __attribute__((try_acquire_capability(sizeof(T) != 0, mu)));

// Dependent success values are compared when the template is instantiated.
template <bool B>
bool tmpl_dep_conflict() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
template <bool B>
bool tmpl_dep_conflict() __attribute__((try_acquire_capability(B, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

template <bool B> struct MemberRedecl {
  bool trylock() __attribute__((try_acquire_capability(B, mu))); // expected-note {{previous attribute is here}}
};
template <bool B>
bool MemberRedecl<B>::trylock() __attribute__((try_acquire_capability(true, mu))) { // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
  return B;
}

void use_tmpl() {
  if (tmpl_conflict<int>()) {
    data = 1;
    unlock();
  }
  if (tmpl_match<int>()) {
    data = 1;
    unlock();
  }
  if (tmpl_dep_conflict<true>()) {
    data = 1;
    unlock();
  }
  if (tmpl_dep_conflict<false>()) { // expected-note {{in instantiation of function template specialization 'Redeclarations::tmpl_dep_conflict<false>' requested here}}
    data = 1;
    unlock();
  }
  MemberRedecl<true> t;
  if (t.trylock()) {
    data = 1;
    unlock();
  }
  MemberRedecl<false> f; // expected-note {{in instantiation of template class 'Redeclarations::MemberRedecl<false>' requested here}}
  if (!f.trylock()) {
    data = 1;
    unlock();
  }
}


// The attributes that the definition of a template inherited from different
// declarations are compared when the template is instantiated.
template <bool B>
bool tmpl_redecl_then_def() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
template <bool B>
bool tmpl_redecl_then_def() __attribute__((try_acquire_capability(B, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
template <bool B> bool tmpl_redecl_then_def() { return B; }

Mutex mu_other;
int data_other __attribute__((guarded_by(mu_other)));
template <bool B>
bool tmpl_redecl_diff_cap_then_def() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
template <bool B>
bool tmpl_redecl_diff_cap_then_def() __attribute__((try_acquire_capability(B, mu_other))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
template <bool B> bool tmpl_redecl_diff_cap_then_def() { return B; }

template <bool B>
bool tmpl_redecl_excl_shared_then_def() __attribute__((try_acquire_capability(true, mu))); // expected-note {{previous attribute is here}}
template <bool B>
bool tmpl_redecl_excl_shared_then_def() __attribute__((try_acquire_shared_capability(B, mu))); // expected-warning {{'try_acquire_shared_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
template <bool B> bool tmpl_redecl_excl_shared_then_def() { return B; }

template <bool B> struct MemberSameDecl {
  bool trylock() __attribute__((try_acquire_capability(true, mu))) // expected-note {{previous attribute is here}}
      __attribute__((try_acquire_capability(B, mu))); // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}
};
template <bool B> bool MemberSameDecl<B>::trylock() { return B; }

// A specialization that has been referenced before a later declaration of the
// template gets the attributes of the later declaration when that declaration
// is seen.
struct Tag {
  static constexpr bool v1 = true;
  static constexpr bool v2 = false;
};
template <class T> bool late_attr(Mutex &m);
void ref_late_attr() { (void)&late_attr<Tag>; }
template <class T>
bool late_attr(Mutex &m) __attribute__((try_acquire_capability(T::v1, m)));
template <class T> bool late_attr(Mutex &m) { return false; }

template <class T>
bool late_conflict(Mutex &m) __attribute__((try_acquire_capability(T::v1, m))); // expected-note {{previous attribute is here}}
void ref_late_conflict() { (void)&late_conflict<Tag>; }
template <class T>
bool late_conflict(Mutex &m) __attribute__((try_acquire_capability(T::v2, m))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}} \
                                                                                // expected-note {{in instantiation of function template specialization 'Redeclarations::late_conflict<Redeclarations::Tag>' requested here}}
template <class T> bool late_conflict(Mutex &m) { return false; }

template <class T> bool late_same_decl(Mutex &m);
void ref_late_same_decl() { (void)&late_same_decl<Tag>; }
template <class T>
bool late_same_decl(Mutex &m) // expected-note {{in instantiation of function template specialization 'Redeclarations::late_same_decl<Redeclarations::Tag>' requested here}}
    __attribute__((try_acquire_capability(T::v1, m))) // expected-note {{previous attribute is here}}
    __attribute__((try_acquire_capability(T::v2, m))) { // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}
  return false;
}

void use_inherited() {
  if (tmpl_redecl_then_def<false>()) { // expected-note {{in instantiation of function template specialization 'Redeclarations::tmpl_redecl_then_def<false>' requested here}}
    data = 1;
    unlock();
  } else {
    data = 2; // expected-warning {{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
  }
  if (tmpl_redecl_diff_cap_then_def<true>()) { // expected-note {{in instantiation of function template specialization 'Redeclarations::tmpl_redecl_diff_cap_then_def<true>' requested here}}
    data = 1;
    data_other = 1; // expected-warning {{writing variable 'data_other' requires holding mutex 'mu_other' exclusively}}
    unlock();
  }
  if (!tmpl_redecl_excl_shared_then_def<false>()) { // expected-note {{in instantiation of function template specialization 'Redeclarations::tmpl_redecl_excl_shared_then_def<false>' requested here}}
    int x = data; // expected-warning {{reading variable 'data' requires holding mutex 'mu'}}
    (void)x;
    unlock_shared(); // expected-warning {{releasing mutex 'mu' that was not held}}
  }
  MemberSameDecl<false> s; // expected-note {{in instantiation of template class 'Redeclarations::MemberSameDecl<false>' requested here}}
  if (s.trylock()) {
    data = 1;
    unlock();
  }
  if (late_attr<Tag>(mu)) {
    data = 1;
    unlock();
  }
  if (late_conflict<Tag>(mu)) {
    data = 1;
    unlock();
  }
  if (late_same_decl<Tag>(mu)) {
    data = 1;
    unlock();
  }
}

// Parameters are compared by their position, whatever their type
// qualifiers, and parameters of an enclosing function by their declaration.
// An implicit and an explicit 'this' are the same.
bool match_const_param(Mutex *m) __attribute__((try_acquire_capability(true, m)));
bool match_const_param(Mutex *const m) __attribute__((try_acquire_capability(true, m)));
void enclosing_params(Mutex *outer) {
  extern bool inner_caps(Mutex *inner)
      __attribute__((try_acquire_capability(true, outer)))
      __attribute__((try_acquire_capability(false, inner)));
  extern bool inner_redecl(Mutex *inner) __attribute__((try_acquire_capability(true, outer))); // expected-note {{previous attribute is here}}
  extern bool inner_redecl(Mutex *inner) __attribute__((try_acquire_capability(true, inner))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
}
struct ThisMember {
  Mutex mu;
  bool trylock_redecl() __attribute__((try_acquire_capability(true, mu)));
  bool trylock_same_decl() __attribute__((try_acquire_capability(true, mu))) // expected-note {{previous attribute is here}}
      __attribute__((try_acquire_capability(false, this->mu))); // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}
};
bool ThisMember::trylock_redecl() __attribute__((try_acquire_capability(true, this->mu))) {
  return false;
}

} // namespace Redeclarations

namespace SameDeclaration {

Mutex mu2;

// Trylock attributes of the same declaration must not contradict each other
// for a capability: with the same access mode but different success values,
// or with different access modes but the same success value.
bool conflict_value() __attribute__((try_acquire_capability(true, mu))) // expected-note {{previous attribute is here}}
    __attribute__((try_acquire_capability(false, mu))); // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}
bool conflict_shared() __attribute__((try_acquire_capability(true, mu, mu2))) // expected-note {{previous attribute is here}}
    __attribute__((try_acquire_shared_capability(true, mu2))); // expected-warning {{'try_acquire_shared_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}

// Different capabilities may have different success values, a capability may
// be acquired exclusively on success and shared on failure, and an attribute
// may be repeated.
bool other_caps() __attribute__((try_acquire_capability(true, mu)))
    __attribute__((try_acquire_capability(false, mu2)));
bool exclusive_or_shared() __attribute__((try_acquire_capability(true, mu)))
    __attribute__((try_acquire_shared_capability(false, mu)));
bool repeated() __attribute__((try_acquire_capability(true, mu)))
    __attribute__((try_acquire_capability(1, mu)));

// Dependent success values are compared when the template is instantiated.
template <bool B>
bool tmpl_conflict() __attribute__((try_acquire_capability(true, mu))) // expected-note {{previous attribute is here}}
    __attribute__((try_acquire_capability(B, mu))); // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}

void use() {
  if (conflict_value()) {
    data = 1;
    unlock();
  }
  if (other_caps()) {
    data = 1;
    unlock();
  } else {
    mu2.Unlock();
  }
  if (repeated()) {
    data = 1;
    unlock();
  }
  if (exclusive_or_shared()) {
    data = 1;
    unlock();
  } else {
    (void)data;
    unlock_shared();
  }
  if (tmpl_conflict<true>()) {
    data = 1;
    unlock();
  }
  if (tmpl_conflict<false>()) { // expected-note {{in instantiation of function template specialization 'SameDeclaration::tmpl_conflict<false>' requested here}}
    data = 1;
    unlock();
  }
}


// The trylock attributes of a parameter of a function template are compared
// when the parameter is instantiated during template argument deduction.
template <bool B>
void parm_conflict(bool (*fp)()
                       __attribute__((try_acquire_capability(true, mu))) // expected-note {{previous attribute is here}}
                       __attribute__((try_acquire_capability(B, mu)))) { // expected-warning {{'try_acquire_capability' attribute conflicts with an earlier attribute on the same declaration; ignoring the attribute}}
  if (fp()) {
    data = 1;
    unlock();
  } else {
    data = 2; // expected-warning {{writing variable 'data' requires holding mutex 'mu' exclusively}}
    unlock(); // expected-warning {{releasing mutex 'mu' that was not held}}
  }
}
bool bool_fn();
void use_parm_conflict() {
  parm_conflict<false>(&bool_fn); // expected-note {{while substituting explicitly-specified template arguments into function template 'parm_conflict'}} \
                                  // expected-note {{while substituting deduced template arguments into function template 'parm_conflict' [with B = false]}}
}
template void parm_conflict<false>(bool (*)()); // expected-note {{in instantiation of function template specialization 'SameDeclaration::parm_conflict<false>' requested here}}

} // namespace SameDeclaration

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
