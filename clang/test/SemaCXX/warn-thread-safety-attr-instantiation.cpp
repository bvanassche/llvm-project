// RUN: %clang_cc1 -std=c++20 -fsyntax-only -verify -Wthread-safety %s
// RUN: %clang_cc1 -std=c++17 -fsyntax-only -verify -Wthread-safety %s
// RUN: %clang_cc1 -std=c++20 -fsyntax-only -verify=default %s

// default-no-diagnostics

// Sema checks of try_acquire attribute arguments must neither odr-use
// constants nor affect template argument deduction.

struct __attribute__((capability("mutex"))) Mutex {};
Mutex mu;
int data __attribute__((guarded_by(mu)));
void unlock() __attribute__((release_capability(mu)));

// Evaluating a success value must not odr-use a local constant. Otherwise a
// lambda would capture it, which changes its layout, or a lambda without a
// capture default would be rejected. The lambdas return a failure value such
// that their bodies are correct.
int lambda_capture_default() {
  const int lo = 0;
  auto l = [=]() __attribute__((try_acquire_capability(lo, mu))) { return 1; };
  static_assert(sizeof(l) == 1, "lambda captured 'lo'");
  auto r = [=]() __attribute__((try_acquire_capability_range(lo, lo, mu))) {
    return 1;
  };
  static_assert(sizeof(r) == 1, "lambda captured 'lo'");
  return l() + r();
}

void lambda_no_capture() {
  constexpr int lo = 0;
  auto l = []() __attribute__((try_acquire_capability(lo, mu))) { return 1; };
  auto r = []() __attribute__((try_acquire_shared_capability_range(lo, lo, mu))) {
    return 1;
  };
  (void)l;
  (void)r;
}

template <typename T> int lambda_in_template() {
  const T lo = 0;
  auto l = [=]() __attribute__((try_acquire_capability_range(lo, lo, mu))) {
    return 1;
  };
  static_assert(sizeof(l) == 1, "lambda captured 'lo'");
  return l();
}
template int lambda_in_template<int>();

// Success values that refer to variable templates and to static data members
// of class templates are still instantiated and evaluated.
template <typename T> constexpr int success_v = 1;
template <typename T> struct Bounds {
  static constexpr int lo = 0;
  static constexpr int hi = 0;
};

int try_var_template() __attribute__((try_acquire_capability(success_v<int>, mu)));
int try_static_member()
    __attribute__((try_acquire_capability_range(Bounds<int>::lo,
                                                Bounds<int>::hi, mu)));

void use_instantiated_success_values() {
  if (try_var_template()) {
    data = 1;
    unlock();
  }
}

// An invalid attribute on a function parameter of a function template must
// not cause a substitution failure, i.e. must not affect which overload is
// selected. Its warnings are reported when the specialization is used, while
// its errors are not reported and the attribute is ignored.
template <class F> char pick(F fp __attribute__((try_acquire_capability(1, mu))));
long pick(...);
template <class F>
char pick_range(F fp __attribute__((try_acquire_capability_range(0, 0, mu)))); // \
  // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'double'; ignoring the attribute}} \
  // expected-warning {{'try_acquire_capability_range' attribute on a variable requires the variable to be of function pointer type}}
long pick_range(...);
template <class F>
char pick_shared_range(
    F fp __attribute__((try_acquire_shared_capability_range(0, 0, mu)))); // \
  // expected-warning {{'try_acquire_shared_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'double'; ignoring the attribute}}
long pick_shared_range(...);
template <int L, int H, class F>
char pick_bounds(F fp __attribute__((try_acquire_capability_range(L, H, mu))));
template <int L, int H> long pick_bounds(...);

double (*dfp)();
int (*ifp)();
int not_a_function_pointer;

static_assert(sizeof(pick(ifp)) == 1, "");
static_assert(sizeof(pick(dfp)) == 1, "annotation changed overload resolution");
static_assert(sizeof(pick_range(ifp)) == 1, "");
static_assert(sizeof(pick_range(dfp)) == 1, // expected-note {{while substituting deduced template arguments into function template 'pick_range' [with F = double (*)()]}}
              "annotation changed overload resolution");
static_assert(sizeof(pick_shared_range(dfp)) == 1, // expected-note {{while substituting deduced template arguments into function template 'pick_shared_range' [with F = double (*)()]}}
              "annotation changed overload resolution");
static_assert(sizeof(pick_range(not_a_function_pointer)) == 1, // expected-note {{while substituting deduced template arguments into function template 'pick_range' [with F = int]}}
              "annotation changed overload resolution");
static_assert(sizeof(pick_bounds<0, 1>(ifp)) == 1, "");
static_assert(sizeof(pick_bounds<1, 0>(ifp)) == 1,
              "annotation changed overload resolution");

// Outside template argument deduction, invalid attributes are still
// diagnosed.
template <typename T> struct Wrapper {
  T get() __attribute__((try_acquire_capability_range(0, 0, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'double'; ignoring the attribute}}
};
Wrapper<double> wrapper; // expected-note {{in instantiation of template class 'Wrapper<double>' requested here}}

// The return type checks of instantiated declarations only warn, such that
// explicit specializations and instantiations for return types that the
// attribute does not apply to remain valid.
template <class T>
T range_tmpl() __attribute__((try_acquire_capability_range(0, 1, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}
template <> bool range_tmpl<bool>(); // expected-note {{in instantiation of function template specialization 'range_tmpl<bool>' requested here}}
template <> int range_tmpl<int>();

template <class T> struct RangeMember {
  T get() __attribute__((try_acquire_capability_range(256, 512, mu))); // expected-warning {{'try_acquire_capability_range' attribute range [256, 512] does not contain any value of return type 'unsigned char'; ignoring the attribute}}
};
template struct RangeMember<unsigned char>; // expected-note {{in instantiation of template class 'RangeMember<unsigned char>' requested here}}
template struct RangeMember<int>;

template <class F> struct RangeField {
  F f __attribute__((try_acquire_capability_range(0, 0, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}
};
RangeField<bool (*)()> range_field_bool; // expected-note {{in instantiation of template class 'RangeField<bool (*)()>' requested here}}
RangeField<int (*)()> range_field_int;

// Unevaluated operands (sizeof, noexcept) in try_acquire bounds must not
// instantiate referenced template definitions.
template <typename T> constexpr int unevaluated_bad() {
  static_assert(sizeof(T) == 0, "should not be instantiated in sizeof/noexcept");
  return 0;
}
int try_unevaluated_sizeof() __attribute__((try_acquire_capability_range(
    0, sizeof(unevaluated_bad<int>()) - sizeof(int), mu)));
int try_unevaluated_noexcept() __attribute__((try_acquire_capability_range(
    0, noexcept(unevaluated_bad<long>()) ? 0 : 0, mu)));

// Speculative SFINAE parameter substitutions must not fail overload
// resolution.
struct ParamRangeSFINAE {
  static constexpr int hi = 5;
#if __cplusplus >= 202002L
  template <typename T>
  static auto sfinae_requires(
      T (*cb)() __attribute__((try_acquire_capability_range(10, sizeof(T) + hi, mu))))
      requires(sizeof(T) == 999);
  template <typename T> static long sfinae_requires(...);
  static constexpr int k1 = sizeof(sfinae_requires<int>(nullptr));
#endif
};

// Deduced return type checks must inspect attributes on redeclarations even
// when the defining declaration itself has no attributes.
struct DeducedRedeclChecks {
  friend auto deduced_bool_friend() { return true; }
  friend auto deduced_bool_friend()
      __attribute__((try_acquire_capability_range(0, 1, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}

  friend auto deduced_conflict_friend() { return 0; }
  friend auto deduced_conflict_friend()
      __attribute__((try_acquire_capability_range(1, 255, mu))); // expected-note {{previous attribute is here}}
  friend auto deduced_conflict_friend()
      __attribute__((try_acquire_capability(true, mu))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
};

auto deduced_local_extern_bool() {
  extern auto deduced_local_extern_bool()
      __attribute__((try_acquire_capability_range(0, 1, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}
  return true;
}

// Out-of-line template definitions with conflicting try_acquire attributes
// must be diagnosed even when a specialization was already instantiated from
// the forward declaration.
template <int A, int B>
int out_of_line_conflict()
    __attribute__((try_acquire_capability(A, mu))); // expected-note {{previous attribute is here}}

void trigger_out_of_line_decl_inst() {
  (void)&out_of_line_conflict<0, 1>;
}

template <int A, int B>
int out_of_line_conflict() // expected-note {{in instantiation of function template specialization 'out_of_line_conflict<0, 1>' requested here}}
    __attribute__((try_acquire_capability(B, mu))) { // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
  return 1;
}

int instantiate_out_of_line_def() { return out_of_line_conflict<0, 1>(); }

// An unrelated attribute that is inherited through a redeclaration does not
// prevent this.
template <int A, int B>
[[nodiscard]] int out_of_line_inherited()
    __attribute__((try_acquire_capability(A, mu))); // expected-note {{previous attribute is here}}
template <int A, int B> int out_of_line_inherited();

void trigger_out_of_line_inherited() {
  (void)&out_of_line_inherited<0, 1>;
}

template <int A, int B>
int out_of_line_inherited() // expected-note {{in instantiation of function template specialization 'out_of_line_inherited<0, 1>' requested here}}
    __attribute__((try_acquire_capability(B, mu))) { // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
  return 1;
}

int instantiate_out_of_line_inherited() {
  return out_of_line_inherited<0, 1>();
}

template <int N>
int tmpl_redecl_diff_range_then_def()
    __attribute__((try_acquire_capability_range(0, 0, mu))); // expected-note {{previous attribute is here}}
template <int N>
int tmpl_redecl_diff_range_then_def()
    __attribute__((try_acquire_capability_range(N, N, mu))); // expected-warning {{'try_acquire_capability_range' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}
template <int N> int tmpl_redecl_diff_range_then_def() { return N; }

int instantiate_tmpl_redecl_diff_range_then_def() {
  return tmpl_redecl_diff_range_then_def<1>(); // expected-note {{in instantiation of function template specialization 'tmpl_redecl_diff_range_then_def<1>' requested here}}
}

template <typename T>
auto templ_deduced_bool_range(T x)
    __attribute__((try_acquire_capability_range(0, 1, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}
template <typename T>
auto templ_deduced_bool_range(T x) {
  return x;
}

bool instantiate_templ_deduced_bool_range() {
  return templ_deduced_bool_range(true); // expected-note {{in instantiation of function template specialization 'templ_deduced_bool_range<bool>' requested here}}
}

// An invalid attribute that is repeated on a redeclaration is diagnosed once.
auto deduced_bool_repeated()
    __attribute__((try_acquire_capability_range(0, 1, mu))); // expected-warning {{'try_acquire_capability_range' attribute only applies to functions and function pointers or references that return a non-boolean integer, unscoped enumeration, or pointer type; type here is 'bool'; ignoring the attribute}}
auto deduced_bool_repeated()
    __attribute__((try_acquire_capability_range(0, 1, mu))) {
  return true;
}

// The warnings about a trylock attribute of a parameter of a function template
// that are found during template argument deduction are reported when the
// specialization is used, once.
template <class T>
void try_deduced_param(T p __attribute__((try_acquire_capability(1, mu)))); // expected-warning {{'try_acquire_capability' attribute on a variable requires the variable to be of function pointer type}}
template <int N>
void try_nonbinary_param(
    int (*fp)() __attribute__((try_acquire_capability(N, mu)))); // expected-warning {{'try_acquire_capability' attribute success value 2 is treated as 'true'}}
void use_try_params() {
  try_deduced_param(42); // expected-note {{while substituting deduced template arguments into function template 'try_deduced_param' [with T = int]}}
  try_nonbinary_param<2>(ifp); // expected-note {{while substituting explicitly-specified template arguments into function template 'try_nonbinary_param'}} \
                               // expected-note {{while substituting deduced template arguments into function template 'try_nonbinary_param' [with N = 2]}}
}

// Conflict detection after an invalid integer literal capability argument.
bool trylock_after_invalid_lit(Mutex *m)
    __attribute__((try_acquire_capability(false, 1))); // expected-warning {{'try_acquire_capability' attribute requires arguments whose type is annotated with 'capability' attribute; type here is 'int'}} expected-note {{previous attribute is here}}
bool trylock_after_invalid_lit(Mutex *m)
    __attribute__((try_acquire_capability(true, m))); // expected-warning {{'try_acquire_capability' attribute on redeclaration conflicts with previous declaration; ignoring the attribute}}

// An empty variadic capability pack names no capabilities, also on a
// non-static method of a capability class.
struct __attribute__((capability("mutex"))) VariadicCapMutex {
  void Unlock() __attribute__((release_capability()));
  template <typename... Mus>
  int TryAllRange(Mus &...mus)
      __attribute__((try_acquire_capability_range(0, 0, mus...)));
};

