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
  return l();
}

void lambda_no_capture() {
  constexpr int lo = 0;
  auto l = []() __attribute__((try_acquire_capability(lo, mu))) { return 1; };
  (void)l;
}

// Success values that refer to variable templates are still instantiated and
// evaluated.
template <typename T> constexpr int success_v = 1;

int try_var_template() __attribute__((try_acquire_capability(success_v<int>, mu)));

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

double (*dfp)();
int (*ifp)();

static_assert(sizeof(pick(ifp)) == 1, "");
static_assert(sizeof(pick(dfp)) == 1, "annotation changed overload resolution");

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
