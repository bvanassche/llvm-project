// RUN: %clang_cc1 -fsyntax-only -verify -Wthread-safety -Wthread-safety-beta -std=c++20 %s -Wno-coroutines-unsupported-target

// expected-no-diagnostics

namespace std {
template <typename _Result, typename...>
struct coroutine_traits {
  using promise_type = typename _Result::promise_type;
};

template <typename _Promise = void>
struct coroutine_handle;

template <>
struct coroutine_handle<void> {
  static coroutine_handle from_address(void *__a) noexcept;
  void resume() const noexcept;
  void destroy() const noexcept;
};

template <typename _Promise>
struct coroutine_handle : coroutine_handle<> {};

struct suspend_always {
  bool await_ready() const noexcept;
  void await_suspend(coroutine_handle<>) const noexcept;
  void await_resume() const noexcept;
};

template <>
struct coroutine_traits<int> {
  struct promise_type {
    suspend_always initial_suspend() noexcept;
    suspend_always final_suspend() noexcept;
    int get_return_object() noexcept;
    void unhandled_exception() noexcept;
    void return_value(int value) noexcept;
  };
};
} // namespace std

class __attribute__((capability("mutex"))) Mutex {
public:
  void Lock() __attribute__((acquire_capability()));
  void Unlock() __attribute__((release_capability()));
};

Mutex co_mu;

int CoroWithTryAcquire() __attribute__((try_acquire_capability(0, co_mu))) {
  co_return 0;
}

class Task {
public:
  struct promise_type {
  public:
    std::suspend_always initial_suspend() noexcept;
    std::suspend_always final_suspend() noexcept;

    Task get_return_object() noexcept;
    void unhandled_exception() noexcept;
    void return_value(int value) noexcept;

    std::suspend_always yield_value(int value) noexcept;
  };
};

Task Foo() noexcept {
  // ICE'd
  co_yield({ int frame = 0; 0; });
  co_await({ int frame = 0; std::suspend_always(); });
  co_return({ int frame = 0; 0; });
}
