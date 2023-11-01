#pragma once

#include <cstddef>
#include <memory>

namespace dlinear {

template <class T>
class Gauss {
 public:
  Gauss(size_t size, size_t seed = 42);
  Gauss(const Gauss &other) = delete;
  Gauss(Gauss &&other) = default;
  Gauss &operator=(const Gauss &other) = delete;
  Gauss &operator=(Gauss &&other) = default;
  ~Gauss();

  void sequential_generate();
  void random_generate();
  void set_A(T *A[]);
  void set_A(size_t i, T row[]);
  void set_A(size_t i, size_t j, T value) { A_[i][j] = value; }
  void set_b(T value[]);
  void set_b(size_t i, T value) { b_[i] = value; }

  size_t size() const { return size_; }

  std::unique_ptr<T[]> solve();

  void print_A();
  void print_b();

 protected:
  virtual void forward_elimination() = 0;
  std::unique_ptr<T[]> backward_substitution();

  size_t size_;
  T **A_;
  T *b_;

 private:
  size_t seed_;
};

}  // namespace dlinear
