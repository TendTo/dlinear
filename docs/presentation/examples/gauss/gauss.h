#pragma once

#include <cstddef>
#include <memory>
#include <mutex>
#include <string>

#define DEFAULT_SEED 42

namespace dlinear {

template <class T>
class Gauss {
 public:
  Gauss(size_t size, size_t seed);
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
  size_t seed() const { return seed_; }
  const T *const *const A() const { return A_; }
  const T *const b() const { return b_; }
  std::string type_name() const;
  virtual std::string class_name() const = 0;

  std::unique_ptr<T[]> solve();

  void print_A();
  void print_b();

 protected:
  virtual void forward_elimination() = 0;
  std::unique_ptr<T[]> backward_substitution();

  size_t size_;
  T **A_;
  T *b_;
  size_t *permutation_;

 private:
  size_t seed_;
};

template <class T>
std::ostream &operator<<(std::ostream &os, const Gauss<T> &gauss);

}  // namespace dlinear
