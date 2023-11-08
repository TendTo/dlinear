#include "gauss.h"

#include <gmpxx.h>

#include <iostream>
#include <random>

namespace dlinear {

template <class T>
Gauss<T>::Gauss(size_t size, size_t seed) : size_{size}, permutation_{nullptr}, seed_{seed} {
  static_assert(std::is_same<double, T>() || std::is_base_of<mpq_class, T>() || std::is_base_of<mpf_class, T>(),
                "Template type must be either double, mpq_class or mpf_class");
  A_ = new T *[size_];
  for (size_t i = 0; i < size_; ++i) {
    A_[i] = new T[size_];
  }
  b_ = new T[size_];
}

template <class T>
Gauss<T>::~Gauss() {
  for (size_t i = 0; i < size_; ++i) {
    delete[] A_[i];
  }
  delete[] A_;
  delete[] b_;
}

template <class T>
void Gauss<T>::set_A(T *A[]) {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = A[i][j];
    }
  }
}

template <class T>
void Gauss<T>::set_A(size_t i, T row[]) {
  for (size_t j = 0; j < size_; ++j) {
    A_[i][j] = row[j];
  }
}

template <class T>
void Gauss<T>::set_b(T value[]) {
  for (size_t i = 0; i < size_; ++i) {
    b_[i] = value[i];
  }
}

template <class T>
std::unique_ptr<T[]> Gauss<T>::backward_substitution() {
  std::unique_ptr<T[]> x{std::make_unique<T[]>(size_)};
  for (size_t i = size_ - 1; i < size_; --i) {
    T &x_i = permutation_ == nullptr ? x[i] : x[permutation_[i]];
    if (A_[i][i] == 0) throw std::runtime_error("Indeterminate system");
    x_i = b_[i];
    for (size_t j = i + 1; j < size_; ++j) {
      const T &x_j = permutation_ == nullptr ? x[j] : x[permutation_[j]];
      x_i -= A_[i][j] * x_j;
    }
    x_i /= A_[i][i];
  }
  return x;
}

template <class T>
std::unique_ptr<T[]> Gauss<T>::solve() {
  forward_elimination();
  return backward_substitution();
}

template <class T>
bool Gauss<T>::is_grater_than_abs(const T &a, const T &b) {
  if (a > 0 && b > 0) {
    return a > b;
  } else if (a < 0 && b < 0) {
    return a < b;
  } else if (a >= 0) {
    return true;
  } else {
    return false;
  }
}

template <class T>
void Gauss<T>::print_A() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      std::cout << A_[i][j] << " ";
    }
    std::cout << std::endl;
  }
}

template <class T>
void Gauss<T>::print_b() {
  for (size_t i = 0; i < size_; ++i) {
    std::cout << b_[i] << std::endl;
  }
}

template <class T>
std::ostream &operator<<(std::ostream &os, const Gauss<T> &gauss) {
  for (size_t i = 0; i < gauss.size(); ++i) {
    for (size_t j = 0; j < gauss.size(); ++j) {
      std::cout << gauss.A()[i][j] << " ";
    }
    std::cout << "\t | " << gauss.b()[i] << std::endl;
  }
  return os;
}

template <class T>
void Gauss<T>::sequential_generate() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = static_cast<T>(2 * i + 3 * j + 13);
    }
    b_[i] = static_cast<T>(11 * i + 7);
  }
}

template <class T>
void Gauss<T>::random_generate() {
  srand(seed_);
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = static_cast<T>(rand() % 100 + 1) / static_cast<T>(rand() % 100 + 1);
    }
    b_[i] = static_cast<T>(rand() % 100 + 1) / static_cast<T>(rand() % 100 + 1);
  }
}

/**
 * Double
 */

template <>
std::string Gauss<double>::type_name() const {
  return "double";
}

/**
 * mpq
 */

template <>
std::string Gauss<mpq_class>::type_name() const {
  return "mpq_class";
}

template <>
void Gauss<mpq_class>::sequential_generate() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = mpq_class(2 * i + 3 * j + 13);
    }
    b_[i] = mpq_class(11 * i + 7);
  }
}

template <>
void Gauss<mpq_class>::random_generate() {
  srand(seed_);
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = mpq_class{rand() % 100 + 1, rand() % 100 + 1};
    }
    b_[i] = mpq_class{rand() % 100 + 1, rand() % 100 + 1};
  }
}

/**
 * mpf
 */

template <>
std::string Gauss<mpf_class>::type_name() const {
  return "mpf_class";
}

template class Gauss<double>;
template class Gauss<mpq_class>;
template class Gauss<mpf_class>;

}  // namespace dlinear
