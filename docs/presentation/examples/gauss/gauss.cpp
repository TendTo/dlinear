#include "gauss.h"

#include <gmpxx.h>

#include <iostream>
#include <random>

namespace dlinear {

template <>
Gauss<double>::Gauss(size_t size, size_t seed) : size_{size}, permutation_{nullptr}, seed_{seed} {
  A_ = new double *[size_];
  for (size_t i = 0; i < size_; ++i) {
    A_[i] = new double[size_];
  }
  b_ = new double[size_];
}

template <>
Gauss<double>::~Gauss() {
  for (size_t i = 0; i < size_; ++i) {
    delete[] A_[i];
  }
  delete[] A_;
  delete[] b_;
}

template <>
std::string Gauss<double>::type_name() const {
  return "double";
}

template <>
void Gauss<double>::sequential_generate() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = static_cast<double>(2 * i + 3 * j + 13);
    }
    b_[i] = static_cast<double>(11 * i + 7);
  }
}

template <>
void Gauss<double>::random_generate() {
  srand(seed_);
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = static_cast<double>(rand() % 100 + 1) / static_cast<double>(rand() % 100 + 1);
    }
    b_[i] = static_cast<double>(rand() % 100 + 1) / static_cast<double>(rand() % 100 + 1);
  }
}

template <>
void Gauss<double>::set_A(double *A[]) {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = A[i][j];
    }
  }
}

template <>
void Gauss<double>::set_A(size_t i, double row[]) {
  for (size_t j = 0; j < size_; ++j) {
    A_[i][j] = row[j];
  }
}

template <>
void Gauss<double>::set_b(double value[]) {
  for (size_t i = 0; i < size_; ++i) {
    b_[i] = value[i];
  }
}

template <>
std::unique_ptr<double[]> Gauss<double>::backward_substitution() {
  std::unique_ptr<double[]> x{std::make_unique<double[]>(size_)};
  for (size_t i = size_ - 1; i < size_; --i) {
    double &x_i = permutation_ == nullptr ? x[i] : x[permutation_[i]];
    if (A_[i][i] == 0) throw std::runtime_error("Indeterminate system");
    x_i = b_[i];
    for (size_t j = i + 1; j < size_; ++j) {
      const double &x_j = permutation_ == nullptr ? x[j] : x[permutation_[j]];
      x_i -= A_[i][j] * x_j;
    }
    x_i /= A_[i][i];
  }
  return x;
}

template <>
std::unique_ptr<double[]> Gauss<double>::solve() {
  forward_elimination();
  return backward_substitution();
}

template <>
void Gauss<double>::print_A() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      std::cout << A_[i][j] << " ";
    }
    std::cout << std::endl;
  }
}

template <>
void Gauss<double>::print_b() {
  for (size_t i = 0; i < size_; ++i) {
    std::cout << b_[i] << std::endl;
  }
}

template <>
std::ostream &operator<<(std::ostream &os, const Gauss<double> &gauss) {
  for (size_t i = 0; i < gauss.size(); ++i) {
    for (size_t j = 0; j < gauss.size(); ++j) {
      std::cout << gauss.A()[i][j] << " ";
    }
    std::cout << "\t | " << gauss.b()[i] << std::endl;
  }
  return os;
}

/**
 * GMP
 */

template <>
Gauss<mpq_class>::Gauss(size_t size, size_t seed) : size_{size}, permutation_{nullptr}, seed_{seed} {
  A_ = new mpq_class *[size_];
  for (size_t i = 0; i < size_; ++i) {
    A_[i] = new mpq_class[size_];
  }
  b_ = new mpq_class[size_];
}

template <>
Gauss<mpq_class>::~Gauss() {
  for (size_t i = 0; i < size_; ++i) {
    delete[] A_[i];
  }
  delete[] A_;
  delete[] b_;
}

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

template <>
void Gauss<mpq_class>::set_A(mpq_class *A[]) {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      A_[i][j] = A[i][j];
    }
  }
}

template <>
void Gauss<mpq_class>::set_A(size_t i, mpq_class row[]) {
  for (size_t j = 0; j < size_; ++j) {
    A_[i][j] = row[j];
  }
}

template <>
void Gauss<mpq_class>::set_b(mpq_class value[]) {
  for (size_t i = 0; i < size_; ++i) {
    b_[i] = value[i];
  }
}

template <>
std::unique_ptr<mpq_class[]> Gauss<mpq_class>::backward_substitution() {
  std::unique_ptr<mpq_class[]> x{std::make_unique<mpq_class[]>(size_)};
  for (size_t i = size_ - 1; i < size_; --i) {
    mpq_class &x_i = permutation_ == nullptr ? x[i] : x[permutation_[i]];
    if (A_[i][i] == 0) throw std::runtime_error("Indeterminate system");
    x_i = b_[i];
    for (size_t j = i + 1; j < size_; ++j) {
      const mpq_class &x_j = permutation_ == nullptr ? x[j] : x[permutation_[j]];
      x_i -= A_[i][j] * x_j;
    }
    x_i /= A_[i][i];
  }
  return x;
}

template <>
std::unique_ptr<mpq_class[]> Gauss<mpq_class>::solve() {
  forward_elimination();
  return backward_substitution();
}

template <>
void Gauss<mpq_class>::print_A() {
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = 0; j < size_; ++j) {
      std::cout << A_[i][j] << " ";
    }
    std::cout << std::endl;
  }
}

template <>
void Gauss<mpq_class>::print_b() {
  for (size_t i = 0; i < size_; ++i) {
    std::cout << b_[i] << std::endl;
  }
}

template <>
std::ostream &operator<<(std::ostream &os, const Gauss<mpq_class> &gauss) {
  for (size_t i = 0; i < gauss.size(); ++i) {
    for (size_t j = 0; j < gauss.size(); ++j) {
      std::cout << gauss.A()[i][j] << " ";
    }
    std::cout << "\t | " << gauss.b()[i] << std::endl;
  }

  return os;
}

}  // namespace dlinear
