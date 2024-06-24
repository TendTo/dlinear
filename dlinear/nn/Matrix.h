/**
 * @file Matrix.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Matrix class.
 */
#pragma once

#include <istream>

#include "dlinear/libs/libeigen.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libonnx.h"

namespace dlinear {

class Matrix {
 public:
  using MatrixE = Eigen::Matrix<mpq_class, Eigen::Dynamic, Eigen::Dynamic>;
  explicit Matrix(const onnx::TensorProto &tensor);
  Matrix(int rows, int cols);

  [[nodiscard]] int64_t rows() const { return rows_; }
  [[nodiscard]] int64_t cols() const { return cols_; }
  [[nodiscard]] const MatrixE &matrix() const { return matrix_; }

 private:
  int64_t rows_;
  int64_t cols_;
  MatrixE matrix_;
};

std::ostream &operator<<(std::ostream &os, const Matrix &matrix);

}  // namespace dlinear
