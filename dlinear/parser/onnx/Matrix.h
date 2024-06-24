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
#include "dlinear/libs/libonnx.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/definitions.h"
#include "dlinear/util/logging.h"

namespace dlinear {

class Matrix {
 public:
  using MatrixE = Eigen::Matrix<Expression, Eigen::Dynamic, Eigen::Dynamic>;
  Matrix(int rows, int cols);
  Matrix(int64_t rows, int64_t cols);
  explicit Matrix(const ::onnx::TensorProto &tensor);
  explicit Matrix(const onnx::ValueInfoProto &value_info, const std::string& name = "");

  [[nodiscard]] int64_t rows() const { return rows_; }
  [[nodiscard]] int64_t cols() const { return cols_; }
  [[nodiscard]] int64_t size() const { return matrix_.size(); }
  [[nodiscard]] const MatrixE &matrix() const { return matrix_; }

  Expression &operator()(int row, int col);
  const Expression &operator()(int row, int col) const;
  Expression &operator[](int index);
  const Expression &operator[](int index) const;

  ARITHMETIC_OPERATORS(Matrix);

  auto begin() { return matrix_.data(); }
  auto end() { return matrix_.data() + matrix_.size(); }

 private:
  int64_t rows_;
  int64_t cols_;
  MatrixE matrix_;
};

std::ostream &operator<<(std::ostream &os, const Matrix &matrix);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Matrix);
