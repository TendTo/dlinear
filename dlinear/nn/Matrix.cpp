/**
 * @file Matrix.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Matrix class.
 */
#include "Matrix.h"

#include <fmt/core.h>

#include <iostream>
#include <ostream>

#include "dlinear/symbolic/literal.h"

namespace dlinear {

namespace {
inline int64_t get_row(const onnx::ValueInfoProto &value_info) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have type");
  DLINEAR_ASSERT(value_info.type().has_tensor_type(), "ValueInfoProto must have tensor_type");
  DLINEAR_ASSERT(value_info.type().tensor_type().has_shape(), "ValueInfoProto must have shape");
  DLINEAR_ASSERT(value_info.type().tensor_type().shape().dim_size() > 0,
                 "ValueInfoProto must have at least one dimension");
  DLINEAR_ASSERT(value_info.type().tensor_type().shape().dim(0).has_dim_value(),
                 "ValueInfoProto must have a dim_value");
  return value_info.type().tensor_type().shape().dim(0).dim_value();
}

inline int64_t get_col(const onnx::ValueInfoProto &value_info) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have type");
  DLINEAR_ASSERT(value_info.type().has_tensor_type(), "ValueInfoProto must have tensor_type");
  DLINEAR_ASSERT(value_info.type().tensor_type().has_shape(), "ValueInfoProto must have shape");
  return value_info.type().tensor_type().shape().dim_size() > 1
             ? value_info.type().tensor_type().shape().dim(1).dim_value()
             : 1;
}
}  // namespace

Matrix::Matrix(const int64_t rows, const int64_t cols) : rows_{rows}, cols_{cols}, matrix_(rows, cols) {
  DLINEAR_ASSERT(rows > 0, "Rows must be positive");
  DLINEAR_ASSERT(cols > 0, "Cols must be positive");
}
Matrix::Matrix(const int rows, const int cols) : rows_{rows}, cols_{cols}, matrix_(rows, cols) {
  DLINEAR_ASSERT(rows > 0, "Rows must be positive");
  DLINEAR_ASSERT(cols > 0, "Cols must be positive");
}

Matrix::Matrix(const onnx::ValueInfoProto &value_info)
    : rows_{get_row(value_info)}, cols_{get_col(value_info)}, matrix_{rows_, cols_} {
  DLINEAR_ASSERT(rows_ > 0, "Rows must be positive");
  DLINEAR_ASSERT(cols_ > 0, "Cols must be positive");
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");

  const int64_t num_variables = rows_ * cols_;
  for (int64_t i = 0; i < num_variables; i++) {
    matrix_.data()[i] = Expression{Variable(fmt::format("{}[{}]", value_info.name(), i))};
  }
}

Matrix::Matrix(const onnx::TensorProto &tensor)
    : rows_{tensor.dims(0)}, cols_{tensor.dims_size() > 1 ? tensor.dims(1) : 1}, matrix_(rows_, cols_) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");

  const void *const raw_data = tensor.has_raw_data() ? tensor.raw_data().data() : nullptr;
  int64_t size = 1;
  if (raw_data != nullptr) {
    for (const int64_t dim : tensor.dims()) {
      size *= dim;
      DLINEAR_ASSERT(dim > 0, "Dimensions must be positive");
    }
  }
  DLINEAR_ASSERT(size == matrix_.size(), "Size mismatch");

  switch (tensor.data_type()) {
    case onnx::TensorProto_DataType::TensorProto_DataType_FLOAT:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] =
            Expression{raw_data == nullptr ? tensor.float_data(i) : static_cast<const float *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_DOUBLE:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] =
            Expression{raw_data == nullptr ? tensor.double_data(i) : static_cast<const double *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT64:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] =
            Expression{raw_data == nullptr ? tensor.uint64_data(i) : static_cast<const uint64_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT64:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] =
            Expression{raw_data == nullptr ? tensor.int64_data(i) : static_cast<const int64_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_BOOL:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] =
            Expression{raw_data == nullptr ? tensor.int32_data(i) : static_cast<const int32_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int8 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = Expression{static_cast<const int8_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT16:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int16 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = Expression{static_cast<const int16_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int32 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = Expression{static_cast<const int32_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint8 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = Expression{static_cast<const uint8_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint32 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = Expression{static_cast<const uint32_t *>(raw_data)[i]};
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UNDEFINED:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported data type: {}", tensor.data_type());
  }
}

Matrix &Matrix::operator+=(const Matrix &rhs) {
  matrix_ += rhs.matrix_;
  rows_ = matrix_.rows();
  cols_ = matrix_.cols();
  return *this;
}

Matrix &Matrix::operator-=(const Matrix &rhs) {
  matrix_ -= rhs.matrix_;
  rows_ = matrix_.rows();
  cols_ = matrix_.cols();
  return *this;
}

Matrix &Matrix::operator*=(const Matrix &rhs) {
  matrix_ *= rhs.matrix_;
  rows_ = matrix_.rows();
  cols_ = matrix_.cols();
  return *this;
}

Matrix &Matrix::operator/=(const Matrix &rhs) {
  matrix_.array() /= rhs.matrix_.array();
  rows_ = matrix_.rows();
  cols_ = matrix_.cols();
  return *this;
}

Expression &Matrix::operator()(int row, int col) {
  DLINEAR_ASSERT(row >= 0 && row < rows_, "Row index out of bounds");
  DLINEAR_ASSERT(col >= 0 && col < cols_, "Col index out of bounds");
  return matrix_(row, col);
}
const Expression &Matrix::operator()(int row, int col) const {
  DLINEAR_ASSERT(row >= 0 && row < rows_, "Row index out of bounds");
  DLINEAR_ASSERT(col >= 0 && col < cols_, "Col index out of bounds");
  return matrix_(row, col);
}
Expression &Matrix::operator[](int index) {
  DLINEAR_ASSERT(index >= 0 && index < matrix_.size(), "Index out of bounds");
  return matrix_.data()[index];
}
const Expression &Matrix::operator[](int index) const {
  DLINEAR_ASSERT(index >= 0 && index < matrix_.size(), "Index out of bounds");
  return matrix_.data()[index];
}

std::ostream &operator<<(std::ostream &os, const Matrix &matrix) {
  os << "Matrix(" << matrix.rows() << ", " << matrix.cols() << ")\n";
  return os << "[" << matrix.matrix() << "]";
}

}  // namespace dlinear
