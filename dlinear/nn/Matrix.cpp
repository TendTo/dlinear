/**
 * @file Matrix.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Matrix class.
 */
#include "Matrix.h"

#include <iostream>
#include <ostream>

namespace dlinear {

namespace {
inline int get_dim() { return 0; }
}  // namespace

Matrix::Matrix(const int rows, const int cols) : rows_{rows}, cols_{cols}, matrix_(rows, cols) {
  DLINEAR_ASSERT(rows > 0, "Rows must be positive");
  DLINEAR_ASSERT(cols > 0, "Cols must be positive");
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
        matrix_.data()[i] = raw_data == nullptr ? tensor.float_data(i) : static_cast<const float *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_DOUBLE:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = raw_data == nullptr ? tensor.double_data(i) : static_cast<const double *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT64:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = raw_data == nullptr ? tensor.uint64_data(i) : static_cast<const uint64_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT64:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = raw_data == nullptr ? tensor.int64_data(i) : static_cast<const int64_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_BOOL:
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = raw_data == nullptr ? tensor.int32_data(i) : static_cast<const int32_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int8 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = static_cast<const int8_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT16:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int16 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = static_cast<const int16_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int32 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = static_cast<const int32_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint8 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = static_cast<const uint8_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint32 data type");
      for (int i = 0; i < size; ++i) {
        matrix_.data()[i] = static_cast<const uint32_t *>(raw_data)[i];
      }
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UNDEFINED:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported data type: {}", tensor.data_type());
  }
}

std::ostream &operator<<(std::ostream &os, const Matrix &matrix) {
  os << "Matrix(" << matrix.rows() << ", " << matrix.cols() << ")\n";
  os << matrix.matrix();
  return os;
}

}  // namespace dlinear
