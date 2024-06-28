/**
 * @file Tensor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Tensor class.
 */
#include "dlinear/parser/onnx/Tensor.h"

#include <fmt/core.h>

#include <execution>
#include <numeric>
#include <ostream>
#include <utility>

#include "dlinear/symbolic/literal.h"

namespace dlinear::onnx {

namespace {

inline std::vector<int64_t> get_dims(const ::onnx::ValueInfoProto &value_info) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have type");
  DLINEAR_ASSERT(value_info.type().has_tensor_type(), "ValueInfoProto must have tensor_type");
  DLINEAR_ASSERT(value_info.type().tensor_type().has_shape(), "ValueInfoProto must have shape");
  std::vector<int64_t> dims;
  dims.reserve(value_info.type().tensor_type().shape().dim_size());
  for (const ::onnx::TensorShapeProto_Dimension &dim : value_info.type().tensor_type().shape().dim()) {
    DLINEAR_ASSERT(dim.has_dim_value(), "ValueInfoProto must have a dim_value");
    DLINEAR_ASSERT(dim.dim_value() > 0, "All dimensions of a tensor must be >= 1");
    dims.push_back(dim.dim_value());
  }
  return dims;
}

inline std::vector<int64_t> get_dims(const ::onnx::TensorProto &tensor) {
  DLINEAR_ASSERT(tensor.dims_size() > 0, "Tensor must have at least a dimentsion");
  std::vector<int64_t> dims;
  dims.reserve(tensor.dims_size());
  for (const std::int64_t dim : tensor.dims()) {
    DLINEAR_ASSERT(dim > 0, "All dimensions of a tensor must be >= 1");
    dims.push_back(dim);
  }
  return dims;
}

inline std::int64_t size_from_dims(const std::vector<std::int64_t> &dims) {
  for (const std::int64_t dim : dims) {
    if (dim <= 0) DLINEAR_RUNTIME_ERROR("All dimensions of a tensor must be >= 1");
  }
  return std::reduce(std::execution::par_unseq, dims.begin(), dims.end(), 1, std::multiplies<std::int64_t>{});
}
inline std::int64_t size_from_dims(const std::initializer_list<std::int64_t> &dims) {
  for (const std::int64_t dim : dims) {
    if (dim <= 0) DLINEAR_RUNTIME_ERROR("All dimensions of a tensor must be >= 1");
  }
  return std::reduce(std::execution::par_unseq, dims.begin(), dims.end(), 1, std::multiplies<std::int64_t>{});
}
}  // namespace

Tensor::Tensor(std::initializer_list<std::int64_t> dims) : dims_{dims}, values_(size_from_dims(dims_)) {
  if (dims_.empty()) dims_.push_back(1);
  for (const std::int64_t dim : dims_) {
    if (dim <= 0) DLINEAR_RUNTIME_ERROR("All dimensions of a tensor must be >= 1");
  }
  DLINEAR_ASSERT(static_cast<std::size_t>(size_from_dims(dims_)) == values_.size(), "The size must be valid");
}

Tensor::Tensor(std::vector<std::int64_t> dims) : dims_{std::move(dims)}, values_(size_from_dims(dims_)) {
  if (dims_.empty()) dims_.push_back(1);
  for (const std::int64_t dim : dims_) {
    if (dim <= 0) DLINEAR_RUNTIME_ERROR("All dimensions of a tensor must be >= 1");
  }
  DLINEAR_ASSERT(static_cast<std::size_t>(size_from_dims(dims_)) == values_.size(), "The size must be valid");
}

Tensor::Tensor(const ::onnx::ValueInfoProto &value_info, const std::string &name)
    : dims_{get_dims(value_info)}, values_{} {
  const std::int64_t size = size_from_dims(dims_);
  DLINEAR_DEBUG_FMT("Dims {} -> Size: {}", dims_, size);
  values_.reserve(size);
  for (int64_t i = 0; i < size; i++) {
    values_.emplace_back(Variable(fmt::format("{}_{}", name.empty() ? value_info.name() : name, i)));
  }
  DLINEAR_ASSERT(static_cast<std::size_t>(size_from_dims(dims_)) == values_.size(), "The size must be valid");
}

Tensor::Tensor(const ::onnx::TensorProto &tensor) : dims_{get_dims(tensor)}, values_{} {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");

  const void *const raw_data = tensor.has_raw_data() ? tensor.raw_data().data() : nullptr;
  const std::int64_t size = size_from_dims(dims_);

  switch (tensor.data_type()) {
    case ::onnx::TensorProto_DataType::TensorProto_DataType_FLOAT:
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(raw_data == nullptr ? tensor.float_data(i) : static_cast<const float *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_DOUBLE:
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(raw_data == nullptr ? tensor.double_data(i) : static_cast<const double *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT64:
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(raw_data == nullptr ? tensor.uint64_data(i) : static_cast<const uint64_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT64:
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(raw_data == nullptr ? tensor.int64_data(i) : static_cast<const int64_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_BOOL:
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(raw_data == nullptr ? tensor.int32_data(i) : static_cast<const int32_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int8 data type");
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(static_cast<const int8_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT16:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int16 data type");
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(static_cast<const int16_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int32 data type");
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(static_cast<const int32_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint8 data type");
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(static_cast<const uint8_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint32 data type");
      for (int i = 0; i < size; ++i) {
        values_.emplace_back(static_cast<const uint32_t *>(raw_data)[i]);
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UNDEFINED:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported data type: {}", tensor.data_type());
  }
}

std::int64_t Tensor::dim(std::size_t i) const {
  if (i >= dims_.size()) return 1;
  return dims_[i];
}

bool Tensor::Broadcastable(const Tensor &rhs) const {
  const int min_size = static_cast<int>(std::min(dims_.size(), rhs.dims_.size()));
  for (int i = 0; i < min_size; i++) {
    if (dims_.rbegin()[i] != rhs.dims_.rbegin()[i] && dims_.rbegin()[i] != 1 && rhs.dims_.rbegin()[i] != 1)
      return false;
  }
  return true;
}

std::vector<std::int64_t> Tensor::BroadcastDim(const Tensor &rhs) const { return BroadcastDim(rhs.dims_); }
std::vector<std::int64_t> Tensor::BroadcastDim(const std::vector<std::int64_t> &dims) const {
  std::vector<std::int64_t> new_dims;
  const int max_size = static_cast<int>(std::max(dims_.size(), dims.size()));
  new_dims.reserve(max_size);
  for (int i = 0; i < max_size; i++) {
    const std::int64_t dim = static_cast<std::size_t>(i) < dims_.size() ? dims_.rbegin()[i] : 1;
    const std::int64_t rhs_dim = static_cast<std::size_t>(i) < dims.size() ? dims.rbegin()[i] : 1;
    new_dims.push_back(std::max(dim, rhs_dim));
  }
  return new_dims;
}

bool Tensor::SameDim(const Tensor &rhs) const {
  if (values_.size() != rhs.size()) return false;
  return dims_ == rhs.dims_;
}

bool Tensor::Equal(const Tensor &rhs) const { return values_ == rhs.values_ && dims_ == rhs.dims_; }

Tensor Tensor::Broadcast(const Tensor &rhs) const { return Broadcast(rhs.dims_); }
Tensor Tensor::Broadcast(const std::vector<std::int64_t> &dims) const {
  if (dims_ == dims) return Tensor{*this};
  std::vector<std::int64_t> old_dims;
  old_dims.reserve(dims.size());
  std::size_t diff = dims.size() - dims_.size();
  for (std::size_t i = 0; i < dims.size(); i++) old_dims.push_back(i < diff ? 1 : dims_[i - diff]);

  Tensor new_tensor{dims};
  for (std::size_t i = 0; i < dims.size(); i++) {
    const std::int64_t idx = static_cast<std::int64_t>(dims.size() - i) - 1;
    if (old_dims[idx] == dims[idx]) continue;
    if (old_dims[idx] == 1) {
      for (std::int64_t j = 1; j < new_tensor.dims_[idx] - 1; j++) {
        new_tensor(j, 0l) = (*this)(0l, 0l);
      }
      new_tensor.dims_[idx] = dims[idx];
    } else if (dims[idx] == 1) {
      for (std::int64_t j = 1; j < new_tensor.dims_[idx] - 1; j++) {
        new_tensor(j, 0l) = (*this)(j, 0l);
      }
    } else {
      DLINEAR_OUT_OF_RANGE("Invalid broadcast");
    }
  }
  return new_tensor;
}

Tensor &Tensor::Flatten() {
  dims_.clear();
  dims_.push_back(static_cast<std::int64_t>(values_.size()));
  return *this;
}
Tensor &Tensor::Flatten(const std::int64_t axis) {
  if (axis < 0 || axis >= static_cast<std::int64_t>(dims_.size()))
    DLINEAR_OUT_OF_RANGE_FMT("Invalid axis. Must be in [{}, {}]", 0, dims_.size());
  const std::int64_t rows =
      std::reduce(std::execution::par_unseq, dims_.begin(), dims_.begin() + axis, 1, std::multiplies<std::int64_t>{});
  const std::int64_t cols =
      std::reduce(std::execution::par_unseq, dims_.begin() + axis, dims_.end(), 1, std::multiplies<std::int64_t>{});
  dims_.clear();
  dims_.push_back(rows);
  dims_.push_back(cols);
  return *this;
}

Tensor &Tensor::Reshape(std::initializer_list<std::int64_t> dims) {
  if (size_from_dims(dims) != size_from_dims(dims_)) DLINEAR_OUT_OF_RANGE("Old size is not compatible with new one");
  dims_.clear();
  for (const std::int64_t dim : dims) dims_.push_back(dim);
  return *this;
}

Tensor &Tensor::Transpose() {
  if (dims_.size() > 2) DLINEAR_RUNTIME_ERROR("Transpose can only be applied to Matrices and Vectors");

  // In-place transpose
  std::vector<bool> visited(values_.size(), false);
  const auto size = static_cast<std::int64_t>(values_.size() - 1);
  for (auto cycle = values_.begin() + 1; cycle != values_.cend(); cycle++) {
    if (visited[cycle - values_.begin()]) continue;
    std::int64_t a = std::distance(values_.begin(), cycle);
    do {
      a = a == size ? size : (dim(0) * a) % size;
      (values_.begin() + a)->Swap(*cycle);
      visited[a] = true;
    } while ((values_.cbegin() + a) != cycle);
  }

  // Invert dimensions
  const std::int64_t temp = dim(1);
  if (dims_.size() == 2) {
    dims_[1] = dims_[0];
  } else {
    dims_.push_back(dims_[0]);
  }
  dims_[0] = temp;
  return *this;
}

Tensor &Tensor::Piecewise(const std::function<Expression(Expression)> &f) {
  for (Expression &e : values_) e = f(e);
  return *this;
}

Tensor Tensor::MatMul(const Tensor &rhs) const {
  if (dims_.size() > 2 || rhs.dims_.size() > 2)
    DLINEAR_RUNTIME_ERROR("MatMul can only be applied to Matrices and Vectors");
  if (dim(1) != rhs.dim(0)) {
    if (dim(0) == rhs.dim(0)) return Tensor{*this}.Transpose().MatMul(rhs);
    if (dim(1) == rhs.dim(1)) return MatMul(Tensor{rhs}.Transpose());
    DLINEAR_RUNTIME_ERROR_FMT("Invalid MatMul between [{}x{}] and [{}x{}]", dim(0), dim(1), rhs.dim(0), rhs.dim(1));
  }
  DLINEAR_ASSERT(dim(0) > 0 && dim(1) > 0 && rhs.dim(0) > 0 && rhs.dim(1) > 0, "All dimensions must be > 0");
  Tensor new_tensor{dim(0), rhs.dim(1)};
  for (std::int64_t row = 0; row < dim(0); row++) {
    for (std::int64_t col = 0; col < rhs.dim(1); col++) {
      new_tensor(row, col) = (*this)(row, 0l) * rhs(0l, col);
      for (std::int64_t inner = 1; inner < dim(1); inner++) {
        new_tensor(row, col) += (*this)(row, inner) * rhs(inner, col);
      }
    }
  }
  return new_tensor;
}

Tensor &Tensor::operator+=(const Expression &rhs) {
  for (Expression &e : values_) e += rhs;
  return *this;
}
Tensor &Tensor::operator-=(const Expression &rhs) {
  for (Expression &e : values_) e -= rhs;
  return *this;
}
Tensor &Tensor::operator*=(const Expression &rhs) {
  for (Expression &e : values_) e *= rhs;
  return *this;
}
Tensor &Tensor::operator/=(const Expression &rhs) {
  for (Expression &e : values_) e /= rhs;
  return *this;
}

Tensor &Tensor::operator+=(const Tensor &rhs) {
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  if (rhs.size() == 1) return *this += rhs[0];
  for (std::size_t i = 0; i < values_.size(); i++) values_[i] += rhs[i];
  return *this;
}
Tensor &Tensor::operator-=(const Tensor &rhs) {
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  if (rhs.size() == 1) return *this -= rhs[0];
  for (std::size_t i = 0; i < values_.size(); i++) values_[i] -= rhs[i];
  return *this;
}
Tensor &Tensor::operator*=(const Tensor &rhs) {
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  if (rhs.size() == 1) return *this *= rhs[0];
  for (std::size_t i = 0; i < values_.size(); i++) values_[i] *= rhs[i];
  return *this;
}
Tensor &Tensor::operator/=(const Tensor &rhs) {
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  if (rhs.size() == 1) return *this /= rhs[0];
  for (std::size_t i = 0; i < values_.size(); i++) values_[i] /= rhs[i];
  return *this;
}

std::vector<Formula> Tensor::operator<(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] < rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator<=(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] <= rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator>(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] > rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator>=(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] >= rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator==(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] == rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator!=(const Tensor &rhs) const {
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  if (!Broadcastable(rhs)) DLINEAR_OUT_OF_RANGE("The two tensors must have the same dimensions");
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_[i] != rhs[i]);
  return formulas;
}

Expression &Tensor::operator[](const int index) { return values_.at(index); }
const Expression &Tensor::operator[](const int index) const { return values_.at(index); }
Expression &Tensor::operator[](const std::size_t index) { return values_.at(index); }
const Expression &Tensor::operator[](const std::size_t index) const { return values_.at(index); }

std::int64_t Tensor::GetDimOffset(std::size_t dim_offset) const {
  if (dim_offset >= dims_.size() - 1) return 1;
  return std::reduce(std::execution::par_unseq, dims_.begin() + static_cast<std::int64_t>(dim_offset) + 1, dims_.end(),
                     1, std::multiplies<std::int64_t>{});
}
const Expression &Tensor::operator()(const std::vector<std::int64_t>& dims) const { return GetCore(dims); }
Expression &Tensor::operator()(const std::vector<std::int64_t>& dims) { return const_cast<Expression &>(GetCore(dims)); }
const Expression &Tensor::GetCore(const std::vector<std::int64_t>& dims) const {
  if (dims.size() < dims_.size())
    DLINEAR_OUT_OF_RANGE_FMT("Expected number of dimensions >= {}, got {}", dims_.size(), dims.size());
  for (std::size_t i = dims_.size(); i < dims.size(); i++) {
    if (dims[i] != 0) DLINEAR_OUT_OF_RANGE_FMT("Max right idx of non 0 dimensions < {}, got {}", dims_.size(), i);
  }
  std::int64_t offset = 0;
  for (std::size_t i = 0; i < dims.size(); i++) {
    offset += dims[i] * GetDimOffset(i);
  }
  return values_[offset];
}

std::ostream &operator<<(std::ostream &os, const Tensor &tensor) {
  os << fmt::format("Tensor({})", tensor.dims());
  std::vector<std::int64_t> indices(tensor.dims().size(), 0);
  std::vector<std::int64_t> counters(tensor.dims().size(), 0);
  for (std::size_t i = 0; i < tensor.dims().size(); i++) {
    const std::size_t idx = indices.size() - i - 1;
    indices[idx] = i == 0 ? tensor.dims()[idx] : tensor.dims()[idx] * indices[idx + 1];
  }

  std::string element_tab(tensor.dims().size(), '\t');

  os << "\n";
  for (std::size_t i = 0; i < tensor.dims().size(); i++) {
    os << std::string(i, '\t') << "[\n";
  }
  for (std::size_t i = 0; i < tensor.size(); i++) {
    os << element_tab << tensor[i];
    for (std::size_t j = 0; j < indices.size(); j++) {
      const std::size_t idx = indices.size() - j - 1;
      if (++(counters[idx]) == indices[idx]) {
        counters[idx] = 0;
        os << "\n" << std::string(idx, '\t') << "]";
        if (i == tensor.size() - 1) continue;
        os << "\n" << std::string(idx, '\t') << "[\n";
      }
    }
  }
  return os;
}

}  // namespace dlinear::onnx
