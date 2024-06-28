/**
 * @file Tensor.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Tensor class.
 */
#pragma once

#include <istream>
#include <numeric>

#include "dlinear/libs/libeigen.h"
#include "dlinear/libs/libonnx.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/concepts.h"
#include "dlinear/util/definitions.h"
#include "dlinear/util/logging.h"

namespace dlinear::onnx {

class Tensor {
 public:
  explicit Tensor(std::initializer_list<std::int64_t> dims);
  explicit Tensor(std::vector<std::int64_t> dims);
  explicit Tensor(const ::onnx::TensorProto &tensor);
  explicit Tensor(const ::onnx::ValueInfoProto &value_info, const std::string &name);

  [[nodiscard]] const std::vector<std::int64_t> &dims() const { return dims_; }
  [[nodiscard]] const std::vector<Expression> &values() const { return values_; };
  [[nodiscard]] std::size_t size() const { return values_.size(); }

  [[nodiscard]] std::int64_t dim(std::size_t i) const;

  [[nodiscard]] bool Broadcastable(const Tensor &rhs) const;
  [[nodiscard]] bool SameDim(const Tensor &rhs) const;
  [[nodiscard]] bool Equal(const Tensor &rhs) const;

  [[nodiscard]] std::vector<std::int64_t> BroadcastDim(const Tensor &rhs) const;
  [[nodiscard]] std::vector<std::int64_t> BroadcastDim(const std::vector<std::int64_t> &dims) const;

  [[nodiscard]] Tensor Broadcast(const Tensor &rhs) const;
  [[nodiscard]] Tensor Broadcast(const std::vector<std::int64_t> &dims) const;

  Tensor &Flatten();
  Tensor &Flatten(std::int64_t axis);
  Tensor &Transpose();
  Tensor &Reshape(std::initializer_list<std::int64_t> dims);
  Tensor &Abs();
  Tensor &Piecewise(const std::function<Expression(Expression)> &f);
  [[nodiscard]] Tensor MatMul(const Tensor &tensor) const;

  template <IsAnyOf<int, std::int64_t> Dim, IsAnyOf<int, std::int64_t>... Dims>
  Expression &operator()(Dim row, Dims... dims) {
    if (sizeof...(dims) + 1 < dims_.size())
      DLINEAR_OUT_OF_RANGE_FMT("Expected number of dimensions >= {}, got {}", dims_.size(), sizeof...(dims) + 1);
    return const_cast<Expression &>(GetCore(row * GetDimOffset(0), 1, dims...));
  }
  template <IsAnyOf<int, std::int64_t> Dim, IsAnyOf<int, std::int64_t>... Dims>
  const Expression &operator()(Dim row, Dims... dims) const {
    if (sizeof...(dims) + 1 < dims_.size())
      DLINEAR_OUT_OF_RANGE_FMT("Expected number of dimensions >= {}, got {}", dims_.size(), sizeof...(dims) + 1);
    return GetCore(row * GetDimOffset(0), 1, dims...);
  }
  const Expression &operator()(const std::vector<std::int64_t>& dims) const;
  Expression &operator()(const std::vector<std::int64_t>& dims);

  std::vector<Formula> operator<(const Tensor &rhs) const;
  std::vector<Formula> operator<=(const Tensor &rhs) const;
  std::vector<Formula> operator>(const Tensor &rhs) const;
  std::vector<Formula> operator>=(const Tensor &rhs) const;
  std::vector<Formula> operator==(const Tensor &rhs) const;
  std::vector<Formula> operator!=(const Tensor &rhs) const;

  Expression &operator[](int index);
  const Expression &operator[](int index) const;
  Expression &operator[](std::size_t index);
  const Expression &operator[](std::size_t index) const;

  std::vector<Expression>::iterator begin() { return values_.begin(); }
  std::vector<Expression>::iterator end() { return values_.end(); }
  std::vector<Expression>::const_iterator cbegin() { return values_.cbegin(); }
  std::vector<Expression>::const_iterator cend() { return values_.cend(); }

  ARITHMETIC_OPERATORS(Tensor);
  GENERIC_ARITHMETIC_OPERATORS(Tensor, Expression &);

 private:
  const Expression &GetCore(const std::vector<std::int64_t>& dims) const;
  [[nodiscard]] std::int64_t GetDimOffset(std::size_t starting_dim) const;
  const Expression &GetCore(std::int64_t offset, std::int64_t) const { return values_[offset]; }
  template <IsAnyOf<int, std::int64_t> Dim, IsAnyOf<int, std::int64_t>... Dims>
  const Expression &GetCore(std::int64_t offset, std::int64_t dim_offset, Dim row, Dims... dims) const {
    if (row != 0 && static_cast<std::size_t>(dim_offset) >= dims_.size())
      DLINEAR_OUT_OF_RANGE_FMT("Max right idx of non 0 dimensions < {}, got {}", dims_.size(), dim_offset);
    if (row != 0 && row >= dims_[dim_offset])
      DLINEAR_OUT_OF_RANGE_FMT("Maximum dimension is {}, got {}", dims_[dim_offset], row);
    return GetCore(offset + row * GetDimOffset(dim_offset), dim_offset + 1, dims...);
  }

  std::vector<std::int64_t> dims_;
  std::vector<Expression> values_;
};

std::ostream &operator<<(std::ostream &os, const Tensor &matrix);

}  // namespace dlinear::onnx

OSTREAM_FORMATTER(dlinear::onnx::Tensor);
