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

#include "dlinear/libs/libonnx.h"
#include "dlinear/libs/libxtensor.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/concepts.h"
#include "dlinear/util/definitions.h"
#include "dlinear/util/logging.h"

namespace dlinear::onnx {

class Tensor {
 public:
  Tensor(std::initializer_list<std::int64_t> dims);
  explicit Tensor(std::int64_t value);
  explicit Tensor(float value);
  explicit Tensor(const std::vector<std::int64_t> &dims);
  explicit Tensor(xt::xarray<Expression> values);
  explicit Tensor(const ::onnx::TensorProto &tensor);
  explicit Tensor(const ::onnx::ValueInfoProto &value_info, const std::string &name);

  [[nodiscard]] const xt::xarray<Expression> &values() const { return values_; };
  [[nodiscard]] std::size_t size() const { return values_.size(); }
  [[nodiscard]] std::size_t ndim() const { return values_.dimension(); }
  [[nodiscard]] std::vector<std::int64_t> dims() const;

  [[nodiscard]] std::int64_t dim(std::size_t i) const;

  [[nodiscard]] bool SameDim(const Tensor &rhs) const;
  [[nodiscard]] bool Equal(const Tensor &rhs) const;

  Tensor &Flatten();
  Tensor &Flatten(std::int64_t axis);
  Tensor &Transpose();
  Tensor &Reshape(std::initializer_list<std::int64_t> dims);
  Tensor &Unsqueeze(const Tensor &tensor);
  Tensor &Abs();
  Tensor &Piecewise(const std::function<Expression(Expression)> &f);
  Tensor &Slice(const std::vector<std::int64_t> &starts, const std::vector<std::int64_t> &ends,
                const std::vector<std::int64_t> &axes = {}, const std::vector<std::int64_t> &steps = {});
  Tensor &Slice(const Tensor &starts, const Tensor &ends, const Tensor &axes = {}, const Tensor &steps = {});
  Tensor Concat(const Tensor &rhs, std::int64_t axis);
  Tensor Concat(const std::vector<Tensor> &rhs, std::int64_t axis);
  Tensor Gather(const Tensor &indices, std::int64_t axis);
  [[nodiscard]] Tensor MatMul(const Tensor &tensor) const;
  [[nodiscard]] Tensor Convolution(const Tensor &w, const std::string &auto_pad,
                                   const std::vector<std::int64_t> &dilations, std::int64_t group,
                                   const std::vector<std::int64_t> &kernel_shape, const std::vector<std::int64_t> &pads,
                                   const std::vector<std::int64_t> &strides) const;
  [[nodiscard]] Tensor Pad(const std::vector<std::int64_t> &pads);

  template <IsAnyOf<int, std::int64_t, std::size_t>... Dims>
  Expression &operator()(Dims... dims) {
    return values_(dims...);
  }
  template <IsAnyOf<int, std::int64_t, std::size_t>... Dims>
  const Expression &operator()(Dims... dims) const {
    return values_(dims...);
  }
  Expression &operator()(std::initializer_list<std::int64_t> dims);
  const Expression &operator()(std::initializer_list<std::int64_t> dims) const;

  std::vector<Formula> operator<(const Tensor &rhs) const;
  std::vector<Formula> operator<=(const Tensor &rhs) const;
  std::vector<Formula> operator>(const Tensor &rhs) const;
  std::vector<Formula> operator>=(const Tensor &rhs) const;
  std::vector<Formula> operator==(const Tensor &rhs) const;
  std::vector<Formula> operator!=(const Tensor &rhs) const;

  explicit operator std::vector<std::int64_t>() const;
  explicit operator std::vector<double>() const;

  Expression &operator[](int index);
  const Expression &operator[](int index) const;
  Expression &operator[](std::size_t index);
  const Expression &operator[](std::size_t index) const;

  auto begin() { return values_.begin(); }
  auto end() { return values_.end(); }
  [[nodiscard]] auto begin() const { return values_.begin(); }
  [[nodiscard]] auto end() const { return values_.end(); }
  [[nodiscard]] auto cbegin() const { return values_.cbegin(); }
  [[nodiscard]] auto cend() const { return values_.cend(); }

  ARITHMETIC_OPERATORS(Tensor);
  GENERIC_ARITHMETIC_OPERATORS(Tensor, Expression &);

 private:
  [[nodiscard]] std::size_t ComputeOffset(std::initializer_list<std::int64_t> dims) const;
  [[nodiscard]] std::size_t ComputeOffset(const std::int64_t *dims, std::size_t size) const;

  xt::xarray<Expression> values_;
};

std::ostream &operator<<(std::ostream &os, const Tensor &matrix);
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression> &values);
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression>::shape_type &shape);

}  // namespace dlinear::onnx
