/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Tensor class.
 */
#pragma once

#include <istream>
#include <numeric>

#include "dlinear/libs/libonnx.h"
#include "dlinear/libs/libxtensor.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/concepts.h"
#include "dlinear/util/definitions.h"

namespace dlinear::onnx {

[[maybe_unused]] const xt::xarray<Expression> unused_;

class Tensor {
 public:
  using ImageView = decltype(xt::view(unused_, std::size_t{}, std::size_t{}));
  using KernelView = decltype(xt::view(unused_, std::size_t{}, std::size_t{}, xt::xrange(0l, 0l), xt::xrange(0l, 0l)));

  /**
   * Construct a tensor with the given @p dims.
   * @param dims dimensions of the tensor
   */
  Tensor(std::initializer_list<std::int64_t> dims);
  /**
   * Construct a tensor with the given @p value.
   * @param value single value of the tensor
   */
  explicit Tensor(std::int64_t value);
  /**
   * Construct a tensor with the given @p value.
   * @param value single value of the tensor
   */
  explicit Tensor(float value);
  /**
   * Construct a tensor with the given @p dims.
   * @param dims dimensions of the tensor
   */
  explicit Tensor(const std::vector<std::int64_t> &dims);
  /**
   * Construct a tensor with the given @p values.
   * @param values xarray of expressions
   */
  explicit Tensor(xt::xarray<Expression> values);
  /**
   * Construct a tensor with the given @p tensor.
   * @param tensor tensor proto from the ONNX model
   */
  explicit Tensor(const ::onnx::TensorProto &tensor);
  /**
   * Construct a tensor with the given @p value_info.
   * @param value_info value info proto from the ONNX model
   * @param name prefix name to give to the variables in the tensor
   */
  explicit Tensor(const ::onnx::ValueInfoProto &value_info, const std::string &name);

  /** @getter{values, tensor} */
  [[nodiscard]] const xt::xarray<Expression> &values() const { return values_; }
  /** @getter{size, tensor} */
  [[nodiscard]] std::size_t size() const { return values_.size(); }
  /** @getter{number of dimensions, tensor} */
  [[nodiscard]] std::size_t ndim() const { return values_.dimension(); }
  /** @getter{dimensions, tensor} */
  [[nodiscard]] std::vector<std::int64_t> dims() const;

  /**
   * Get the dimension at index @p i of the tensor.
   *
   * If the dimension requested is not present, it will return 1.
   * @param i index of the dimension
   * @return the dimension at the given index
   * @return 1 if the @p i is out of bounds
   */
  [[nodiscard]] std::int64_t dim(std::size_t i) const;

  /**
   * Check whether the two tensors have the same dimension.
   * @param o tensor to compare with
   * @return true if the two tensors have the same dimension
   * @return false if the two tensors have different dimensions
   */
  [[nodiscard]] bool SameDim(const Tensor &o) const;
  /** @equal_to{tensor} */
  [[nodiscard]] bool Equal(const Tensor &o) const;

  /**
   * Flatten the tensor along the given @p axis
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Flatten.html).
   * @param axis axis to flatten along
   * @return reference to the tensor
   */
  Tensor &Flatten(std::int64_t axis);
  /**
   * Transpose the tensor with the given @p perm.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Transpose.html).
   * @param perm permutation of the dimensions
   * @return reference to the tensor
   */
  Tensor &Transpose(const std::vector<std::int64_t> &perm = {});
  /**
   * Reshape the tensor with the given @p dims.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Reshape.html).
   * @param dims dimensions to reshape the tensor
   * @return reference to the tensor
   */
  Tensor &Reshape(std::initializer_list<std::int64_t> dims);
  /**
   * Reshape the tensor with the given @p tensor_dim.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Reshape.html).
   * @param tensor_dim tensor containing the dimensions to reshape the tensor
   * @param allow_zero whether to allow zero in the dimensions
   * @return reference to the tensor
   */
  Tensor &Reshape(const Tensor &tensor_dim, bool allow_zero);
  /**
   * Insert single-dimensional entries to the shape of an input tensor.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Unsqueeze.html).
   * @param axes axes along which the tensor will be unsqueezed
   * @return reference to the tensor
   */
  Tensor &Unsqueeze(const Tensor &axes);
  /**
   * Apply the Abs function to the tensor.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Abs.html).
   * @return reference to the tensor
   */
  Tensor &Abs();
  /**
   * Apply the @p f function to each element of the tensor.
   * @param f function to apply to each element
   * @return reference to the tensor
   */
  Tensor &Elementwise(const std::function<Expression(Expression)> &f);
  /**
   * Slice the tensor with the given @p starts, @p ends, @p axes, and @p steps.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Slice.html).
   * @param starts 1-D tensor of starting indices of corresponding axis in @p axes
   * @param ends 1-D tensor of ending indices (exclusive) of corresponding axis in @p axes
   * @param axes 1-D tensor of axes that @p starts and @p ends apply to.
   * Negative value means counting dimensions from the back.
   * Accepted range is @f$[-r, r-1]@f$ where @f$r = \text{rank(input)}@f$.
   * Behavior is undefined if an axis is repeated.
   * @param steps 1-D tensor of slice step of corresponding axis in @p axes.
   * Negative value means slicing backward.
   * Cannot be 0.
   * Defaults to 1.
   * @return reference to the tensor
   */
  Tensor &Slice(const std::vector<std::int64_t> &starts, const std::vector<std::int64_t> &ends,
                const std::vector<std::int64_t> &axes = {}, const std::vector<std::int64_t> &steps = {});
  /**
   * Slice the tensor with the given @p starts, @p ends, @p axes, and @p steps.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Slice.html).
   * @param starts 1-D tensor of starting indices of corresponding axis in @p axes
   * @param ends 1-D tensor of ending indices (exclusive) of corresponding axis in @p axes
   * @param axes 1-D tensor of axes that @p starts and @p ends apply to.
   * Negative value means counting dimensions from the back.
   * Accepted range is @f$[-r, r-1]@f$ where @f$r = \text{rank(input)}@f$.
   * Behavior is undefined if an axis is repeated
   * @param steps 1-D tensor of slice step of corresponding axis in @p axes.
   * Negative value means slicing backward.
   * Cannot be 0.
   * Defaults to 1
   * @return reference to the tensor
   */
  Tensor &Slice(const Tensor &starts, const Tensor &ends, const Tensor &axes = {}, const Tensor &steps = {});
  /**
   * Concatenate the tensor with the given @p rhs along the given @p axis.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Concat.html).
   * @param rhs other tensor to concatenate with
   * @param axis Which axis to concat on.
   * A negative value means counting dimensions from the back
   * Accepted range is @f$[-r, r-1]@f$ where @f$r = \text{rank(inputs)}@f$
   * @return new tensor with the concatenated values
   */
  Tensor Concat(const Tensor &rhs, std::int64_t axis);
  /**
   * Concatenate the tensors with the given @p rhs along the given @p axis.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Concat.html).
   * @param rhs other tensors to concatenate with
   * @param axis Which axis to concat on.
   * A negative value means counting dimensions from the back
   * Accepted range is @f$[-r, r-1]@f$ where @f$r = \text{rank(inputs)}@f$
   * @return new tensor with the concatenated values
   */
  Tensor Concat(const std::vector<Tensor> &rhs, std::int64_t axis);
  /**
   * Gather the tensor with the given @p indices along the given @p axis.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Gather.html).
   * @param indices tensor of any rank @f$q@f$.
   * All index values are expected to be within bounds @f$[-s, s-1]@f$ along axis of size @f$s@f$.
   * It is an error if any of the index values are out of bounds
   * @param axis which axis to concat on.
   * A negative value means counting dimensions from the back
   * Accepted range is @f$[-r, r-1]@f$ where @f$r = \text{rank(inputs)}@f$
   * @return new tensor with the gathered values
   */
  Tensor Gather(const Tensor &indices, std::int64_t axis);
  /**
   * Matrix multiplication of two tensors.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__MatMul.html).
   * @param tensor tensor to multiply with
   * @return new tensor with the multiplied values
   */
  [[nodiscard]] Tensor MatMul(const Tensor &tensor) const;
  /**
   * Convolution of two tensors.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Conv.html).
   * @param w convolution kernel with shape @f$[M, C, k_1, k_2, \dots, k_n]@f$
   * @param dilations dilation value along each spatial axis of the filter
   * @param group number of groups input channels and output channels are divided into
   * @param kernel_shape shape of the convolution kernel. If not present, should be inferred from input W
   * @param pads padding for the beginning and ending along each spatial axis,
   * it can take any value greater than or equal to 0.
   * The value represent the number of pixels added to the beginning and end part of the corresponding axis.
   * pads format should be as follow @f$[x1_{begin}, x2_{begin} \dots x1_{end}, x2_{end} \dots]@f$,
   * where @f$xi_{begin}@f$ is the number of pixels added at the beginning of axis @f$i@f$
   * and @f$xi_{end}@f$ is the number of pixels added at the end of axis @f$i@f$.
   * @param strides stride along each spatial axis
   * @return
   */
  [[nodiscard]] Tensor Convolution(const Tensor &w, const std::vector<std::int64_t> &dilations, std::int64_t group,
                                   const std::vector<std::int64_t> &kernel_shape, const std::vector<std::int64_t> &pads,
                                   const std::vector<std::int64_t> &strides) const;
  /**
   * Convolution of two tensors.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Conv.html).
   * @param image input tensor
   * @param kernel convolution kernel
   * @param new_shape shape of the output tensor
   * @param dilations dilation value along each spatial axis of the filter
   * @param group number of groups input channels and output channels are divided into
   * @param pads padding for the beginning and ending along each spatial axis,
   * it can take any value greater than or equal to 0.
   * The value represent the number of pixels added to the beginning and end part of the corresponding axis.
   * pads format should be as follow @f$[x1_{begin}, x2_{begin} \dots x1_{end}, x2_{end} \dots]@f$,
   * where @f$xi_{begin}@f$ is the number of pixels added at the beginning of axis @f$i@f$
   * and @f$xi_{end}@f$ is the number of pixels added at the end of axis @f$i@f$.
   * @param strides stride along each spatial axis
   * @return
   */
  [[nodiscard]] xt::xarray<Expression> Convolution(const ImageView &image, const KernelView &kernel,
                                                   const std::vector<std::size_t> &new_shape,
                                                   const std::vector<std::int64_t> &dilations, std::int64_t group,
                                                   const std::vector<std::int64_t> &pads,
                                                   const std::vector<std::int64_t> &strides) const;
  const Expression &Max() const;
  /**
   * Pad the tensor with the given @p pads.
   *
   * [ONNX documentation](https://onnx.ai/onnx/operators/onnx__Pad.html).
   * @param pads padding for the beginning and ending along each spatial axis
   */
  [[nodiscard]] Tensor Pad(const std::vector<std::int64_t> &pads) const;

  [[nodiscard]] Tensor Squeeze() const;
  [[nodiscard]] Tensor Squeeze(std::vector<std::int64_t> axes) const;

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
  explicit operator std::vector<std::size_t>() const;

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
  /**
   * Given a set of indices @p dims, compute the offset of the tensor.
   * @param dims set of indices
   * @return offset of the tensor
   */
  [[nodiscard]] std::size_t ComputeOffset(std::initializer_list<std::int64_t> dims) const;
  /**
   * Given a set of indices @p dims, compute the offset of the tensor.
   * @param dims set of indices
   * @param size size of the set of indices
   * @return offset of the tensor
   */
  [[nodiscard]] std::size_t ComputeOffset(const std::int64_t *dims, std::size_t size) const;

  xt::xarray<Expression> values_;  ///< Internal storage of the values of the tensor
};

std::ostream &operator<<(std::ostream &os, const Tensor &matrix);
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression> &values);
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression>::shape_type &shape);

}  // namespace dlinear::onnx
