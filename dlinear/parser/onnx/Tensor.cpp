/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "dlinear/parser/onnx/Tensor.h"

#include <fmt/core.h>

#include <execution>
#include <numeric>
#include <ostream>
#include <span>
#include <utility>

#include "dlinear/symbolic/literal.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear::onnx {

namespace {

inline std::vector<int64_t> get_dims(const ::onnx::ValueInfoProto &value_info) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have type");
  DLINEAR_ASSERT(value_info.type().has_tensor_type(), "ValueInfoProto must have tensor_type");
  DLINEAR_ASSERT(value_info.type().tensor_type().has_shape(), "ValueInfoProto must have shape");
  std::vector<int64_t> dims;
  dims.reserve(value_info.type().tensor_type().shape().dim_size());
  for (const ::onnx::TensorShapeProto_Dimension &dim : value_info.type().tensor_type().shape().dim()) {
    if (dim.has_dim_value()) {
      dims.push_back(dim.dim_value());
    } else if (dim.has_dim_param()) {
      DLINEAR_WARN_FMT("Parametric dimension {} is being set to 1", dim.dim_param());
      dims.push_back(1);
    } else {
      DLINEAR_UNREACHABLE();
    }
  }
  return dims;
}

inline std::vector<int64_t> get_dims(const ::onnx::TensorProto &tensor) {
  if (tensor.dims_size() == 0) return {1};
  std::vector<int64_t> dims;
  dims.reserve(tensor.dims_size());
  for (const std::int64_t dim : tensor.dims()) {
    DLINEAR_ASSERT(dim > 0, "All dimensions of a tensor must be >= 1");
    dims.push_back(dim);
  }
  return dims;
}

}  // namespace

Tensor::Tensor(std::initializer_list<std::int64_t> dims) : values_(xt::xarray<Expression>::from_shape(dims)) {}

Tensor::Tensor(const std::int64_t value) : values_(value) {}

Tensor::Tensor(const float value) : values_(value) {}

Tensor::Tensor(const std::vector<std::int64_t> &dims) : values_(xt::xarray<Expression>::from_shape(dims)) {}

Tensor::Tensor(xt::xarray<Expression> values) : values_(std::move(values)) {}

Tensor::Tensor(const ::onnx::ValueInfoProto &value_info, const std::string &name)
    : values_{xt::xarray<Expression>::from_shape(get_dims(value_info))} {
  std::int64_t i = 0;
  for (Expression &e : values_) e = Variable(fmt::format("{}_{}", name.empty() ? value_info.name() : name, i++));
}

Tensor::Tensor(const ::onnx::TensorProto &tensor) : values_{xt::xarray<Expression>::from_shape(get_dims(tensor))} {
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");

  const void *const raw_data = tensor.has_raw_data() ? tensor.raw_data().data() : nullptr;
  const int size = static_cast<int>(values_.size());

  switch (tensor.data_type()) {
    case ::onnx::TensorProto_DataType::TensorProto_DataType_FLOAT:
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = raw_data == nullptr ? tensor.float_data(i) : static_cast<const float *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_DOUBLE:
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = raw_data == nullptr ? tensor.double_data(i) : static_cast<const double *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT64:
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = raw_data == nullptr ? tensor.uint64_data(i) : static_cast<const uint64_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT64:
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = raw_data == nullptr ? tensor.int64_data(i) : static_cast<const int64_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_BOOL:
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = raw_data == nullptr ? tensor.int32_data(i) : static_cast<const int32_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int8 data type");
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = static_cast<const int8_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT16:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int16 data type");
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = static_cast<const int16_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_INT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int32 data type");
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = static_cast<const int32_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint8 data type");
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = static_cast<const uint8_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UINT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint32 data type");
      for (int i = 0; i < size; ++i) {
        values_.flat(i) = static_cast<const uint32_t *>(raw_data)[i];
      }
      break;
    case ::onnx::TensorProto_DataType::TensorProto_DataType_UNDEFINED:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported data type: {}", tensor.data_type());
  }
}

std::vector<std::int64_t> Tensor::dims() const { return {values_.shape().cbegin(), values_.shape().cend()}; }

std::int64_t Tensor::dim(std::size_t i) const {
  if (i >= values_.dimension()) return 1;
  return static_cast<std::int64_t>(values_.shape(i));
}

bool Tensor::SameDim(const Tensor &rhs) const {
  if (values_.size() != rhs.size()) return false;
  return values_.shape() == rhs.values_.shape();
}

bool Tensor::Equal(const Tensor &rhs) const {
  if (values_.shape() != rhs.values_.shape()) return false;
  for (std::size_t i = 0; i < values_.size(); i++) {
    if (!values_.flat(i).EqualTo(rhs.values_.flat(i))) return false;
  }
  return true;
}

Tensor &Tensor::Flatten(const std::int64_t axis) {
  if (axis < 0 || axis >= static_cast<std::int64_t>(values_.size()))
    DLINEAR_OUT_OF_RANGE_FMT("Invalid axis. Must be in [{}, {}]", 0, values_.size());
  const std::int64_t rows =
      std::reduce(values_.shape().cbegin(), values_.shape().cbegin() + axis, 1, std::multiplies<std::int64_t>{});
  const std::int64_t cols =
      std::reduce(values_.shape().cbegin() + axis, values_.shape().cend(), 1, std::multiplies<std::int64_t>{});
  values_.reshape({rows, cols});
  return *this;
}

Tensor &Tensor::Unsqueeze(const Tensor &axes) {
  std::vector<std::size_t> new_shape(values_.shape().size() + axes.size(), 0);
  for (const std::int64_t axes_value : static_cast<std::vector<std::int64_t>>(axes)) new_shape.at(axes_value) = 1;
  for (std::size_t i = 0, j = 0; i < new_shape.size(); i++) {
    if (new_shape[i] != 1) new_shape[i] = values_.shape()[j++];
  }
  values_.reshape(new_shape);
  return *this;
}

Tensor &Tensor::Reshape(std::initializer_list<std::int64_t> dims) {
  values_.reshape(dims);
  return *this;
}
Tensor &Tensor::Reshape(const Tensor &tensor_dim, const bool allow_zero) {
  DLINEAR_ASSERT(
      std::none_of(tensor_dim.begin(), tensor_dim.end(),
                   [](const Expression &e) { return get_constant_value(e) < 0 && get_constant_value(e) != -1; }),
      "The dimension must be a positive integer or -1");
  DLINEAR_ASSERT(std::count_if(tensor_dim.begin(), tensor_dim.end(),
                               [](const Expression &e) { return get_constant_value(e) == -1; }) <= 1,
                 "At most one dimension can be -1");
  const auto dims = static_cast<std::vector<std::int64_t>>(tensor_dim);
  std::vector<std::size_t> new_dims;
  new_dims.reserve(tensor_dim.size());
  for (const std::int64_t &dim : dims) {
    if (dim == 0 && !allow_zero) {
      new_dims.push_back(values_.shape(new_dims.size()));
      continue;
    }
    if (dim == -1) {
      new_dims.push_back(values_.size() / std::reduce(dims.cbegin(), dims.cend(), -1, std::multiplies<std::int64_t>{}));
      continue;
    }
    new_dims.push_back(dim);
  }
  values_.reshape(new_dims);
  return *this;
}

Tensor &Tensor::Transpose(const std::vector<std::int64_t> &perm) {
  values_ = perm.empty() ? xt::transpose(values_) : xt::transpose(values_, perm);
  return *this;
}

Tensor &Tensor::Abs() {
  for (Expression &e : values_) e = abs(e);
  return *this;
}

Tensor &Tensor::Elementwise(const std::function<Expression(Expression)> &f) {
  for (Expression &e : values_) e = f(e);
  return *this;
}

Tensor &Tensor::Slice(const Tensor &starts, const Tensor &ends, const Tensor &axes, const Tensor &steps) {
  return Slice(static_cast<std::vector<std::int64_t>>(starts), static_cast<std::vector<std::int64_t>>(ends),
               static_cast<std::vector<std::int64_t>>(axes), static_cast<std::vector<std::int64_t>>(steps));
}
Tensor &Tensor::Slice(const std::vector<std::int64_t> &starts, const std::vector<std::int64_t> &ends,
                      const std::vector<std::int64_t> &axes, const std::vector<std::int64_t> &steps) {
  if (starts.empty() || ends.empty()) DLINEAR_OUT_OF_RANGE("Starts and ends must not be empty");
  if (starts.size() != ends.size()) DLINEAR_OUT_OF_RANGE("Starts and ends must have the same size");
  if (!axes.empty() && axes.size() != starts.size()) DLINEAR_OUT_OF_RANGE("Axes must have the same size as starts");
  if (!steps.empty() && steps.size() != starts.size()) DLINEAR_OUT_OF_RANGE("Steps must have the same size as starts");

  xt::xstrided_slice_vector sv(values_.dimension(), xt::all());
  for (std::size_t i = 0; i < starts.size(); i++) {
    const std::int64_t start =
        starts[i] < 0 ? starts[i] + dim(axes.empty() ? static_cast<std::int64_t>(i) : axes[i]) : starts[i];
    std::int64_t end = ends[i] < 0 ? ends[i] + dim(axes.empty() ? static_cast<std::int64_t>(i) : axes[i]) : ends[i];
    const std::int64_t axis = axes.empty() ? static_cast<std::int64_t>(i) : axes[i];
    const std::int64_t step = steps.empty() ? 1 : steps[i];
    end = std::min(end, dim(axis));
    if (start >= dim(axis)) DLINEAR_OUT_OF_RANGE_FMT("Invalid start value: {}", start);
    if (step <= 0) DLINEAR_OUT_OF_RANGE_FMT("Invalid step value: {}", step);
    if (start >= end) DLINEAR_OUT_OF_RANGE_FMT("Invalid slice: start {} >= end {}", start, end);
    sv[axis] = xt::range(start, end, step);
  }
  values_ = xt::xarray<Expression>(xt::strided_view(values_, sv));
  return *this;
}

Tensor Tensor::Concat(const Tensor &rhs, const std::int64_t axis) {
  return Tensor{xt::concatenate(xt::xtuple(values_, rhs.values_), axis < 0 ? values_.dimension() + axis : axis)};
}

Tensor Tensor::Concat(const std::vector<Tensor> &rhs, const std::int64_t axis) {
  const std::size_t normalized_axis = axis < 0 ? values_.dimension() + axis : axis;
  xt::xarray<Expression> values = values_;
  for (const Tensor &t : rhs) values = xt::concatenate(xt::xtuple(values, t.values_), normalized_axis);
  return Tensor{values};
}

Tensor Tensor::Gather(const dlinear::onnx::Tensor &indices, std::int64_t axis) {
  if (axis < 0 || axis >= static_cast<std::int64_t>(values_.dimension()))
    DLINEAR_OUT_OF_RANGE_FMT("Invalid axis. Must be in [{}, {}]", 0, values_.dimension());

  // TODO: make sure this gather implementation is correct
  std::vector<std::int64_t> new_shape{};
  new_shape.insert(new_shape.end(), values_.shape().begin(), values_.shape().begin() + axis);
  new_shape.insert(new_shape.end(), indices.values_.shape().begin(), indices.values_.shape().end());
  new_shape.insert(new_shape.end(), values_.shape().begin() + axis + 1, values_.shape().end());
  xt::xarray<Expression> new_values = xt::zeros<Expression>(new_shape);

  int counter = 0;
  for (const auto &index : indices) {
    xt::xstrided_slice_vector data_slices{};
    xt::xstrided_slice_vector new_values_slices{};
    for (int i = 0; i < axis; ++i) {
      data_slices.emplace_back(xt::all());
      new_values_slices.emplace_back(xt::all());
    }
    for (size_t i = 1; i < indices.ndim(); ++i) {
      new_values_slices.emplace_back(0);
    }
    data_slices.emplace_back(get_constant_value(index).get_num().get_ui());
    new_values_slices.emplace_back(counter++);
    data_slices.emplace_back(xt::ellipsis());
    new_values_slices.emplace_back(xt::ellipsis());

    auto data_slice = xt::strided_view(values_, data_slices);
    auto new_slice = xt::strided_view(new_values, new_values_slices);
    for (size_t j = 0; j < data_slice.size(); ++j) {
      new_slice(j) = data_slice(j);
    }
  }

  return Tensor{new_values};
}

Tensor Tensor::Convolution(const Tensor &w, const std::vector<std::int64_t> &dilation, const std::int64_t group,
                           const std::vector<std::int64_t> &kernel_shape, const std::vector<std::int64_t> &pads,
                           const std::vector<std::int64_t> &stride) const {
  DLINEAR_ASSERT(values_.dimension() == 4, "Convolution can only be applied to a 4D tensors");
  DLINEAR_ASSERT(w.values_.dimension() == 4, "Convolution can only be applied to a 4D tensors");
  DLINEAR_ASSERT(values_.shape()[1] == w.values_.shape()[1] * group,
                 "The number of input channels must be equal to the number of output channels times the group");
  DLINEAR_ASSERT(w.values_.shape()[0] % group == 0, "The number of output channels must be divisible by the group");
  DLINEAR_ASSERT(group == 1, "Group convolution is not supported yet");

  [[maybe_unused]] const std::size_t batch_size = values_.shape()[0];
  [[maybe_unused]] const std::size_t input_channels = values_.shape()[1];
  const std::vector<std::size_t> remaining_input_shapes{values_.shape().begin() + 2, values_.shape().end()};

  [[maybe_unused]] const std::size_t feature_map = w.values_.shape()[0];
  DLINEAR_ASSERT(w.values_.shape()[1] == input_channels / group,
                 "The number of input channels must be equal to the number of output channels");
  const std::vector<std::size_t> remaining_kernel_shapes{w.values_.shape().begin() + 2, w.values_.shape().end()};

  const auto image = xt::view(values_, 0ul, 0ul);
  std::vector<std::size_t> new_shape{};
  for (std::size_t i = 0; i < image.shape().size(); i++) {
    const std::size_t pad_offset = pads.size() / 2;
    new_shape.push_back(
        1 + (image.shape()[i] + pads[i] + pads[i + pad_offset] - dilation[i] * (w.values_.shape()[i + 2] - 1) - 1) /
                stride[i]);
  }

  std::vector<std::size_t> new_values_shape{1, w.values_.shape()[0]};
  new_values_shape.insert(new_values_shape.end(), new_shape.begin(), new_shape.end());
  xt::xarray<Expression> new_values{new_values_shape};

  for (std::size_t i = 0; i < w.values_.shape()[0]; i++) {
    const auto kernel = xt::view(w.values_, i, 0ul, xt::range(0, kernel_shape[0]), xt::range(0, kernel_shape[1]));
    xt::xarray<Expression> row_values{Convolution(image, kernel, new_shape, dilation, group, pads, stride)};

    for (std::size_t j = 1; j < values_.shape()[1]; j++) {
      row_values += Convolution(xt::view(values_, 0ul, j),
                                xt::view(w.values_, i, j, xt::range(0, kernel_shape[0]), xt::range(0, kernel_shape[1])),
                                new_shape, dilation, group, pads, stride);
    }
    auto new_values_view = xt::view(new_values, 0l, i, xt::all(), xt::all());
    std::size_t counter = 0;
    for (Expression &e : new_values_view) {
      e = row_values.flat(counter++);
    }
  }

  return Tensor{std::move(new_values)};
}
xt::xarray<Expression> Tensor::Convolution(const ImageView &image, const KernelView &kernel,
                                           const std::vector<std::size_t> &new_shape,
                                           const std::vector<std::int64_t> &dilation, std::int64_t,
                                           const std::vector<std::int64_t> &pads,
                                           const std::vector<std::int64_t> &stride) const {
  DLINEAR_ASSERT(pads.size() == 4, "Pads must have 4 elements");
  DLINEAR_ASSERT(dilation.size() == 2, "Dilations must have 2 elements");
  DLINEAR_ASSERT(stride.size() == 2, "Strides must have 2 elements");
  DLINEAR_ASSERT(image.dimension() == 2, "Image must be a 2D tensor");
  DLINEAR_ASSERT(kernel.dimension() == 2, "Kernel must be a 2D tensor");
  xt::xarray<Expression> new_values{xt::zeros<Expression>(new_shape)};

  std::size_t out_r = 0;
  std::size_t out_c = 0;
  const auto ih = static_cast<std::int64_t>(image.shape()[0]);
  const auto iw = static_cast<std::int64_t>(image.shape()[1]);
  const auto kh = static_cast<std::int64_t>(kernel.shape()[0]);
  const auto kw = static_cast<std::int64_t>(kernel.shape()[1]);
  const std::int64_t fkmh = kh / 2;
  const std::int64_t fkmw = kw / 2;
  const std::int64_t lkmh = kw / 2 - (kh & 1 ? 0 : 1);
  const std::int64_t lkmw = kw / 2 - (kw & 1 ? 0 : 1);
  for (std::int64_t r = -pads[0] + fkmh * dilation[0]; r < ih + pads[2] - lkmh * dilation[0]; r += stride[0]) {
    for (std::int64_t c = -pads[1] + fkmw * dilation[1]; c < iw + pads[3] - lkmw * dilation[1]; c += stride[1]) {
      new_values(out_r, out_c) = 0;
      for (std::int64_t i = 0; i < kh; i++) {
        for (std::int64_t j = 0; j < kw; j++) {
          const std::int64_t ir = r + (i - fkmh) * dilation[0];
          const std::int64_t ic = c + (j - fkmw) * dilation[1];
          new_values(out_r, out_c) +=
              ir >= 0 && ir < ih && ic >= 0 && ic < iw ? image(ir, ic) * kernel(i, j) : Expression::Zero();
        }
      }
      out_c++;
    }
    out_c = 0;
    out_r++;
  }
  new_values.reshape({1, 1, new_values.shape()[0], new_values.shape()[1]});
  return new_values;
}

const Expression &Tensor::Max() const {
  DLINEAR_ASSERT(values_.size() > 0, "Cannot get the maximum value of an empty tensor");
  return *std::max_element(values_.begin(), values_.end(), [](const Expression &lhs, const Expression &rhs) {
    if (!is_constant(lhs) || !is_constant(rhs)) DLINEAR_RUNTIME_ERROR_FMT("Cannot compare {} and {}", lhs, rhs);
    return get_constant_value(lhs) < get_constant_value(rhs);
  });
}

Tensor Tensor::Squeeze() const { return Tensor{xt::squeeze(values_)}; }
Tensor Tensor::Squeeze(std::vector<std::int64_t> axes) const {
  for (std::int64_t &axis : axes) {
    if (axis >= static_cast<std::int64_t>(values_.dimension()))
      DLINEAR_OUT_OF_RANGE_FMT("Invalid axis. Must be in [{}, {}]", -values_.dimension() + 1, -1);
    if (axis < 0) axis += static_cast<std::int64_t>(values_.dimension());
  }
  return Tensor{xt::squeeze(values_, axes)};
}

Tensor Tensor::Pad(const std::vector<std::int64_t> &pads) const {
  if ((pads.size() & 1) != 0) DLINEAR_OUT_OF_RANGE("Pads must have an even number of elements");
  if (pads.size() > values_.dimension() * 2)
    DLINEAR_OUT_OF_RANGE_FMT("Pads must have at most {} elements", values_.dimension() * 2);

  std::vector<std::size_t> new_shape(values_.shape().size(), 0);
  for (std::size_t i = 0; i < values_.shape().size(); i++) {
    new_shape[i] = values_.shape()[i] + (i >= pads.size() / 2 ? 0 : pads[i] + pads[i + pads.size() / 2]);
  }

  xt::xstrided_slice_vector slices(values_.dimension());
  for (std::size_t i = 0; i < values_.dimension(); i++) {
    const std::size_t offset = i >= pads.size() / 2 ? 0 : pads[i];
    slices[i] = xt::range(offset, values_.shape()[i] + offset);
  }

  xt::xarray<Expression> new_values = xt::zeros<Expression>(new_shape);
  size_t counter = 0;
  for (Expression &e : xt::strided_view(new_values, slices)) {
    e = values_.flat(counter++);
  }
  return Tensor{new_values};
}

Tensor Tensor::MatMul(const Tensor &rhs) const {
  if (values_.dimension() > 2 || rhs.values_.dimension() > 2)
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
  if (values_.dimension() != 2) {
    new_tensor.values_.reshape({rhs.dim(1)});
  } else if (rhs.values_.dimension() != 2) {
    new_tensor.values_.reshape({dim(0)});
  }
  return new_tensor;
}

Tensor &Tensor::operator+=(const Expression &rhs) {
  if (is_constant(rhs) && get_constant_value(rhs) == 0) return *this;
  values_ += rhs;
  return *this;
}
Tensor &Tensor::operator-=(const Expression &rhs) {
  if (is_constant(rhs) && get_constant_value(rhs) == 0) return *this;
  values_ -= rhs;
  return *this;
}
Tensor &Tensor::operator*=(const Expression &rhs) {
  if (is_constant(rhs) && get_constant_value(rhs) == 1) return *this;
  values_ *= rhs;
  return *this;
}
Tensor &Tensor::operator/=(const Expression &rhs) {
  if (is_constant(rhs) && get_constant_value(rhs) == 1) return *this;
  values_ /= rhs;
  return *this;
}

Tensor &Tensor::operator+=(const Tensor &rhs) {
  if (rhs.values_.size() == 1) return *this += rhs.values_.flat(0);
  values_ += rhs.values_;
  return *this;
}
Tensor &Tensor::operator-=(const Tensor &rhs) {
  if (rhs.values_.size() == 1) return *this -= rhs.values_.flat(0);
  values_ -= rhs.values_;
  return *this;
}
Tensor &Tensor::operator*=(const Tensor &rhs) {
  if (rhs.values_.size() == 1) return *this *= rhs.values_.flat(0);
  values_ *= rhs.values_;
  return *this;
}
Tensor &Tensor::operator/=(const Tensor &rhs) {
  if (rhs.values_.size() == 1) return *this /= rhs.values_.flat(0);
  values_ /= rhs.values_;
  return *this;
}

std::vector<Formula> Tensor::operator<(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) < rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) < rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator<=(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) <= rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) <= rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator>(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) > rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) > rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator>=(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) >= rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) >= rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator==(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) == rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) == rhs[i]);
  return formulas;
}
std::vector<Formula> Tensor::operator!=(const Tensor &rhs) const {
  if (values_.size() == 1 && rhs.values_.size() == 1) return {values_.flat(0) != rhs.values_.flat(0)};
  if (values_.shape() != rhs.values_.shape())
    DLINEAR_RUNTIME_ERROR_FMT("Invalid comparison between {} and {}", values_.shape(), rhs.values_.shape());
  std::vector<Formula> formulas;
  formulas.reserve(values_.size());
  for (std::size_t i = 0; i < values_.size(); i++) formulas.push_back(values_.flat(i) != rhs[i]);
  return formulas;
}

Expression &Tensor::operator[](const int index) { return values_.flat(index); }
const Expression &Tensor::operator[](const int index) const { return values_.flat(index); }
Expression &Tensor::operator[](const std::size_t index) { return values_.flat(index); }
const Expression &Tensor::operator[](const std::size_t index) const { return values_.flat(index); }

Expression &Tensor::operator()(std::initializer_list<std::int64_t> dims) { return values_.flat(ComputeOffset(dims)); }
const Expression &Tensor::operator()(std::initializer_list<std::int64_t> dims) const {
  return values_.flat(ComputeOffset(dims));
}

Tensor::operator std::vector<std::int64_t>() const {
  std::vector<std::int64_t> result;
  result.reserve(values_.size());
  for (const Expression &e : values_) {
    DLINEAR_ASSERT(is_constant(e), "Values must constants");
    DLINEAR_ASSERT(get_constant_value(e).get_den().get_ui() == 1, "Values must be integers");
    result.push_back(e.Evaluate().get_num().get_si());
  }
  return result;
}
Tensor::operator std::vector<double>() const {
  std::vector<double> result;
  result.reserve(values_.size());
  for (const Expression &e : values_) {
    DLINEAR_ASSERT(is_constant(e), "Values must constants");
    result.push_back(e.Evaluate().get_d());
  }
  return result;
}
Tensor::operator std::vector<std::size_t>() const {
  std::vector<std::size_t> result;
  result.reserve(values_.size());
  for (const Expression &e : values_) {
    DLINEAR_ASSERT(is_constant(e), "Values must constants");
    DLINEAR_ASSERT(get_constant_value(e).get_den().get_ui() == 1, "Values must be integers");
    result.push_back(e.Evaluate().get_num().get_ui());
  }
  return result;
}

std::size_t Tensor::ComputeOffset(std::initializer_list<std::int64_t> dims) const {
  const std::size_t being_offset = dims.size() > values_.dimension() ? dims.size() - values_.dimension() : 0;
  return ComputeOffset(dims.begin() + being_offset, std::min(dims.size(), values_.dimension()));
}
std::size_t Tensor::ComputeOffset(const std::int64_t *const dims, const std::size_t size) const {
  DLINEAR_ASSERT(size <= values_.dimension(), "Invalid number of dimensions");
  std::size_t offset = 0;
  std::size_t stride = 1;
  for (std::size_t i = 0; i < size; i++) {
    offset += dims[size - i - 1] * stride;
    stride *= values_.shape().rbegin()[static_cast<std::int64_t>(i)];
  }
  return offset;
}

std::ostream &operator<<(std::ostream &os, const Tensor &tensor) {
  return os << "Tensor(" << tensor.values().shape() << ")\n" << tensor.values();
}
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression> &values) {
  for (const Expression &e : values) os << e << '\n';
  return os;
}
std::ostream &operator<<(std::ostream &os, const xt::xarray<dlinear::Expression>::shape_type &shape) {
  for (const std::size_t dim : shape) os << dim << ' ';
  return os;
}

}  // namespace dlinear::onnx
