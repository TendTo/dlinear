/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "dlinear/parser/onnx/Driver.h"

#include <bit>
#include <fstream>

#include "dlinear/parser/onnx/NodeOpType.h"
#include "dlinear/solver/LeakyReluConstraint.h"
#include "dlinear/solver/ReluConstraint.h"
#include "dlinear/util/exception.h"

#ifdef DLINEAR_PYDLINEAR
#include "pydlinear/interrupt.h"
#endif

namespace dlinear::onnx {

static_assert(std::endian::native == std::endian::little, "Only little-endian systems are supported for onnx parsing");

namespace {
inline void invalid_number_of_inputs([[maybe_unused]] const ::onnx::NodeProto& node,
                                     [[maybe_unused]] const int actualNumberOfInputs,
                                     [[maybe_unused]] const int lowerBound, [[maybe_unused]] const int upperBound) {
  if (lowerBound == upperBound) {
    DLINEAR_RUNTIME_ERROR_FMT("Onnx operation '{}' expected to have exactly {} inputs, but found {}", node.op_type(),
                              lowerBound, actualNumberOfInputs);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Onnx operation '{}' expected to have between {} and {} inputs, but found {}",
                              node.op_type(), lowerBound, upperBound, actualNumberOfInputs);
  }
}

inline const ::onnx::AttributeProto* FindAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                                   ::onnx::AttributeProto_AttributeType expectedType,
                                                   bool throw_on_missing = false) {
  for (const ::onnx::AttributeProto& attr : node.attribute()) {
    if (attr.name() == name) {
      if (attr.type() != expectedType) {
        DLINEAR_RUNTIME_ERROR_FMT("Attribute '{}' must be of type {}", name,
                                  AttributeProto_AttributeType_Name(expectedType));
      }
      return &attr;
    }
  }
  if (throw_on_missing)
    DLINEAR_RUNTIME_ERROR_FMT("Onnx node of type {} is missing the expected attribute {}", node.op_type(), name);
  return nullptr;
}

/**
 * Get the corresponding attribute type for the type @p T.
 * @tparam T type of the attribute to get.
 * @return onnx attribute type
 */
template <IsAnyOf<bool, float, std::int64_t, std::string, std::vector<float>, std::vector<std::int64_t>,
                  std::vector<std::string>, const ::onnx::TensorProto*>
              T>
constexpr ::onnx::AttributeProto_AttributeType GetAttributeType() {
  if constexpr (std::is_same_v<T, bool> || std::is_same_v<T, std::int64_t>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_INT;
  } else if constexpr (std::is_same_v<T, float>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_FLOAT;
  } else if constexpr (std::is_same_v<T, std::string>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_STRING;
  } else if constexpr (std::is_same_v<T, std::vector<float>>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_FLOATS;
  } else if constexpr (std::is_same_v<T, std::vector<std::int64_t>>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_INTS;
  } else if constexpr (std::is_same_v<T, std::vector<std::string>>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_STRINGS;
  } else if constexpr (std::is_same_v<T, const ::onnx::TensorProto*>) {
    return ::onnx::AttributeProto_AttributeType::AttributeProto_AttributeType_TENSOR;
  }
  DLINEAR_UNREACHABLE();
}

/**
 * Get the corresponding attribute value for the type @p T.
 * @tparam T type of the attribute to get.
 * @return onnx attribute value
 */
template <IsAnyOf<bool, float, std::int64_t, std::string, std::vector<float>, std::vector<std::int64_t>,
                  std::vector<std::string>, const ::onnx::TensorProto*>
              T>
T GetAttributeValue(const ::onnx::AttributeProto* attr) {
  DLINEAR_ASSERT(attr != nullptr, "AttributeProto must not be null");
  if constexpr (std::is_same_v<T, bool>) {
    return attr->i() != 0;
  } else if constexpr (std::is_same_v<T, std::int64_t>) {
    return attr->i();
  } else if constexpr (std::is_same_v<T, float>) {
    return attr->f();
  } else if constexpr (std::is_same_v<T, std::string>) {
    return attr->s();
  } else if constexpr (std::is_same_v<T, std::vector<float>>) {
    return std::vector<float>{attr->floats().begin(), attr->floats().end()};
  } else if constexpr (std::is_same_v<T, std::vector<std::int64_t>>) {
    return std::vector<std::int64_t>{attr->ints().begin(), attr->ints().end()};
  } else if constexpr (std::is_same_v<T, std::vector<std::string>>) {
    return std::vector<std::string>{attr->strings().begin(), attr->strings().end()};
  } else if constexpr (std::is_same_v<T, const ::onnx::TensorProto*>) {
    return &attr->t();
  }
  DLINEAR_UNREACHABLE();
}

}  // namespace

OnnxDriver::OnnxDriver(Context& context) : Driver{context, "OnnxDriver"} {}

bool OnnxDriver::ParseStreamCore(std::istream& in) {
  const bool res = model_.ParseFromIstream(&in);
  if (!res) {
    DLINEAR_ERROR("OnnxDriver::ParseStreamCore(): Failed to parse model from input stream");
    return false;
  }
  ParseGraph();
  return true;
}

bool OnnxDriver::ParseFile(const std::string& filename) {
  std::ifstream input(filename, std::ios::binary);
  if (!input.is_open()) {
    DLINEAR_ERROR_FMT("OnnxDriver::ParseFile({}): Failed to open file", filename);
    return false;
  }
  return ParseStream(input);
}

void OnnxDriver::ParseGraph() {
  DLINEAR_TRACE("OnnxDriver::ParseGraph()");
  if (!model_.has_graph()) DLINEAR_RUNTIME_ERROR("ModelProto must have a graph");
  std::unordered_set<std::string> initializers;
  for (const ::onnx::TensorProto& tensor : model_.graph().initializer()) {
    AddInitializer(tensor);
    initializers.insert(tensor.name());
  }
  for (const ::onnx::ValueInfoProto& input : model_.graph().input()) {
    if (!available_inputs_.contains(input.name())) AddValueInfo(input, true);
  }
  for (const ::onnx::ValueInfoProto& output : model_.graph().output()) AddValueInfo(output);
  AddNodes();
  DLINEAR_DEBUG_FMT("OnnxDriver::ParseGraph(): assertions {}", context_.assertions());
}

template <IsAnyOf<bool, float, std::int64_t, std::string, std::vector<float>, std::vector<std::int64_t>,
                  std::vector<std::string>, const ::onnx::TensorProto*>
              T>
T OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                           const std::optional<T>& default_value) const {
  const ::onnx::AttributeProto* const attr =
      FindAttribute(node, name, GetAttributeType<T>(), !default_value.has_value());
  return attr == nullptr ? default_value.value() : GetAttributeValue<T>(attr);
}

void OnnxDriver::EnsureInput(const ::onnx::NodeProto& node, const int lb, const int ub) {
  if (node.input_size() < lb || node.input_size() > ub) invalid_number_of_inputs(node, node.input_size(), lb, ub);
}
void OnnxDriver::EnsureInput(const ::onnx::NodeProto& node, const int exact) {
  if (node.input_size() != exact) invalid_number_of_inputs(node, node.input_size(), exact, exact);
}

void OnnxDriver::AddInitializer(const ::onnx::TensorProto& tensor) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_TRACE_FMT("AddInitializer({})", tensor.name());
  available_inputs_.emplace(tensor.name(), tensor);
}

void OnnxDriver::AddFormula(const std::string& output_name) {
  if (!variables_.contains(output_name) || !available_inputs_.contains(output_name)) return;
  DLINEAR_DEBUG_FMT("AddFormula({})", output_name);
  const Tensor& var_tensor = variables_.at(output_name);
  const Tensor& final_tensor = available_inputs_.at(output_name);
  DLINEAR_TRACE_FMT("AddFormula({}): {} == {}", output_name, var_tensor, final_tensor);
  for (const Formula& f : (var_tensor == final_tensor)) Assert(f);
  DLINEAR_TRACE_FMT("Added formula for {}. Current assertions: {}", output_name, context_.assertions());
}

template <>
void OnnxDriver::AddNode<NodeOpType::Abs>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Abs", "NodeProto must have an op_type of Abs");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input)}.Abs());
  DLINEAR_DEBUG_FMT("Abs node: {} = |{}|", output, input);
  DLINEAR_TRACE_FMT("{} = |{}|", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Add>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Add", "NodeProto must have an op_type of Add");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input1) + available_inputs_.at(input2));
  DLINEAR_DEBUG_FMT("Add node: {} = {} + {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} + {}", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Concat>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Concat", "NodeProto must have an op_type of Concat");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1, 2147483647);

  const auto axis = GetAttribute<std::int64_t>(node, "axis");
  const std::string& output = node.output(0);
  const std::string& input1 = node.input(0);
  const std::vector<std::string> inputs(node.input().begin() + 1, node.input().end());
  std::vector<Tensor> tensors;
  tensors.reserve(inputs.size());
  std::transform(inputs.begin(), inputs.end(), std::back_inserter(tensors),
                 [this](const std::string& input) { return available_inputs_.at(input); });

  available_inputs_.emplace(output, Tensor{available_inputs_.at(input1)}.Concat(tensors, axis));
  DLINEAR_DEBUG_FMT("Concat node: {} = concat({})", output, inputs);
  DLINEAR_TRACE_FMT("{} = concat({})", available_inputs_.at(output), tensors);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Constant>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Constant", "NodeProto must have an op_type of Constant");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.attribute_size() == 1, "NodeProto must have exactly 1 attribute");

  const std::string& output = node.output(0);
  const ::onnx::AttributeProto& attr = node.attribute(0);
  if (attr.has_t()) {
    available_inputs_.emplace(output, Tensor{attr.t()});
  } else if (attr.has_f()) {
    Tensor c{1};
    c[0] = attr.f();
    available_inputs_.emplace(output, std::move(c));
  } else if (attr.has_i()) {
    Tensor c{1};
    c[0] = attr.i();
    available_inputs_.emplace(output, std::move(c));
  } else {
    DLINEAR_RUNTIME_ERROR("Constant node must have a tensor, float, or integer attribute");
  }
  DLINEAR_DEBUG_FMT("Constant node: {}", output);
  DLINEAR_TRACE_FMT("{}", available_inputs_.at(output));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Conv>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Conv", "NodeProto must have an op_type of Conv");
  DLINEAR_ASSERT(node.input_size() == 2 || node.input_size() == 3, "NodeProto must have [2-3] inputs");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);

  const std::string& output = node.output(0);
  const Tensor& x = available_inputs_.at(input1);
  const Tensor& w = available_inputs_.at(input2);

  std::string auto_pad{GetAttribute<std::string>(node, "auto_pad", "NOTSET")};
  std::vector<std::int64_t> dilations{GetAttribute<std::vector<std::int64_t>>(node, "dilations", {{1, 1}})};
  const auto group = GetAttribute<std::int64_t>(node, "group", 1);
  std::vector<std::int64_t> kernel_shape{GetAttribute<std::vector<std::int64_t>>(
      node, "kernel_shape", {{w.values().shape().begin() + 2, w.values().shape().end()}})};
  std::vector<std::int64_t> pads{GetAttribute<std::vector<std::int64_t>>(node, "pads", {{0, 0, 0, 0}})};
  std::vector<std::int64_t> strides{GetAttribute<std::vector<std::int64_t>>(node, "strides", {{1, 1}})};

  if (auto_pad != "NOTSET") {
    pads.clear();
    pads.assign(2 * strides.size(), 0);  // If auto_pad is VALID, we are done
    if (auto_pad != "VALID") {
      for (std::size_t i = 0; i < strides.size(); ++i) {
        const std::int64_t out_dim =
            (static_cast<std::int64_t>(x.values().shape()[i + 2]) + strides[i] - 1) / strides[i];
        const std::int64_t fks = kernel_shape[i] / 2;
        const std::int64_t lks = kernel_shape[i] / 2 - (kernel_shape[i] & 1 ? 0 : 1);
        const std::int64_t pad = out_dim * strides[i] + fks * dilations[i] + lks * dilations[i] -
                                 static_cast<std::int64_t>(x.values().shape()[i + 2]);
        if (auto_pad == "SAME_LOWER") {
          pads[i] = pad / 2;
          pads[i + strides.size()] = pad / 2 + (pad & 1);
        } else if (auto_pad == "SAME_UPPER") {
          pads[i] = pad / 2 + (pad & 1);
          pads[i + strides.size()] = pad / 2;
        }
      }
    }
  }

  Tensor conv{x.Convolution(w, dilations, group, kernel_shape, pads, strides)};
  if (node.input_size() > 2) {
    Tensor& b = available_inputs_.at(node.input(2));
    b.Reshape({1, static_cast<std::int64_t>(b.size()), 1, 1});
    conv += b;
  }
  available_inputs_.emplace(output, std::move(conv));

  DLINEAR_DEBUG_FMT("Conv node: {} <- conv({}, {}, {}, {}, {}, {}, {}, {})", output, input1, input2, auto_pad,
                    dilations, group, kernel_shape, pads, strides);
  DLINEAR_TRACE_FMT("{} <- conv({}, {})", available_inputs_.at(output), x, w);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Dropout>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Dropout", "NodeProto must have an op_type of Dropout");
  DLINEAR_ASSERT(node.output_size() == 1 || node.output_size() == 2, "NodeProto must have [1-2] output");
  EnsureInput(node, 1, 3);

  if (node.input_size() == 3 && available_inputs_.at(node.input(2)).values().size() > 0 &&
      available_inputs_.at(node.input(2))[0] != 0) {
    DLINEAR_RUNTIME_ERROR("training_mode must be false in Dropout node");
  }

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input));
  DLINEAR_DEBUG_FMT("Dropout node: {} = {}", output, input);
  DLINEAR_TRACE_FMT("{} = {}", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Flatten>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Flatten", "NodeProto must have an op_type of Flatten");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  const std::int64_t axis = GetAttribute<std::int64_t>(node, "axis", 1);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input)}.Flatten(axis));
  DLINEAR_DEBUG_FMT("Flatten node: {} <- {}", output, input);
  DLINEAR_TRACE_FMT("{} <- {}", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Gather>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Gather", "NodeProto must have an op_type of Gather");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  const std::int64_t axis = GetAttribute<std::int64_t>(node, "axis", 0);
  available_inputs_.emplace(output, available_inputs_.at(input1).Gather(available_inputs_.at(input2), axis));

  DLINEAR_DEBUG_FMT("Gather node: {} = {}[{}, axis = {}]", output, input1, input2, axis);
  DLINEAR_TRACE_FMT("{} = {}[{}, axis = {}]", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2), axis);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Gemm>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Gemm", "NodeProto must have an op_type of Abs");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2, 3);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  const float alpha = GetAttribute<float>(node, "alpha", 1);
  const bool transA = GetAttribute<bool>(node, "transA", false);
  const bool transB = GetAttribute<bool>(node, "transB", false);

  Tensor A{available_inputs_.at(input1)};
  if (transA) A.Transpose();
  Tensor B{available_inputs_.at(input2)};
  if (transB) B.Transpose();
  Tensor gemm = A.MatMul(B) * alpha;

  if (node.attribute_size() == 2) {
    DLINEAR_DEBUG_FMT("Gemm node: {} = {} * {} x {}", output, alpha, input1, input2);
    DLINEAR_TRACE_FMT("{} = {} * {} x {}", gemm, alpha, available_inputs_.at(input1), available_inputs_.at(input2));
  }

  if (node.input_size() == 3) {
    const auto beta = GetAttribute<float>(node, "beta", 1);
    const std::string& input3 = node.input(2);
    gemm += available_inputs_.at(input3) * beta;
    DLINEAR_DEBUG_FMT("Gemm node: {} = {} * {} x {} + {} * {}", output, alpha, input1, input2, beta, input3);
    DLINEAR_TRACE_FMT("{} = {} * {} x {} + {} * {}", gemm, alpha, available_inputs_.at(input1),
                      available_inputs_.at(input2), beta, available_inputs_.at(input3));
  }

  available_inputs_.emplace(output, gemm);

  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Identity>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Identity", "NodeProto must have an op_type of Identity");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input));
  DLINEAR_DEBUG_FMT("Identity node: {} = {}", output, input);
  DLINEAR_TRACE_FMT("{} = {}", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::LeakyRelu>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "LeakyRelu", "NodeProto must have an op_type of LeakyRelu");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);
  const float alpha = GetAttribute<float>(node, "alpha", 0.01);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  Tensor relu = Tensor{available_inputs_.at(input)};

#ifndef NDEBUG
  std::size_t counter = 0;
  relu.Elementwise([alpha, &counter, &input, this](const Expression& e) {
#else
  relu.Elementwise([alpha, this](const Expression& e) {
#endif
    const Formula condition{e > 0};
    // Trivial cases for the ReLU function
    if (is_true(condition)) {
      return e;
    } else if (is_false(condition)) {
      return alpha * e;
    }
#ifndef NDEBUG
    const Variable relu_var{fmt::format("{}_leaky_relu_{}", input, ++counter)};
#else
    const Variable relu_var{"lr"};
#endif
    // Adding the fresh ITE variable as a guided constraint
    context_.AssertPiecewiseLinearFunction(relu_var, e >= 0, e, alpha * e);
    context_.AddGuidedConstraint(
        std::make_unique<LeakyReluConstraint>(relu_var, e, alpha, context_.predicate_abstractor()));
    return Expression{relu_var};
  });
  available_inputs_.emplace(output, relu);
  DLINEAR_DEBUG_FMT("Relu node: {} = 0 if input < 0 else {} * {}", output, alpha, input);
  DLINEAR_TRACE_FMT("{}", relu);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::MatMul>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "MatMul", "NodeProto must have an op_type of MatMul");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input1).MatMul(available_inputs_.at(input2)));
  DLINEAR_DEBUG_FMT("MatMul node: {} = {} x {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} x {}", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Mul>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Mul", "NodeProto must have an op_type of Mul");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input1) * available_inputs_.at(input2));
  DLINEAR_DEBUG_FMT("Mul node: {} = {} * {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} * {}", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Reshape>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Reshape", "NodeProto must have an op_type of Reshape");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  const bool allow_zero = GetAttribute<bool>(node, "allowzero", false);

  const Tensor& shape = available_inputs_.at(input2);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input1)}.Reshape(shape, allow_zero));
  DLINEAR_DEBUG_FMT("Reshape node: {} = reshape({}, {})", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = reshape({}, {})", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Relu>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Relu", "NodeProto must have an op_type of Relu");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  Tensor relu = Tensor{available_inputs_.at(input)};

#ifndef NDEBUG
  std::size_t counter = 0;
  relu.Elementwise([&counter, &input, this](const Expression& e) {
#else
  relu.Elementwise([this](const Expression& e) {
#endif
    const Formula condition{e > 0};
    // Trivial cases for the ReLU function
    if (is_true(condition)) {
      return e;
    } else if (is_false(condition)) {
      return Expression{0};
    }
#ifndef NDEBUG
    const Variable relu_var{fmt::format("{}_relu_{}", input, ++counter)};
#else
    const Variable relu_var{"r"};
#endif
    // Adding the fresh ITE variable as a guided constraint
    context_.AssertPiecewiseLinearFunction(relu_var, e >= 0, e, 0);
    context_.Assert(relu_var >= 0);
    context_.AddGuidedConstraint(std::make_unique<ReluConstraint>(relu_var, e, context_.predicate_abstractor()));
    return Expression{relu_var};
  });
  available_inputs_.emplace(output, relu);
  DLINEAR_DEBUG_FMT("Relu node: {} = 0 if input < 0 else {}", output, input);
  DLINEAR_TRACE_FMT("{}", relu);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Sign>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Sign", "NodeProto must have an op_type of Sign");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  Tensor sign = Tensor{available_inputs_.at(input)};

  sign.Elementwise([](const Expression& e) { return if_then_else(e == 0, 0, if_then_else(e >= 0, 1, -1)); });
  available_inputs_.emplace(output, sign);
  DLINEAR_DEBUG_FMT("Sign node: {} = Sign({})", output, input);
  DLINEAR_TRACE_FMT("{}", sign);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Sigmoid>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Sigmoid", "NodeProto must have an op_type of Sigmoid");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  Tensor relu = Tensor{available_inputs_.at(input)};

  relu.Elementwise([](const Expression& e) {
    if (!is_constant(e)) DLINEAR_RUNTIME_ERROR("Cannot apply the sigmoid function to a non constant value");
    return 1 / (1 + exp(-get_constant_value(e).get_d()));
  });
  available_inputs_.emplace(output, relu);
  DLINEAR_DEBUG_FMT("Relu node: {} = 0 if input < 0 else {}", output, input);
  DLINEAR_TRACE_FMT("{}", relu);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Slice>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Slice", "NodeProto must have an op_type of Slice");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 3, 5);

  const std::string& data = node.input(0);
  const std::string& starts = node.input(1);
  const std::string& ends = node.input(2);
  const std::string& axis = node.input_size() > 3 ? node.input(3) : "";
  const std::string& steps = node.input_size() > 4 ? node.input(4) : "";
  const std::string& output = node.output(0);
  const std::vector<std::int64_t> starts_v = static_cast<std::vector<std::int64_t>>(available_inputs_.at(starts));
  const std::vector<std::int64_t> ends_v = static_cast<std::vector<std::int64_t>>(available_inputs_.at(ends));
  const std::vector<std::int64_t> axis_v =
      axis.empty() ? std::vector<std::int64_t>{} : static_cast<std::vector<std::int64_t>>(available_inputs_.at(axis));
  const std::vector<std::int64_t> steps_v =
      steps.empty() ? std::vector<std::int64_t>{} : static_cast<std::vector<std::int64_t>>(available_inputs_.at(steps));
  available_inputs_.emplace(output, available_inputs_.at(data).Slice(starts_v, ends_v, axis_v, steps_v));

  DLINEAR_DEBUG_FMT("Slice node: {} = {}[{}:{}:{}:{}]", output, data, starts, ends, axis, steps);
  DLINEAR_TRACE_FMT("{} = {}[{}:{}:{}:{}", available_inputs_.at(output), available_inputs_.at(data), starts_v, ends_v,
                    axis_v, steps_v);

  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Softmax>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Softmax", "NodeProto must have an op_type of Softmax");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);

  const Expression& max = available_inputs_.at(input).Max();
  const xt::xarray<Expression> softmax_values{xt::exp((available_inputs_.at(input) - max).values())};
  const std::int64_t axis = GetAttribute<std::int64_t>(node, "axis", -1);

  DLINEAR_ASSERT(std::for_each(available_inputs_.at(input).begin(), available_inputs_.at(input).end(),
                               [](const Expression& e) { return is_constant(e); }),
                 "Softmax input must be constant");

  xt::xarray<Expression> sum{xt::sum(softmax_values, axis)};
  auto shape = available_inputs_.at(input).values().shape();
  shape.at(axis < 0 ? shape.size() + axis : axis) = 1;
  sum.reshape(shape);
  available_inputs_.emplace(output, softmax_values / sum);
  DLINEAR_DEBUG_FMT("Softmax node: {} = softmax({}, axis = {})", output, input, axis);
  DLINEAR_TRACE_FMT("{} = softmax({}, axis = {})", available_inputs_.at(output), available_inputs_.at(input), axis);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Squeeze>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Squeeze", "NodeProto must have an op_type of Squeeze");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1, 2);

  const std::string& input1 = node.input(0);
  const std::string& output = node.output(0);

  if (node.input_size() == 1) {
    available_inputs_.emplace(output, available_inputs_.at(input1).Squeeze());
    DLINEAR_DEBUG_FMT("Squeeze node: {} = squeeze({})", output, input1);
    DLINEAR_TRACE_FMT("{} = squeeze({})", available_inputs_.at(output), available_inputs_.at(input1));
    AddFormula(output);
    return;
  }

  const std::string& input2 = node.input(1);
  available_inputs_.emplace(output, available_inputs_.at(input1).Squeeze(
                                        static_cast<std::vector<std::int64_t>>(available_inputs_.at(input2))));
  DLINEAR_DEBUG_FMT("Squeeze node: {} = squeeze({}, {})", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = squeeze({}, {})", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Sub>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Sub", "NodeProto must have an op_type of Sub");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input1) - available_inputs_.at(input2));
  DLINEAR_DEBUG_FMT("Sub node: {} = {} - {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} - {}", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Transpose>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Transpose", "NodeProto must have an op_type of Transpose");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 1);

  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  std::vector<std::int64_t> perm{GetAttribute<std::vector<std::int64_t>>(node, "perm", {{}})};
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input)}.Transpose(perm));
  DLINEAR_DEBUG_FMT("Transpose {} = {}^T", output, input);
  DLINEAR_TRACE_FMT("{} = {}^T", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Unsqueeze>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Unsqueeze", "NodeProto must have an op_type of Unsqueeze");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  EnsureInput(node, 2);

  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input1)}.Unsqueeze(available_inputs_.at(input2)));
  DLINEAR_DEBUG_FMT("Transpose {} = unsqueeze({}, {})", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = unsqueeze({}, {})", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

bool OnnxDriver::AddNode(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.has_op_type(), "NodeProto must have an op_type");
#ifdef DLINEAR_PYDLINEAR
  py_check_signals();
#endif

  DLINEAR_TRACE_FMT("AddNode({})", node.name());
  if (DLINEAR_TRACE_ENABLED) {
    for ([[maybe_unused]] const std::string& input : node.input()) DLINEAR_TRACE_FMT("Node input: {}", input);
  }
  const bool missing_input = std::any_of(node.input().begin(), node.input().end(), [this](const std::string& input) {
    return !available_inputs_.contains(input);
  });
  if (missing_input) {
    DLINEAR_TRACE_FMT("Missing input for node {}. Delaying addition", node.name());
    return false;
  }

  const auto it = node_handlers.find(node.op_type());
  if (it == node_handlers.end()) {
    DLINEAR_RUNTIME_ERROR_FMT("Onnx operation {} not currently supported", node.op_type());
  }
  it->second(*this, node);
  return true;
}

void OnnxDriver::AddNodes() {
  std::list<const ::onnx::NodeProto*> nodes;
  for (const ::onnx::NodeProto& node : model_.graph().node()) nodes.push_back(&node);
  bool added = true;
  while (added) {
    added = false;
    for (auto it = nodes.begin(); it != nodes.end(); it++) {
      if (AddNode(**it)) {
        it = nodes.erase(it);
        it--;
        added = true;
      }
    }
  }
  if (!nodes.empty()) {
    DLINEAR_ERROR("Failed to add all nodes");
    if (DLINEAR_TRACE_ENABLED) {
      for ([[maybe_unused]] const ::onnx::NodeProto* node : nodes)
        DLINEAR_ERROR_FMT("Failed to add node: {}", node->name());
    }
  }
}

void OnnxDriver::AddValueInfo(const ::onnx::ValueInfoProto& value_info, const bool is_input) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have a type");
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");
#ifdef DLINEAR_PYDLINEAR
  py_check_signals();
#endif
  DLINEAR_TRACE_FMT("AddValueInfo({})", value_info.name());
  switch (value_info.type().value_case()) {
    case ::onnx::TypeProto::kTensorType:
      AddValueInfoTensor(value_info, is_input);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void OnnxDriver::AddValueInfoTensor(const ::onnx::ValueInfoProto& value_info, const bool is_input) {
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");
  DLINEAR_ASSERT(value_info.type().value_case() == ::onnx::TypeProto::kTensorType, "ValueInfoProto must be a tensor");
  DLINEAR_TRACE_FMT("AddValueInfoTensor({}, {})", value_info.name(), is_input);
  const auto [it, res] = variables_.emplace(value_info.name(), Tensor(value_info, is_input ? "X" : "Y"));
  if (is_input) available_inputs_.emplace(value_info.name(), it->second);
  for (const auto& exp : it->second) context_.DeclareVariable(get_variable(exp));
  DLINEAR_DEBUG_FMT("Added variables tensor: {} -> {}", it->first, it->second);
  if (is_input) DLINEAR_TRACE_FMT("Added input: {} -> {}", value_info.name(), it->second);
}

const Variable& OnnxDriver::ToEqualVar(const Expression& expr) {
  if (is_variable(expr)) return get_variable(expr);
  auto it = equal_vars_.find(expr);
  if (it != equal_vars_.end()) return it->second;
  const auto [ins, _] = equal_vars_.emplace(expr, Variable{"var/" + expr.to_string()});
  return ins->second;
}

std::ostream& operator<<(std::ostream& os, const OnnxDriver& model) {
  os << "OnnxDriver(\n";
  os << "------\nVARIABLES\n------\n";
  for (const auto& [name, variables] : model.variables()) {
    os << name << ": " << variables << "\n";
  }
  os << "------\nINPUTS\n------\n";
  for (const auto& [name, values] : model.available_inputs()) {
    os << name << ": " << values << "\n";
  }
  return os << ")";
}

const std::map<std::string, std::function<void(OnnxDriver&, const ::onnx::NodeProto&)>> OnnxDriver::node_handlers{
    {"Abs", &OnnxDriver::AddNode<NodeOpType::Abs>},
    {"Add", &OnnxDriver::AddNode<NodeOpType::Add>},
    //    {"AveragePool", &OnnxDriver::AddNode<NodeOpType::AveragePool>},
    //    {"BatchNormalization", &OnnxDriver::AddNode<NodeOpType::BatchNormalization>},
    {"Concat", &OnnxDriver::AddNode<NodeOpType::Concat>},
    {"Constant", &OnnxDriver::AddNode<NodeOpType::Constant>},
    {"Conv", &OnnxDriver::AddNode<NodeOpType::Conv>},
    {"Dropout", &OnnxDriver::AddNode<NodeOpType::Dropout>},
    {"Flatten", &OnnxDriver::AddNode<NodeOpType::Flatten>},
    {"Gather", &OnnxDriver::AddNode<NodeOpType::Gather>},
    {"Gemm", &OnnxDriver::AddNode<NodeOpType::Gemm>},
    //    {"GlobalAveragePool", &OnnxDriver::AddNode<NodeOpType::GlobalAveragePool>},
    {"Identity", &OnnxDriver::AddNode<NodeOpType::Identity>},
    {"LeakyRelu", &OnnxDriver::AddNode<NodeOpType::LeakyRelu>},
    //    {"LRN", &OnnxDriver::AddNode<NodeOpType::LRN>},
    {"MatMul", &OnnxDriver::AddNode<NodeOpType::MatMul>},
    //    {"MaxPool", &OnnxDriver::AddNode<NodeOpType::MaxPool>},
    {"Mul", &OnnxDriver::AddNode<NodeOpType::Mul>},
    {"Relu", &OnnxDriver::AddNode<NodeOpType::Relu>},
    {"Reshape", &OnnxDriver::AddNode<NodeOpType::Reshape>},
    {"Sign", &OnnxDriver::AddNode<NodeOpType::Sign>},
    {"Sigmoid", &OnnxDriver::AddNode<NodeOpType::Sigmoid>},
    {"Slice", &OnnxDriver::AddNode<NodeOpType::Slice>},
    {"Softmax", &OnnxDriver::AddNode<NodeOpType::Softmax>},
    {"Squeeze", &OnnxDriver::AddNode<NodeOpType::Squeeze>},
    {"Sub", &OnnxDriver::AddNode<NodeOpType::Sub>},
    {"Transpose", &OnnxDriver::AddNode<NodeOpType::Transpose>},
    {"Unsqueeze", &OnnxDriver::AddNode<NodeOpType::Unsqueeze>},
};

// else if (strcmp(nodeType, "BatchNormalization") == 0) {
//   batchNormEquations(node, makeEquations);
// }
// else if (strcmp(nodeType, "MaxPool") == 0) {
//   maxPoolEquations(node, makeEquations);
// }
// else if (strcmp(nodeType, "LeakyRelu") == 0) {
//   leakyReluEquations(node, makeEquations);
// }
// else if (strcmp(nodeType, "Tanh") == 0) {
//   tanhEquations(node, makeEquations);
// }

template bool OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                       const std::optional<bool>& default_value) const;
template std::string OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                              const std::optional<std::string>& default_value) const;
template std::int64_t OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                               const std::optional<std::int64_t>& default_value) const;
template std::vector<std::int64_t> OnnxDriver::GetAttribute(
    const ::onnx::NodeProto& node, const std::string& name,
    const std::optional<std::vector<std::int64_t>>& default_value) const;
template float OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                        const std::optional<float>& default_value) const;
template std::vector<float> OnnxDriver::GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                                     const std::optional<std::vector<float>>& default_value) const;
template std::vector<std::string> OnnxDriver::GetAttribute(
    const ::onnx::NodeProto& node, const std::string& name,
    const std::optional<std::vector<std::string>>& default_value) const;
template const ::onnx::TensorProto* OnnxDriver::GetAttribute(
    const ::onnx::NodeProto& node, const std::string& name,
    const std::optional<const ::onnx::TensorProto*>& default_value) const;

}  // namespace dlinear::onnx
