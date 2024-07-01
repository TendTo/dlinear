/**
 * @file OnnxDriver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Neural network model.
 */
#include "dlinear/parser/onnx/Driver.h"

#include <fmt/core.h>

#include <fstream>

#include "dlinear/parser/onnx/NodeOpType.h"

namespace dlinear::onnx {

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
  if (model_.graph().input_size() == 0) DLINEAR_RUNTIME_ERROR("GraphProto must have at least one input");
  if (model_.graph().output_size() == 0) DLINEAR_RUNTIME_ERROR("GraphProto must have at least one output");
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

void OnnxDriver::AddInitializer(const ::onnx::TensorProto& tensor) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");
  DLINEAR_TRACE_FMT("AddInitializer({})", tensor.name());
  available_inputs_.emplace(tensor.name(), tensor);
}

void OnnxDriver::AddFormula(const std::string& output_name) {
  if (!variables_.contains(output_name) || !available_inputs_.contains(output_name)) return;
  DLINEAR_DEBUG_FMT("AddFormula({})", output_name);
  const Tensor& var_tensor = variables_.at(output_name);
  const Tensor& final_tensor = available_inputs_.at(output_name);
  DLINEAR_DEBUG_FMT("AddFormula({}): len({}) == len({})", output_name, var_tensor.dims(), final_tensor.dims());
  DLINEAR_TRACE_FMT("AddFormula({}): {} == {}", output_name, var_tensor, final_tensor);
  for (const Formula& f : (var_tensor == final_tensor)) Assert(f);
  DLINEAR_TRACE_FMT("Added formula for {}. Current assertions: {}", output_name, context_.assertions());
}

template <>
void OnnxDriver::AddNode<NodeOpType::Abs>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Abs", "NodeProto must have an op_type of Abs");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() == 1, "NodeProto must have exactly 1 input");
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
  DLINEAR_ASSERT(node.input_size() == 2, "NodeProto must have exactly 2 inputs");
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
void OnnxDriver::AddNode<NodeOpType::Flatten>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Flatten", "NodeProto must have an op_type of Flatten");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() == 1, "NodeProto must have exactly 1 inputs");
  DLINEAR_ASSERT(node.attribute_size() == 1, "NodeProto must have exactly 1 attribute");
  DLINEAR_ASSERT(node.attribute(0).has_i(), "NodeProto attribute must have an integer value");
  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input)}.Flatten(node.attribute(0).i()));
  DLINEAR_DEBUG_FMT("Flatten node: {} <- {}", output, input);
  DLINEAR_TRACE_FMT("{} <- {}", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Gemm>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Gemm", "NodeProto must have an op_type of Abs");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() == 2 || node.input_size() == 3, "NodeProto must have [2-3] inputs");
  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  const float alpha = node.attribute_size() > 0 && node.attribute(0).has_f() ? node.attribute(0).f() : 1;
  Tensor gemm = available_inputs_.at(input1).MatMul(available_inputs_.at(input2)) * alpha;

  if (node.attribute_size() == 2) {
    DLINEAR_DEBUG_FMT("Gemm node: {} = {} * {} x {}", output, alpha, input1, input2);
    DLINEAR_TRACE_FMT("{} = {} * {} x {}", gemm, alpha, available_inputs_.at(input1), available_inputs_.at(input2));
  }

  if (node.input_size() == 3) {
    const auto beta = node.attribute_size() > 1 && node.attribute(1).has_f() ? node.attribute(1).f() : 1;
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
void OnnxDriver::AddNode<NodeOpType::MatMul>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "MatMul", "NodeProto must have an op_type of MatMul");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() == 2, "NodeProto must have exactly 2 inputs");
  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  DLINEAR_ASSERT(!available_inputs_.contains(output), "Input1 must be available");
  available_inputs_.emplace(output, available_inputs_.at(input1).MatMul(available_inputs_.at(input2)));
  DLINEAR_DEBUG_FMT("MatMul node: {} = {} x {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} x {}", available_inputs_.contains(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Relu>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Relu", "NodeProto must have an op_type of Relu");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() == 1, "NodeProto must have exactly 1 input");
  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  Tensor relu = Tensor{available_inputs_.at(input)};
  relu.Piecewise([](const Expression& e) { return if_then_else(e >= 0, e, 0); });
  available_inputs_.emplace(output, relu);
  DLINEAR_DEBUG_FMT("Relu node: {} = 0 if input < 0 else {}", output, input);
  DLINEAR_TRACE_FMT("{}", relu);
  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Slice>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Slice", "NodeProto must have an op_type of Slice");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly 1 output");
  DLINEAR_ASSERT(node.input_size() < 3 || node.input_size() > 5, "NodeProto must have [3-5] inputs");
  const std::string& data = node.input(0);
  const std::string& starts = node.input(1);
  const std::string& ends = node.input(2);
  const std::string& axis = node.input_size() > 3 ? node.input(3) : "";
  const std::string& steps = node.input_size() > 4 ? node.input(4) : "";
  const std::string& output = node.output(0);
  available_inputs_.emplace(output,
                            available_inputs_.at(data).Slice(available_inputs_.at(starts), available_inputs_.at(ends)));

  DLINEAR_DEBUG_FMT("Slice node: {} = {}[{}:{}:{}:{}]", output, data, starts, ends, axis, steps);
  DLINEAR_TRACE_FMT("{} = {}[{}:{}:{}:{}", available_inputs_.at(output), available_inputs_.at(data),
                    available_inputs_.at(starts), available_inputs_.at(ends), available_inputs_.at(axis),
                    available_inputs_.at(steps));

  AddFormula(output);
}

template <>
void OnnxDriver::AddNode<NodeOpType::Sub>(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Sub", "NodeProto must have an op_type of Sub");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly one output");
  DLINEAR_ASSERT(node.input_size() == 2, "NodeProto must have exactly two inputs");
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
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly one output");
  DLINEAR_ASSERT(node.input_size() == 1, "NodeProto must have exactly one inputs");
  const std::string& input = node.input(0);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, Tensor{available_inputs_.at(input)}.Transpose());
  DLINEAR_DEBUG_FMT("Transpose {} = {}^T", output, input);
  DLINEAR_TRACE_FMT("{} = {}^T", available_inputs_.at(output), available_inputs_.at(input));
  AddFormula(output);
}

bool OnnxDriver::AddNode(const ::onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.has_op_type(), "NodeProto must have an op_type");

  DLINEAR_TRACE_FMT("AddNode({})", node.name());
  for (const std::string& input : node.input()) DLINEAR_TRACE_FMT("Node input: {}", input);
  const bool missing_input = std::any_of(node.input().begin(), node.input().end(), [this](const std::string& input) {
    return !available_inputs_.contains(input);
  });
  if (missing_input) {
    DLINEAR_TRACE_FMT("Missing input for node {}. Delaying addition", node.name());
    return false;
  }

  const NodeOpType op_type = parseNodeOpType(node.op_type());
  switch (op_type) {
    case NodeOpType::Abs:
      AddNode<NodeOpType::Abs>(node);
      break;
    case NodeOpType::Add:
      AddNode<NodeOpType::Add>(node);
      break;
    case NodeOpType::Flatten:
      AddNode<NodeOpType::Flatten>(node);
      break;
    case NodeOpType::Gemm:
      AddNode<NodeOpType::Gemm>(node);
      break;
    case NodeOpType::MatMul:
      AddNode<NodeOpType::MatMul>(node);
      break;
    case NodeOpType::Relu:
      AddNode<NodeOpType::Relu>(node);
      break;
    case NodeOpType::Slice:
      AddNode<NodeOpType::Slice>(node);
      break;
    case NodeOpType::Sub:
      AddNode<NodeOpType::Sub>(node);
      break;
    case NodeOpType::Transpose:
      AddNode<NodeOpType::Transpose>(node);
      break;
    default:
      DLINEAR_RUNTIME_ERROR_FMT("NodeOpType {} is not supported", node.op_type());
  }
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
}

void OnnxDriver::AddValueInfo(const ::onnx::ValueInfoProto& value_info, const bool is_input) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have a type");
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");
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

}  // namespace dlinear::onnx
