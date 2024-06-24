/**
 * @file NeuralNetworkModel.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Neural network model.
 */
#include "NeuralNetworkModel.h"

#include <fmt/core.h>

#include "dlinear/nn/NodeOpType.h"

namespace dlinear {

NeuralNetworkModel::NeuralNetworkModel(const std::string& filename) {
  std::ifstream input(filename, std::ios::binary);
  if (!input) DLINEAR_RUNTIME_ERROR_FMT("Failed to open file: {}", filename);
  const bool res = model_.ParseFromIstream(&input);
  if (!res) DLINEAR_RUNTIME_ERROR_FMT("Failed to parse model: {}", filename);
  ParseGraph();
}

NeuralNetworkModel::NeuralNetworkModel(std::ifstream& input) {
  const bool res = model_.ParseFromIstream(&input);
  if (!res) DLINEAR_RUNTIME_ERROR("Failed to parse model from input stream");
  ParseGraph();
}

void NeuralNetworkModel::ParseGraph() {
  for (const onnx::ValueInfoProto& input : model_.graph().input()) AddValueInfo(input);
  for (const onnx::TensorProto& tensor : model_.graph().initializer()) AddInitializer(tensor);
  AddNodes();
  for (const onnx::ValueInfoProto& output : model_.graph().output()) AddValueInfo(output);
}

void NeuralNetworkModel::AddInitializer(const onnx::TensorProto& tensor) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");
  available_inputs_.emplace(tensor.name(), tensor);
}

template <>
bool NeuralNetworkModel::AddNodeImpl<NodeOpType::Add>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Add", "NodeProto must have an op_type of Add");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly one output");
  DLINEAR_ASSERT(node.input_size() == 2, "NodeProto must have exactly two inputs");
  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  available_inputs_.emplace(output, available_inputs_.at(input1) + available_inputs_.at(input2));
  DLINEAR_TRACE_FMT("Add node: {} = {} + {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} + {}", available_inputs_.at(output), available_inputs_.at(input1),
                    available_inputs_.at(input2));
  return true;
}

template <>
bool NeuralNetworkModel::AddNodeImpl<NodeOpType::MatMul>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "MatMul", "NodeProto must have an op_type of MatMul");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly one output");
  DLINEAR_ASSERT(node.input_size() == 2, "NodeProto must have exactly two inputs");
  const std::string& input1 = node.input(0);
  const std::string& input2 = node.input(1);
  const std::string& output = node.output(0);
  DLINEAR_ASSERT(!available_inputs_.contains(output), "Input1 must be available");
  available_inputs_.emplace(output, available_inputs_.at(input1) * available_inputs_.at(input2));
  DLINEAR_TRACE_FMT("MatMul node: {} = {} * {}", output, input1, input2);
  DLINEAR_TRACE_FMT("{} = {} * {}", available_inputs_.at(input1) * available_inputs_.at(input2),
                    available_inputs_.at(input1), available_inputs_.at(input2));
  return true;
}

template <>
bool NeuralNetworkModel::AddNodeImpl<NodeOpType::Relu>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Relu", "NodeProto must have an op_type of Relu");
  DLINEAR_ASSERT(node.output_size() == 1, "NodeProto must have exactly one output");
  DLINEAR_ASSERT(node.input_size() == 1, "NodeProto must have exactly one inputs");
  const std::string& input = node.input(0);
  const std::string& output = node.output(0);

  Variable var(fmt::format("Relu[{} => {}]", input, output), Variable::Type::BOOLEAN);

  const Matrix& m = available_inputs_.at(input);
  Matrix relu = Matrix{m.rows(), m.cols()};
  for (int i = 0; i < m.matrix().size(); i++) {
    const Expression& e = m[i];
    relu[i] = if_then_else(e >= 0, e, 0);
  }
  available_inputs_.emplace(output, relu);
  DLINEAR_DEBUG_FMT("MatMul node: {} = 0 if input < 0 else {}", output, input);
  DLINEAR_ERROR_FMT("{}", relu);
  return true;
}

void NeuralNetworkModel::AddNodes() {
  std::list<const onnx::NodeProto*> nodes;
  for (const onnx::NodeProto& node : model_.graph().node()) nodes.push_back(&node);
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

bool NeuralNetworkModel::AddNode(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.has_op_type(), "NodeProto must have an op_type");

  const bool missing_input = std::any_of(node.input().begin(), node.input().end(), [this](const std::string& input) {
    return !available_inputs_.contains(input);
  });
  if (missing_input) {
    DLINEAR_TRACE_FMT("Missing input for node {}", node.name());
    return false;
  }

  const NodeOpType op_type = parseNodeOpType(node.op_type());
  switch (op_type) {
    case NodeOpType::Add:
      return AddNodeImpl<NodeOpType::Add>(node);
    case NodeOpType::AveragePool:
    case NodeOpType::BatchNormalization:
    case NodeOpType::Concat:
    case NodeOpType::Conv:
    case NodeOpType::Dropout:
    case NodeOpType::Gemm:
    case NodeOpType::GlobalAveragePool:
    case NodeOpType::Identity:
    case NodeOpType::LeakyRelu:
      DLINEAR_UNREACHABLE();
    case NodeOpType::MatMul:
      return AddNodeImpl<NodeOpType::MatMul>(node);
    case NodeOpType::MaxPool:
    case NodeOpType::Mul:
      DLINEAR_UNREACHABLE();
    case NodeOpType::Relu:
      return AddNodeImpl<NodeOpType::Relu>(node);
    case NodeOpType::Reshape:
    case NodeOpType::Sigmoid:
    case NodeOpType::Softmax:
    case NodeOpType::Transpose:
      DLINEAR_UNREACHABLE();
    default:
      DLINEAR_UNREACHABLE();
  }
}

void NeuralNetworkModel::AddValueInfo(const onnx::ValueInfoProto& value_info) {
  DLINEAR_ASSERT(value_info.has_type(), "ValueInfoProto must have a type");
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");
  switch (value_info.type().value_case()) {
    case onnx::TypeProto::kTensorType:
      AddValueInfoTensor(value_info);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void NeuralNetworkModel::AddValueInfoTensor(const onnx::ValueInfoProto& value_info) {
  DLINEAR_ASSERT(value_info.has_name(), "ValueInfoProto must have a name");
  DLINEAR_ASSERT(value_info.type().value_case() == onnx::TypeProto::kTensorType, "ValueInfoProto must be a tensor");
  const auto [it, res] = available_inputs_.emplace(value_info.name(), Matrix(value_info));
  variables_.emplace(value_info.name(), &it->second);
}

std::ostream& operator<<(std::ostream& os, const NeuralNetworkModel& model) {
  os << "NeuralNetworkModel(\n";
  os << "------\nVARIABLES\n------\n";
  for (const auto& [name, variables] : model.variables()) {
    os << name << ": " << *variables << "\n";
  }
  os << "------\nINPUTS\n------\n";
  for (const auto& [name, values] : model.available_inputs()) {
    os << name << ": " << values << "\n";
  }
  return os << ")";
}

}  // namespace dlinear
