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

Variables NeuralNetworkModel::all_variables() const {
  Variables all_variables;
  for (const auto& [_, variables] : variables_) {
    all_variables += variables;
  }
  return all_variables;
}

void NeuralNetworkModel::ParseGraph() {
  for (const onnx::ValueInfoProto& input : model_.graph().input()) AddValueInfo(input);
  for (const onnx::ValueInfoProto& output : model_.graph().output()) AddValueInfo(output);
  for (const onnx::TensorProto& tensor : model_.graph().initializer()) AddInitializer(tensor);
  AddNodes();
}

void NeuralNetworkModel::AddInitializer(const onnx::TensorProto& tensor) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");
  initializers_.emplace(tensor.name(), tensor);
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::Add>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Add", "NodeProto must have an op_type of Add");
  for (const std::string& input : node.input()) {
    DLINEAR_ASSERT(initializers_.contains(input) || variables_.contains(input), "Input variable not found");

  }
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::MatMul>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "MatMul", "NodeProto must have an op_type of MatMul");
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::Relu>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Relu", "NodeProto must have an op_type of Relu");
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

  const NodeOpType op_type = parseNodeOpType(node.op_type());
  switch (op_type) {
    case NodeOpType::Add:
      AddNodeImpl<NodeOpType::Add>(node);
      break;
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
      AddNodeImpl<NodeOpType::MatMul>(node);
      break;
    case NodeOpType::MaxPool:
    case NodeOpType::Mul:
      DLINEAR_UNREACHABLE();
    case NodeOpType::Relu:
      AddNodeImpl<NodeOpType::Relu>(node);
      break;
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

  const onnx::TypeProto_Tensor& tensor = value_info.type().tensor_type();
  const onnx::TensorShapeProto& shape = tensor.shape();
  DLINEAR_ASSERT(shape.dim_size() > 0, "Tensor must have at least one dimension");

  std::string variable_name_fmt = fmt::format("{}[", value_info.name());

  int64_t num_variables = 1;
  for (const onnx::TensorShapeProto_Dimension& dim : shape.dim()) {
    switch (dim.value_case()) {
      case onnx::TensorShapeProto_Dimension::kDimParam:
        DLINEAR_ASSERT(false, "DimParam not supported");
        break;
      case onnx::TensorShapeProto_Dimension::kDimValue:
        DLINEAR_ASSERT(dim.dim_value() > 0, "Only positive dimensions are supported");
        num_variables *= dim.dim_value();
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  }

  for (int64_t i = 0; i < num_variables; i++) {
    variables_[value_info.name()] += Variable(fmt::format("{}[{}]", value_info.name(), i));
  }
}

std::ostream& operator<<(std::ostream& os, const NeuralNetworkModel& model) {
  os << "NeuralNetworkModel(";
  os << "variables: [";
  for (const auto& [name, variables] : model.variables()) {
    os << name << ": " << variables << ", ";
  }
  os << "], initializers: [";
  for (const auto& [name, values] : model.initializers()) {
    os << name << ": " << values << "\n";
  }
  return os << "])";
}

}  // namespace dlinear
