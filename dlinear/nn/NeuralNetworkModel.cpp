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
  for (const onnx::NodeProto& node : model_.graph().node()) AddNode(node);
}

void NeuralNetworkModel::AddInitializer(const onnx::TensorProto& tensor) {
  DLINEAR_ASSERT(tensor.has_name(), "TensorProto must have a name");
  DLINEAR_ASSERT(tensor.has_data_type(), "TensorProto must have a data_type");
  DLINEAR_ASSERT(tensor.dims_size() > 0, "TensorProto must have at least one dimension");

  const void* const raw_data = tensor.has_raw_data() ? tensor.raw_data().data() : nullptr;
  int64_t size = 1;
  if (raw_data != nullptr) {
    for (const int64_t dim : tensor.dims()) {
      size *= dim;
      DLINEAR_ASSERT(dim > 0, "Dimensions must be positive");
    }
  }

  switch (tensor.data_type()) {
    case onnx::TensorProto_DataType::TensorProto_DataType_FLOAT:
      initializers_[tensor.name()] =
          raw_data == nullptr
              ? std::vector<mpq_class>(tensor.float_data().begin(), tensor.float_data().end())
              : std::vector<mpq_class>(static_cast<const float*>(raw_data), static_cast<const float*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_DOUBLE:
      initializers_[tensor.name()] =
          raw_data == nullptr ? std::vector<mpq_class>(tensor.double_data().begin(), tensor.double_data().end())
                              : std::vector<mpq_class>(static_cast<const double*>(raw_data),
                                                       static_cast<const double*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT64:
      initializers_[tensor.name()] =
          raw_data == nullptr ? std::vector<mpq_class>(tensor.uint64_data().begin(), tensor.uint64_data().end())
                              : std::vector<mpq_class>(static_cast<const uint64_t*>(raw_data),
                                                       static_cast<const uint64_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT64:
      initializers_[tensor.name()] =
          raw_data == nullptr ? std::vector<mpq_class>(tensor.int64_data().begin(), tensor.int64_data().end())
                              : std::vector<mpq_class>(static_cast<const int64_t*>(raw_data),
                                                       static_cast<const int64_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_BOOL:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for bool data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const bool*>(raw_data), static_cast<const bool*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int8 data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const int8_t*>(raw_data), static_cast<const int8_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT16:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int16 data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const int16_t*>(raw_data), static_cast<const int16_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_INT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for int32 data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const int32_t*>(raw_data), static_cast<const int32_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT8:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint8 data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const uint8_t*>(raw_data), static_cast<const uint8_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UINT32:
      DLINEAR_ASSERT(raw_data != nullptr, "Raw data must be provided for uint32 data type");
      initializers_[tensor.name()] =
          std::vector<mpq_class>(static_cast<const uint32_t*>(raw_data), static_cast<const uint32_t*>(raw_data) + size);
      break;
    case onnx::TensorProto_DataType::TensorProto_DataType_UNDEFINED:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported data type: {}", tensor.data_type());
  }
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::Add>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Add", "NodeProto must have an op_type of Add");
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::MatMul>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "MatMul", "NodeProto must have an op_type of MatMul");
}

template <>
void NeuralNetworkModel::AddNodeImpl<NodeOpType::Relu>(const onnx::NodeProto& node) {
  DLINEAR_ASSERT(node.op_type() == "Relu", "NodeProto must have an op_type of Relu");
}

void NeuralNetworkModel::AddNode(const onnx::NodeProto& node) {
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
    os << name << ": [";
    for (const auto& value : values) {
      os << value << ", ";
    }
    os << "], ";
  }
  return os << "])";
}

}  // namespace dlinear
