/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "dlinear/parser/onnx/NodeOpType.h"

#include <map>
#include <string>

#include "dlinear/util/exception.h"

namespace dlinear::onnx {

const std::map<std::string, NodeOpType> string_to_node_op_type{
    {"Abs", NodeOpType::Abs},
    {"Add", NodeOpType::Add},
    {"AveragePool", NodeOpType::AveragePool},
    {"BatchNormalization", NodeOpType::BatchNormalization},
    {"Concat", NodeOpType::Concat},
    {"Constant", NodeOpType::Constant},
    {"Conv", NodeOpType::Conv},
    {"Dropout", NodeOpType::Dropout},
    {"Flatten", NodeOpType::Flatten},
    {"Gather", NodeOpType::Gather},
    {"Gemm", NodeOpType::Gemm},
    {"GlobalAveragePool", NodeOpType::GlobalAveragePool},
    {"Identity", NodeOpType::Identity},
    {"LeakyRelu", NodeOpType::LeakyRelu},
    {"LRN", NodeOpType::LRN},
    {"MatMul", NodeOpType::MatMul},
    {"MaxPool", NodeOpType::MaxPool},
    {"Mul", NodeOpType::Mul},
    {"Relu", NodeOpType::Relu},
    {"Reshape", NodeOpType::Reshape},
    {"Slice", NodeOpType::Slice},
    {"Sigmoid", NodeOpType::Sigmoid},
    {"Sign", NodeOpType::Sign},
    {"Softmax", NodeOpType::Softmax},
    {"Squeeze", NodeOpType::Squeeze},
    {"Sub", NodeOpType::Sub},
    {"Transpose", NodeOpType::Transpose},
    {"Unsqueeze", NodeOpType::Unsqueeze},
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type) {
  switch (op_type) {
    case NodeOpType::Abs:
      return os << "Abs";
    case NodeOpType::Add:
      return os << "Add";
    case NodeOpType::AveragePool:
      return os << "AveragePool";
    case NodeOpType::BatchNormalization:
      return os << "BatchNormalization";
    case NodeOpType::Concat:
      return os << "Concat";
    case NodeOpType::Constant:
      return os << "Constant";
    case NodeOpType::Conv:
      return os << "Conv";
    case NodeOpType::Dropout:
      return os << "Dropout";
    case NodeOpType::Flatten:
      return os << "Flatten";
    case NodeOpType::Gather:
      return os << "Gather";
    case NodeOpType::Gemm:
      return os << "Gemm";
    case NodeOpType::GlobalAveragePool:
      return os << "GlobalAveragePool";
    case NodeOpType::Identity:
      return os << "Identity";
    case NodeOpType::LeakyRelu:
      return os << "LeakyRelu";
    case NodeOpType::LRN:
      return os << "LRN";
    case NodeOpType::MatMul:
      return os << "MatMul";
    case NodeOpType::MaxPool:
      return os << "MaxPool";
    case NodeOpType::Mul:
      return os << "Mul";
    case NodeOpType::Relu:
      return os << "Relu";
    case NodeOpType::Reshape:
      return os << "Reshape";
    case NodeOpType::Slice:
      return os << "Slice";
    case NodeOpType::Sign:
      return os << "Sign";
    case NodeOpType::Sigmoid:
      return os << "Sigmoid";
    case NodeOpType::Softmax:
      return os << "Softmax";
    case NodeOpType::Squeeze:
      return os << "Squeeze";
    case NodeOpType::Sub:
      return os << "Sub";
    case NodeOpType::Transpose:
      return os << "Transpose";
    case NodeOpType::Unsqueeze:
      return os << "Unsqueeze";
    default:
      DLINEAR_UNREACHABLE();
  }
}

NodeOpType parseNodeOpType(const std::string& op_type) { return string_to_node_op_type.at(op_type); }

}  // namespace dlinear::onnx
