/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
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
const std::map<NodeOpType, std::string> node_op_type_to_string{
    {NodeOpType::Abs, "Abs"},
    {NodeOpType::Add, "Add"},
    {NodeOpType::AveragePool, "AveragePool"},
    {NodeOpType::BatchNormalization, "BatchNormalization"},
    {NodeOpType::Concat, "Concat"},
    {NodeOpType::Constant, "Constant"},
    {NodeOpType::Conv, "Conv"},
    {NodeOpType::Dropout, "Dropout"},
    {NodeOpType::Flatten, "Flatten"},
    {NodeOpType::Gather, "Gather"},
    {NodeOpType::Gemm, "Gemm"},
    {NodeOpType::GlobalAveragePool, "GlobalAveragePool"},
    {NodeOpType::Identity, "Identity"},
    {NodeOpType::LeakyRelu, "LeakyRelu"},
    {NodeOpType::LRN, "LRN"},
    {NodeOpType::MatMul, "MatMul"},
    {NodeOpType::MaxPool, "MaxPool"},
    {NodeOpType::Mul, "Mul"},
    {NodeOpType::Relu, "Relu"},
    {NodeOpType::Reshape, "Reshape"},
    {NodeOpType::Slice, "Slice"},
    {NodeOpType::Sign, "Sign"},
    {NodeOpType::Sigmoid, "Sigmoid"},
    {NodeOpType::Softmax, "Softmax"},
    {NodeOpType::Squeeze, "Squeeze"},
    {NodeOpType::Sub, "Sub"},
    {NodeOpType::Transpose, "Transpose"},
    {NodeOpType::Unsqueeze, "Unsqueeze"},
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type) {
  return os << node_op_type_to_string.at(op_type);
}

NodeOpType parseNodeOpType(const std::string& op_type) { return string_to_node_op_type.at(op_type); }

}  // namespace dlinear::onnx
