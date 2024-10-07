/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Type of node operation.
 */
#pragma once

#include <istream>
#include <string>

namespace dlinear::onnx {

enum class NodeOpType {
  Abs,
  Add,
  AveragePool,
  BatchNormalization,
  Concat,
  Constant,
  Conv,
  Dropout,
  Flatten,
  Gather,
  Gemm,
  GlobalAveragePool,
  Identity,
  LeakyRelu,
  LRN,
  MatMul,
  MaxPool,
  Mul,
  Relu,
  Reshape,
  Sigmoid,
  Sign,
  Slice,
  Softmax,
  Squeeze,
  Sub,
  Transpose,
  Unsqueeze,
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type);
NodeOpType parseNodeOpType(const std::string& op_type);

}  // namespace dlinear::onnx
