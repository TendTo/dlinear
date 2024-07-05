/**
 * @file NodeOpType.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Type of node operation.
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
  Slice,
  Softmax,
  Sub,
  Transpose,
  Unsqueeze,
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type);
NodeOpType parseNodeOpType(const std::string& op_type);

}  // namespace dlinear::onnx
