/**
 * @file NodeOpType.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Neural network model.
 */
#pragma once

#include <istream>
#include <string>

namespace dlinear {

enum class NodeOpType {
  Add,
  AveragePool,
  BatchNormalization,
  Concat,
  Conv,
  Dropout,
  Gemm,
  GlobalAveragePool,
  Identity,
  LeakyRelu,
  MatMul,
  MaxPool,
  Mul,
  Relu,
  Reshape,
  Sigmoid,
  Softmax,
  Transpose,
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type);
NodeOpType parseNodeOpType(const std::string& op_type);

}  // namespace dlinear
