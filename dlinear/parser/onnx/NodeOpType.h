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

/** Type of node operation. */
enum class NodeOpType {
  Abs,                 ///< Absolute value
  Add,                 ///< Addition
  AveragePool,         ///< Average pooling
  BatchNormalization,  ///< Batch normalization
  Concat,              ///< Concatenation
  Constant,            ///< Constant
  Conv,                ///< Convolution
  Dropout,             ///< Dropout
  Flatten,             ///< Flatten
  Gather,              ///< Gather
  Gemm,                ///< General matrix multiplication
  GlobalAveragePool,   ///< Global average pooling
  Identity,            ///< Identity
  LeakyRelu,           ///< Leaky ReLU
  LRN,                 ///< Local response normalization
  MatMul,              ///< Matrix multiplication
  MaxPool,             ///< Max pooling
  Mul,                 ///< Multiplication
  Relu,                ///< ReLU
  Reshape,             ///< Reshape
  Sigmoid,             ///< Sigmoid
  Sign,                ///< Sign
  Slice,               ///< Slice
  Softmax,             ///< Softmax
  Squeeze,             ///< Squeeze
  Sub,                 ///< Subtraction
  Transpose,           ///< Transpose
  Unsqueeze,           ///< Unsqueeze
};

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type);
/**
 * Parse a string to a node operation type.
 * @param op_type string to parse
 * @return node operation type parsed from @p op_type
 */
NodeOpType parseNodeOpType(const std::string& op_type);

}  // namespace dlinear::onnx
