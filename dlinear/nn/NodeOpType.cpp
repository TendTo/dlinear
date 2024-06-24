/**
* @file NodeOpType.cpp
* @author dlinear (https://github.com/TendTo/dlinear)
* @copyright 2024 dlinear
* @licence Apache-2.0 license
*/
#include "NodeOpType.h"

#include <iostream>

#include "dlinear/util/exception.h"

namespace dlinear {

std::ostream& operator<<(std::ostream& os, const NodeOpType& op_type) {
  switch (op_type) {
    case NodeOpType::Add:
      return os << "Add";
    case NodeOpType::AveragePool:
      return os << "AveragePool";
    case NodeOpType::BatchNormalization:
      return os << "BatchNormalization";
    case NodeOpType::Concat:
      return os << "Concat";
    case NodeOpType::Conv:
      return os << "Conv";
    case NodeOpType::Dropout:
      return os << "Dropout";
    case NodeOpType::Gemm:
      return os << "Gemm";
    case NodeOpType::GlobalAveragePool:
      return os << "GlobalAveragePool";
    case NodeOpType::Identity:
      return os << "Identity";
    case NodeOpType::LeakyRelu:
      return os << "LeakyRelu";
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
    case NodeOpType::Sigmoid:
      return os << "Sigmoid";
    case NodeOpType::Softmax:
      return os << "Softmax";
    case NodeOpType::Transpose:
      return os << "Transpose";
    default:
      DLINEAR_UNREACHABLE();
  }
}

NodeOpType parseNodeOpType(const std::string& op_type) {
  if (op_type == "Add") return NodeOpType::Add;
  if (op_type == "AveragePool") return NodeOpType::AveragePool;
  if (op_type == "BatchNormalization") return NodeOpType::BatchNormalization;
  if (op_type == "Concat") return NodeOpType::Concat;
  if (op_type == "Conv") return NodeOpType::Conv;
  if (op_type == "Dropout") return NodeOpType::Dropout;
  if (op_type == "Gemm") return NodeOpType::Gemm;
  if (op_type == "GlobalAveragePool") return NodeOpType::GlobalAveragePool;
  if (op_type == "Identity") return NodeOpType::Identity;
  if (op_type == "LeakyRelu") return NodeOpType::LeakyRelu;
  if (op_type == "MatMul") return NodeOpType::MatMul;
  if (op_type == "MaxPool") return NodeOpType::MaxPool;
  if (op_type == "Mul") return NodeOpType::Mul;
  if (op_type == "Relu") return NodeOpType::Relu;
  if (op_type == "Reshape") return NodeOpType::Reshape;
  if (op_type == "Sigmoid") return NodeOpType::Sigmoid;
  if (op_type == "Softmax") return NodeOpType::Softmax;
  if (op_type == "Transpose") return NodeOpType::Transpose;
  DLINEAR_UNREACHABLE();
}

}  // namespace dlinear
