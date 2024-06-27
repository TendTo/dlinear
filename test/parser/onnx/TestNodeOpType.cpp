/**
 * @file TestNodeOpType.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/onnx/NodeOpType.h"

using dlinear::onnx::NodeOpType;
using dlinear::onnx::parseNodeOpType;

TEST(TestNodeOpType, ParseNodeOpType) {
  EXPECT_EQ(parseNodeOpType("Add"), NodeOpType::Add);
  EXPECT_EQ(parseNodeOpType("AveragePool"), NodeOpType::AveragePool);
  EXPECT_EQ(parseNodeOpType("BatchNormalization"), NodeOpType::BatchNormalization);
  EXPECT_EQ(parseNodeOpType("Concat"), NodeOpType::Concat);
  EXPECT_EQ(parseNodeOpType("Conv"), NodeOpType::Conv);
  EXPECT_EQ(parseNodeOpType("Dropout"), NodeOpType::Dropout);
  EXPECT_EQ(parseNodeOpType("Gemm"), NodeOpType::Gemm);
  EXPECT_EQ(parseNodeOpType("GlobalAveragePool"), NodeOpType::GlobalAveragePool);
  EXPECT_EQ(parseNodeOpType("Identity"), NodeOpType::Identity);
  EXPECT_EQ(parseNodeOpType("LeakyRelu"), NodeOpType::LeakyRelu);
  EXPECT_EQ(parseNodeOpType("MatMul"), NodeOpType::MatMul);
  EXPECT_EQ(parseNodeOpType("MaxPool"), NodeOpType::MaxPool);
  EXPECT_EQ(parseNodeOpType("Mul"), NodeOpType::Mul);
  EXPECT_EQ(parseNodeOpType("Relu"), NodeOpType::Relu);
  EXPECT_EQ(parseNodeOpType("Reshape"), NodeOpType::Reshape);
  EXPECT_EQ(parseNodeOpType("Sigmoid"), NodeOpType::Sigmoid);
  EXPECT_EQ(parseNodeOpType("Softmax"), NodeOpType::Softmax);
  EXPECT_EQ(parseNodeOpType("Transpose"), NodeOpType::Transpose);
}
