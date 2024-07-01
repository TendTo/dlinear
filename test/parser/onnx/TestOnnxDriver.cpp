/**
 * @file TestOnnxDriver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/onnx/Driver.h"
#include "dlinear/util/filesystem.h"

using dlinear::Config;
using dlinear::Context;
using dlinear::get_files;
using dlinear::onnx::OnnxDriver;
using dlinear::onnx::Tensor;

class TestOnnxDriver : public ::testing::Test {
 protected:
  Config config_;
  Context context_;
  OnnxDriver driver_;

  TestOnnxDriver() : config_{GetConfig()}, context_{config_}, driver_{context_} {}

  static Config GetConfig() {
    Config config;
    config.m_format() = Config::Format::VNNLIB;
    return config;
  }

  static std::string GetPathToFile(const std::string& filename) {
    return "test/parser/onnx/onnx/" + filename + ".onnx";
  }
};

TEST_F(TestOnnxDriver, Abs) {
  const std::string filename{GetPathToFile("abs")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 3 * 4 * 5 * 2);  // Add both input and output (3 x 4 x 5)
  EXPECT_EQ(context_.assertions().size(), 3u * 4u * 5u);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_abs(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == abs(X_{}))", i, i));
    i++;
  }
}

TEST_F(TestOnnxDriver, Add) {
  const std::string filename{GetPathToFile("add")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 * 4 * 2);  // Add both input and output (2 x 3 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 3u * 4u);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == ({}{} + X_{}))", i, i % 2 == 0 ? "" : "-", i + 1, i));
    i++;
  }
}

// TODO: implement broadcast matrix
// TEST_F(TestOnnxDriver, AddBroadcastMatrix) {
//  const std::string filename{GetPathToFile("add_broadcast_matrix")};
//  driver_.ParseFile(filename);
//
//  EXPECT_EQ(context_.box().size(), 3 * 4 * 5 * 2);  // Add both input and output (3 x 4 x 5)
//  EXPECT_EQ(context_.assertions().size(), 3u * 4u * 5u);
//  int i = 0;
//  for (const auto& assertion : context_.assertions()) {
//    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
//    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
//    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
//    EXPECT_TRUE(is_abs(get_rhs_expression(assertion)));
//    EXPECT_EQ(assertion.to_string(), fmt::format("Y_{} == X_{} + {}", i, i, i));
//    i++;
//  }
//}

// TODO: implement AveragePool
// TEST_F(TestOnnxDriver, AveragePool) {
//  const std::string filename{GetPathToFile("average_pooling")};
//  driver_.ParseFile(filename);
//
//  EXPECT_EQ(context_.box().size(), 2 * 3 * 4 * 2);  // Add both input and output (2 x 3 x 4)
//  EXPECT_EQ(context_.assertions().size(), 2u * 3u * 4u);
//
//  int i = 0;
//  for (const auto& assertion : context_.assertions()) {
//    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
//    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
//    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
//    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
//    EXPECT_EQ(assertion.to_string(),
//              fmt::format("(Y_{} == ({}{} + X_{}))", i, i % 2 == 0 ? "" : "-", i + 1, i));
//    i++;
//  }
//}

TEST_F(TestOnnxDriver, GemmNoC) {
  const std::string filename{GetPathToFile("gemm_no_c")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 + 2 * 4);  // Add both input (2 x 3) and output (2 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u);

  Tensor mul = driver_.available_inputs().at("x").MatMul(driver_.available_inputs().at("initializer0"));

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 3u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, mul[i].to_string()));
    i++;
  }
}

TEST_F(TestOnnxDriver, GemmAlphaNoC) {
  const std::string filename{GetPathToFile("gemm_alpha_no_c")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 + 2 * 4);  // Add both input (2 x 3) and output (2 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u);

  const float alpha = 2;
  Tensor mul = driver_.available_inputs().at("x").MatMul(driver_.available_inputs().at("initializer0"));

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 3u);
    EXPECT_TRUE(is_multiplication(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, (alpha * mul[i]).to_string()));
    i++;
  }
}

TEST_F(TestOnnxDriver, Gemm) {
  const std::string filename{GetPathToFile("gemm")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 + 2 * 4);  // Add both input (2 x 3) and output (2 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u);

  Tensor mul = driver_.available_inputs().at("x").MatMul(driver_.available_inputs().at("initializer0"));
  mul += driver_.available_inputs().at("initializer1");

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 3u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, mul[i].to_string()));
    i++;
  }
}

TEST_F(TestOnnxDriver, GemmAlphaBeta) {
  const std::string filename{GetPathToFile("gemm_alpha_beta")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 + 2 * 4);  // Add both input (2 x 3) and output (2 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u);

  const float alpha = 2;
  const float beta = 3;
  Tensor mul = driver_.available_inputs().at("x").MatMul(driver_.available_inputs().at("initializer0")) * alpha;
  mul += driver_.available_inputs().at("initializer1") * beta;

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 3u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, mul[i].to_string()));
    i++;
  }
}

TEST_F(TestOnnxDriver, TripleRelu) {
  //  DLINEAR_LOG_INIT_VERBOSITY(5);

  const std::string filename{GetPathToFile("triple_relu")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 * 3 * 3 * 2);  // Add both input and output (shape 1 x 1) and ite vars
  EXPECT_EQ(context_.assertions().size(), 1u);
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_abs(get_rhs_expression(assertion)));
  }
}