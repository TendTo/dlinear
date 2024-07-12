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
using dlinear::Expression;
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
    DLINEAR_LOG_INIT_VERBOSITY(2);
    Config config;
    config.m_format() = Config::Format::VNNLIB;
    return config;
  }

  static std::string GetPathToFile(const std::string& filename) {
    return "test/parser/onnx/onnx/" + filename + ".onnx";
  }

  void AssertCorrect(const std::string& name, const std::initializer_list<std::int64_t> dims, const Tensor& expected,
                     const std::string& output_name = "y") {
    const std::string filename{GetPathToFile(name)};
    driver_.ParseFile(filename);

    const std::int64_t y_size = std::reduce(dims.begin(), dims.end(), 1, std::multiplies<>());

    EXPECT_EQ(context_.box().size(), 1 + y_size);  // Add both input (1) and output (1 x 4 x 2 x 2)
    EXPECT_EQ(context_.assertions().size(), static_cast<std::size_t>(y_size));

    ASSERT_EQ(driver_.available_inputs().at(output_name).ndim(), dims.size());
    for (std::size_t i = 0; i < dims.size(); i++) {
      EXPECT_EQ(driver_.available_inputs().at(output_name).dims()[i], dims.begin()[i]);
    }

    for (const auto& assertion : context_.assertions()) {
      EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
      EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
      EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
    }

    EXPECT_TRUE(driver_.available_inputs().at(output_name).Equal(expected));
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

TEST_F(TestOnnxDriver, AddBroadcast) {
  const std::string filename{GetPathToFile("add_broadcast")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 3 * 4 * 2 * 2);  // Add both input and output (2 x 4 x 3)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u * 3u);
  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == ({} + X_{}))", i, i % 2 == 0 ? "1" : "2", i));
    i++;
  }
}

TEST_F(TestOnnxDriver, AddBroadcastSingle) {
  const std::string filename{GetPathToFile("add_broadcast_single")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 3 * 4 * 2 * 2);  // Add both input and output (3 x 4 x 2)
  EXPECT_EQ(context_.assertions().size(), 3u * 4u * 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 2);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == ({} + X_{}))", i, "1", i));
    i++;
  }
}

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

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);

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

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);

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

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);

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

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);

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

TEST_F(TestOnnxDriver, Slice) {
  const std::string filename{GetPathToFile("slice")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 4 + 1 * 2);  // Add both input (2 x 4) and output (1 x 2)
  EXPECT_EQ(context_.assertions().size(), 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 2);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == X_{})", i, i * 2 + 4));
    i++;
  }
}

TEST_F(TestOnnxDriver, SliceNegative) {
  const std::string filename{GetPathToFile("slice_negative")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 4 + 1 * 3);  // Add both input (2 x 4) and output (1 x 3)
  EXPECT_EQ(context_.assertions().size(), 3u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 3);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == X_{})", i, i + 1));
    i++;
  }
}

TEST_F(TestOnnxDriver, SliceAxis) {
  const std::string filename{GetPathToFile("slice_axis")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 4 + 2 * 2);  // Add both input (2 x 4) and output (2 x 2)
  EXPECT_EQ(context_.assertions().size(), 4u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 2);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == X_{})", i, i < 2 ? i : i + 2));
    i++;
  }
}

TEST_F(TestOnnxDriver, Unsqueeze) {
  const std::string filename{GetPathToFile("unsqueeze")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 3 * 4 * 5 * 2);  // Add both input (3 x 4 x 5) and output (1 x 3 x 4 x 5 x 1)
  EXPECT_EQ(context_.assertions().size(), 3u * 4u * 5u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 5u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 4);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 5);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[4], 1);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == X_{})", i, i));
    i++;
  }
}

TEST_F(TestOnnxDriver, Concat) {
  const std::string filename{GetPathToFile("concat")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 2 + 6 * 2);  // Add both input (2 x 2) and output (6 x 2)
  EXPECT_EQ(context_.assertions().size(), 6u * 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 6);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 2);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, i + 1));
    i++;
  }
}

TEST_F(TestOnnxDriver, ConcatNegative) {
  const std::string filename{GetPathToFile("concat_negative")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 2 * 1 * 3);  // Add both input (1) and output (2 x 1 x 3)
  EXPECT_EQ(context_.assertions().size(), 2u * 1u * 3u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 3);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {})", i, i + 1));
    i++;
  }
}

TEST_F(TestOnnxDriver, Sub) {
  const std::string filename{GetPathToFile("sub")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 * 4 * 2);  // Add both input and output (2 x 3 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 3u * 4u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 4);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_addition(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == ({}{} + X_{}))", i, i % 2 == 0 ? "-" : "", i + 1, i));
    i++;
  }
}

TEST_F(TestOnnxDriver, Constant) {
  const std::string filename{GetPathToFile("constant")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 2 * 4 * 5);  // Add both input (1) and output (2 x 4 x 5)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u * 5u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 5);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == {}{})", i, i % 2 == 0 ? "" : "-", i + 1, i));
    i++;
  }
}

TEST_F(TestOnnxDriver, Mul) {
  const std::string filename{GetPathToFile("mul")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 3 * 4 * 2);  // Add both input and output (2 x 3 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 3u * 4u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 4);

  int i = 0;
  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_multiplication(get_rhs_expression(assertion)));
    EXPECT_EQ(assertion.to_string(), fmt::format("(Y_{} == ({}{} * X_{}))", i, i % 2 == 0 ? "-" : "", i + 2, i));
    i++;
  }
}

TEST_F(TestOnnxDriver, Transpose) {
  const std::string filename{GetPathToFile("transpose")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 2 * 4 * 2);  // Add both input (4 x 2) and output (2 x 4)
  EXPECT_EQ(context_.assertions().size(), 2u * 4u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 2u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
  }
}

TEST_F(TestOnnxDriver, Gather) {
  const std::string filename{GetPathToFile("gather")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 3 * 2 + 2 * 2 * 2);  // Add both input (3 x 2) and output (2 x 2 x 2)
  EXPECT_EQ(context_.assertions().size(), 2u * 2u * 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 3u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 2);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_rhs_expression(assertion)));
  }
}

TEST_F(TestOnnxDriver, Convolution) {
  const std::string filename{GetPathToFile("convolution")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 1 * 5 * 5);  // Add both input (1) and output (1 x 1 x 5 x 5)
  EXPECT_EQ(context_.assertions().size(), 1u * 1u * 5u * 5u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 5);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 5);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{{12.0, 21.0, 27.0, 33.0, 24.0},
                                {33.0, 54.0, 63.0, 72.0, 51.0},
                                {63.0, 99.0, 108.0, 117.0, 81.0},
                                {93.0, 144.0, 153.0, 162.0, 111.0},
                                {72.0, 111.0, 117.0, 123.0, 84.0}};
  values.reshape({1, 1, 5, 5});
  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConvolutionNoPadding) {
  const std::string filename{GetPathToFile("convolution_no_padding")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 1 * 3 * 3);  // Add both input (1) and output (1 x 1 x 3 x 3)
  EXPECT_EQ(context_.assertions().size(), 1u * 1u * 3u * 3u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 3);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{
      {54.0, 63.0, 72.0},
      {99.0, 108.0, 117.0},
      {144.0, 153.0, 162.0},
  };
  values.reshape({1, 1, 3, 3});
  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConvolutionAutopadSame) {
  const std::string filename{GetPathToFile("convolution_autopad_same")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 1 * 3 * 3);  // Add both input (1) and output (1 x 1 x 3 x 3)
  EXPECT_EQ(context_.assertions().size(), 1u * 1u * 3u * 3u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 3);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{
      {12.0, 27.0, 24.0},
      {63.0, 108.0, 81.0},
      {72.0, 117.0, 84.0},
  };
  values.reshape({1, 1, 3, 3});
  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConvolutionDilation) {
  const std::string filename{GetPathToFile("convolution_dilation")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 1 * 3 * 3);  // Add both input (1) and output (1 x 1 x 3 x 3)
  EXPECT_EQ(context_.assertions().size(), 1u * 1u * 3u * 3u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 3);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 3);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{
      {984., 1029., 1074.},
      {1299., 1344., 1389.},
      {1614., 1659., 1704.},
  };
  values.reshape({1, 1, 3, 3});
  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConvolutionFeatures) {
  const std::string filename{GetPathToFile("convolution_features")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 4 * 2 * 2);  // Add both input (1) and output (1 x 4 x 2 x 2)
  EXPECT_EQ(context_.assertions().size(), 1u * 4u * 2u * 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 2);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{{
      {{4743., 7374.}, {8271., 12654.}},
      {{10737., 17094.}, {20178., 31608.}},
      {{16731., 26814.}, {32085., 50562.}},
      {{22725., 36534.}, {43992., 69516.}},
  }};
  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConvolutionB) {
  const std::string filename{GetPathToFile("convolution_b")};
  driver_.ParseFile(filename);

  EXPECT_EQ(context_.box().size(), 1 + 1 * 4 * 2 * 2);  // Add both input (1) and output (1 x 4 x 2 x 2)
  EXPECT_EQ(context_.assertions().size(), 1u * 4u * 2u * 2u);

  ASSERT_EQ(driver_.available_inputs().at("y").ndim(), 4u);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[0], 1);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[1], 4);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[2], 2);
  EXPECT_EQ(driver_.available_inputs().at("y").dims()[3], 2);

  for (const auto& assertion : context_.assertions()) {
    EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
    EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
    EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 0u);
    EXPECT_TRUE(is_constant(get_rhs_expression(assertion)));
  }

  xt::xarray<Expression> values{{
      {{4843., 7474.}, {8371., 12754.}},
      {{10937., 17294.}, {20378., 31808.}},
      {{17031., 27114.}, {32385., 50862.}},
      {{23125., 36934.}, {44392., 69916.}},
  }};

  Tensor expected{values};
  EXPECT_TRUE(driver_.available_inputs().at("y").Equal(expected));
}

TEST_F(TestOnnxDriver, ConstantResnet2b) {
  AssertCorrect("resnet_2b.constant", {1, 10},
                Tensor{xt::xarray<Expression>{
                    {mpq_class{"67259515042599560786479318875811559149350469211976057544786367146397071001/"
                               "27606985387162255149739023449108101809804435888681546220650096895197184"},
                     mpq_class{"5457631274884186893146315784632508683050887613465050503029690961477573631/"
                               "6901746346790563787434755862277025452451108972170386555162524223799296"},
                     mpq_class{"43401139709273914685253191977833347346714044717479229654383067566827532381/"
                               "110427941548649020598956093796432407239217743554726184882600387580788736"},
                     mpq_class{"-16194617341877112080997059234285649292825040514720270675444766303195398447/"
                               "27606985387162255149739023449108101809804435888681546220650096895197184"},
                     mpq_class{"-11949424451746129869138054392468334338224563551114444403457807911045395969/"
                               "55213970774324510299478046898216203619608871777363092441300193790394368"},
                     mpq_class{"-4238408437553481654211608236809096536276300638292329391404945626087415315719/"
                               "3533694129556768659166595001485837031654967793751237916243212402585239552"},
                     mpq_class{"9618317673931359354336008266248732138428483533434915871485885972991345183/"
                               "55213970774324510299478046898216203619608871777363092441300193790394368"},
                     mpq_class{"-388642497236228708677965478483626012674958787931010724023564829510474140685/"
                               "220855883097298041197912187592864814478435487109452369765200775161577472"},
                     mpq_class{"-13664684914010402101623100626311568506835384699896675001641022394960294079/"
                               "110427941548649020598956093796432407239217743554726184882600387580788736"},
                     mpq_class{"323307245234318070101351814953780763046097102525185292283941754424222481087/"
                               "3533694129556768659166595001485837031654967793751237916243212402585239552"}}}},
                "33");
}

// TEST_F(TestOnnxDriver, TripleRelu) {
//   //  DLINEAR_LOG_INIT_VERBOSITY(5);
//
//   const std::string filename{GetPathToFile("triple_relu")};
//   driver_.ParseFile(filename);
//
//   EXPECT_EQ(context_.box().size(), 1 * 3 * 3 * 2);  // Add both input and output (shape 1 x 1) and ite vars
//   EXPECT_EQ(context_.assertions().size(), 1u);
//   for (const auto& assertion : context_.assertions()) {
//     EXPECT_EQ(get_lhs_expression(assertion).GetVariables().size(), 1u);
//     EXPECT_TRUE(is_variable(get_lhs_expression(assertion)));
//     EXPECT_EQ(get_rhs_expression(assertion).GetVariables().size(), 1u);
//     EXPECT_TRUE(is_abs(get_rhs_expression(assertion)));
//   }
// }