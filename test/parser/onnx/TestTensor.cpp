/**
 * @file TestTensor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/onnx/Tensor.h"

using dlinear::Expression;
using dlinear::onnx::Tensor;

class TestTensor : public ::testing::Test {
 protected:
  Tensor tensor_{2, 3, 4, 7};
  Tensor tensor2_{2, 2, 2};
  Tensor tensor_zero_{1};
  Tensor tensor_one_{1};

  TestTensor() {
    DLINEAR_LOG_INIT_VERBOSITY(5);
    for (std::size_t i = 0; i < tensor_.size(); i++) tensor_[i] = i + 1;
    for (Expression& e : tensor2_) e = 2;
    tensor_zero_[0] = 0;
    tensor_one_[0] = 1;
  }
};

TEST_F(TestTensor, DimConstructor) {
  Tensor tensor{1, 2, 3};
  EXPECT_EQ(tensor.dims().size(), 3u);
  EXPECT_EQ(tensor.dims()[0], 1);
  EXPECT_EQ(tensor.dims()[1], 2);
  EXPECT_EQ(tensor.dims()[2], 3);
  EXPECT_EQ(tensor.values().size(), 1u * 2u * 3u);
}

TEST_F(TestTensor, SingleValueConstructor) {
  Tensor tensor(1.0f);
  EXPECT_EQ(tensor.dims().size(), 0u);
  EXPECT_EQ(tensor.values().size(), 1u);
}

TEST_F(TestTensor, EmptyDimConstructor) {
  Tensor tensor{};
  EXPECT_EQ(tensor.dims().size(), 0u);
  EXPECT_EQ(tensor.values().size(), 1u);
}
TEST_F(TestTensor, NegativeDimConstructor) { EXPECT_THROW(Tensor({1, -1, 1}), std::bad_array_new_length); }

TEST_F(TestTensor, VectorConstructor) {
  Tensor tensor{std::vector<std::int64_t>{1, 2, 3}};
  EXPECT_EQ(tensor.dims().size(), 3u);
  EXPECT_EQ(tensor.dims()[0], 1);
  EXPECT_EQ(tensor.dims()[1], 2);
  EXPECT_EQ(tensor.dims()[2], 3);
  EXPECT_EQ(tensor.values().size(), 1u * 2u * 3u);
}

TEST_F(TestTensor, EmptyVectorConstructor) {
  Tensor tensor{std::vector<std::int64_t>{}};
  EXPECT_EQ(tensor.dims().size(), 0u);
  EXPECT_EQ(tensor.values().size(), 1u);
}
TEST_F(TestTensor, NegativeVectorConstructor) {
  EXPECT_THROW(Tensor{std::vector<std::int64_t>({1, -1, 1})}, std::bad_array_new_length);
}

TEST_F(TestTensor, RoundParenthesisAccessTwoDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor(i, 0l)), i);
}

TEST_F(TestTensor, RoundParenthesisAccessThreeDim) {
  Tensor tensor{3, 4, 2};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 0;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 1;
  tensor[12] = tensor[13] = tensor[14] = tensor[15] = 1;
  tensor[16] = tensor[17] = tensor[18] = tensor[19] = 2;
  tensor[20] = tensor[21] = tensor[22] = tensor[23] = 2;
  for (std::int64_t k = 0; k < tensor.dim(2); k++) {
    for (std::int64_t j = 0; j < tensor.dim(1); j++) {
      for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor(i, j, k)), i);
    }
  }
}

TEST_F(TestTensor, RoundParenthesisAccessExtraDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor(0, 0, 0, i, 1)), i);
}

TEST_F(TestTensor, RoundParenthesisAccessMissingDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(1); i++) EXPECT_EQ(get_constant_value(tensor(i)), 0);
}

TEST_F(TestTensor, RoundParenthesisVectorAccessTwoDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor({i, 0l})), i);
}

TEST_F(TestTensor, RoundParenthesisVectorAccessThreeDim) {
  Tensor tensor{3, 4, 2};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 0;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 1;
  tensor[12] = tensor[13] = tensor[14] = tensor[15] = 1;
  tensor[16] = tensor[17] = tensor[18] = tensor[19] = 2;
  tensor[20] = tensor[21] = tensor[22] = tensor[23] = 2;
  for (std::int64_t k = 0; k < tensor.dim(2); k++) {
    for (std::int64_t j = 0; j < tensor.dim(1); j++) {
      for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor({i, j, k})), i);
    }
  }
}

TEST_F(TestTensor, RoundParenthesisVectorAccessExtraDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(0); i++) EXPECT_EQ(get_constant_value(tensor({0, 0, i, 1})), i);
}

TEST_F(TestTensor, InvalidRoundParenthesisVectorAccessMissingDim) {
  Tensor tensor{3, 4};
  tensor[0] = tensor[1] = tensor[2] = tensor[3] = 0;
  tensor[4] = tensor[5] = tensor[6] = tensor[7] = 1;
  tensor[8] = tensor[9] = tensor[10] = tensor[11] = 2;
  for (std::int64_t i = 0; i < tensor.dim(1); i++) EXPECT_EQ(get_constant_value(tensor({i})), 0);
}

TEST_F(TestTensor, SameDim) {
  Tensor tensor1{1}, tensor12{1};
  EXPECT_TRUE(tensor1.SameDim(tensor12));
  Tensor tensor2{3, 4}, tensor22{3, 4};
  EXPECT_TRUE(tensor2.SameDim(tensor22));
  Tensor tensor3{3, 4, 6, 1, 1}, tensor32{3, 4, 6, 1, 1};
  EXPECT_TRUE(tensor3.SameDim(tensor32));
  Tensor tensor4{3}, tensor42{3};
  EXPECT_TRUE(tensor4.SameDim(tensor42));
}

TEST_F(TestTensor, DifferentDim) {
  Tensor tensor1{1}, tensor12{2};
  EXPECT_FALSE(tensor1.SameDim(tensor12));
  Tensor tensor2{1, 4}, tensor22{4, 1};
  EXPECT_FALSE(tensor2.SameDim(tensor22));
  Tensor tensor3{3, 4, 6, 1, 1}, tensor32{3, 4};
  EXPECT_FALSE(tensor3.SameDim(tensor32));
  Tensor tensor4{3, 4, 1}, tensor42{3, 4, 2};
  EXPECT_FALSE(tensor4.SameDim(tensor42));
}

TEST_F(TestTensor, Equal) {
  Tensor tensor1{1}, tensor12{1};
  for (std::size_t i = 0; i < tensor1.size(); i++) tensor1[i] = tensor12[i] = i;
  EXPECT_TRUE(tensor1.Equal(tensor12));
  Tensor tensor2{3, 4}, tensor22{3, 4};
  for (std::size_t i = 0; i < tensor2.size(); i++) tensor2[i] = tensor22[i] = i;
  EXPECT_TRUE(tensor2.Equal(tensor22));
  Tensor tensor3{3, 4, 6, 1, 1}, tensor32{3, 4, 6, 1, 1};
  for (std::size_t i = 0; i < tensor3.size(); i++) tensor3[i] = tensor32[i] = i;
  EXPECT_TRUE(tensor3.Equal(tensor32));
  Tensor tensor4{3}, tensor42{3};
  for (std::size_t i = 0; i < tensor4.size(); i++) tensor4[i] = tensor42[i] = i;
  EXPECT_TRUE(tensor4.Equal(tensor42));
}

TEST_F(TestTensor, NotEqual) {
  Tensor tensor1{1}, tensor12{1};
  for (std::size_t i = 0; i < tensor1.size(); i++) {
    tensor1[i] = i;
    tensor12[i] = i + 1;
  }
  EXPECT_FALSE(tensor1.Equal(tensor12));
  Tensor tensor2{3, 4}, tensor22{3, 4};
  for (std::size_t i = 0; i < tensor2.size(); i++) tensor2[i] = tensor22[i] = i;
  tensor2[0] = -1;
  EXPECT_FALSE(tensor2.Equal(tensor22));
  Tensor tensor3{3, 4, 4, 2, 1}, tensor32{3, 4, 4, 1, 2};
  for (std::size_t i = 0; i < tensor3.size(); i++) tensor3[i] = tensor32[i] = i;
  EXPECT_FALSE(tensor3.Equal(tensor32));
  Tensor tensor4{3, 4}, tensor42{4, 3};
  for (std::size_t i = 0; i < tensor4.size(); i++) tensor4[i] = tensor42[i] = i;
  EXPECT_FALSE(tensor4.Equal(tensor42));
}

TEST_F(TestTensor, Addition) {
  Tensor double_tensor = tensor_ + tensor_;
  EXPECT_EQ(double_tensor.size(), tensor_.size());
  EXPECT_EQ(double_tensor.dims(), tensor_.dims());

  for (std::size_t i = 0; i < tensor_.size(); i++)
    EXPECT_EQ(get_constant_value(double_tensor[i]), 2 * get_constant_value(tensor_[i]));
}

TEST_F(TestTensor, AdditionBroadcast) {
  Tensor double_tensor = tensor_ + tensor_;
  EXPECT_EQ(double_tensor.size(), tensor_.size());
  EXPECT_EQ(double_tensor.dims(), tensor_.dims());

  for (std::size_t i = 0; i < tensor_.size(); i++)
    EXPECT_EQ(get_constant_value(double_tensor[i]), 2 * get_constant_value(tensor_[i]));
}

TEST_F(TestTensor, AdditionSingleDimension) {
  tensor_one_ += tensor_one_;
  EXPECT_EQ(get_constant_value(tensor_one_(0)), 2);
}

TEST_F(TestTensor, InvalidAdditionSize) { EXPECT_THROW(tensor_ += tensor2_, xt::broadcast_error); }

TEST_F(TestTensor, Subtraction) {
  Tensor zero_tensor = tensor_ - tensor_;
  EXPECT_EQ(zero_tensor.size(), tensor_.size());
  EXPECT_EQ(zero_tensor.dims(), tensor_.dims());

  for (std::size_t i = 0; i < tensor_.size(); i++) EXPECT_EQ(get_constant_value(zero_tensor[i]), 0);
}

TEST_F(TestTensor, SubtractionSingleDimension) {
  tensor_one_ -= tensor_one_;
  EXPECT_EQ(get_constant_value(tensor_one_(0)), 0);
}

TEST_F(TestTensor, InvalidSubtractionSize) { EXPECT_THROW(tensor_ -= tensor2_, xt::broadcast_error); }

TEST_F(TestTensor, Multiplication) {
  Tensor square_tensor = tensor_ * tensor_;
  EXPECT_EQ(square_tensor.size(), tensor_.size());
  EXPECT_EQ(square_tensor.dims(), tensor_.dims());

  for (std::size_t i = 0; i < tensor_.size(); i++)
    EXPECT_EQ(get_constant_value(square_tensor[i]), get_constant_value(tensor_[i]) * get_constant_value(tensor_[i]));
}

TEST_F(TestTensor, MultiplicationSingleDimension) {
  tensor_one_ *= tensor_one_;
  EXPECT_EQ(get_constant_value(tensor_one_(0)), 1);
}

TEST_F(TestTensor, InvalidMultiplicationSize) { EXPECT_THROW(tensor_ *= tensor2_, xt::broadcast_error); }

TEST_F(TestTensor, Division) {
  Tensor square_tensor = tensor_ / tensor_;
  EXPECT_EQ(square_tensor.size(), tensor_.size());
  EXPECT_EQ(square_tensor.dims(), tensor_.dims());

  for (std::size_t i = 0; i < tensor_.size(); i++) EXPECT_EQ(get_constant_value(square_tensor[i]), 1);
}

TEST_F(TestTensor, DivisionSingleDimension) {
  tensor_one_ /= tensor_one_;
  EXPECT_EQ(get_constant_value(tensor_one_(0)), 1);
}

TEST_F(TestTensor, InvalidDivisionSize) { EXPECT_THROW(tensor_ /= tensor2_, xt::broadcast_error); }

TEST_F(TestTensor, MatMul) {
  Tensor a{2, 4}, b{4, 3};
  a(0, 0) = 1;
  a(0, 1) = 1;
  a(0, 2) = 1;
  a(0, 3) = 1;
  a(1, 0) = 1;
  a(1, 1) = 1;
  a(1, 2) = 1;
  a(1, 3) = 1;

  b(0, 0) = 1;
  b(0, 1) = 1;
  b(0, 2) = 1;
  b(1, 0) = 1;
  b(1, 1) = 1;
  b(1, 2) = 1;
  b(2, 0) = 1;
  b(2, 1) = 1;
  b(2, 2) = 1;
  b(3, 0) = 1;
  b(3, 1) = 1;
  b(3, 2) = 1;
}

TEST_F(TestTensor, MatMul2) {
  Tensor a{2, 3}, b{3, 2};
  a(0, 0) = 1;
  a(0, 1) = 2;
  a(0, 2) = 3;
  a(1, 0) = 4;
  a(1, 1) = 5;
  a(1, 2) = 6;

  b(0, 0) = 10;
  b(0, 1) = 11;
  b(1, 0) = 20;
  b(1, 1) = 21;
  b(2, 0) = 30;
  b(2, 1) = 31;

  Tensor c{a.MatMul(b)};
  EXPECT_EQ(c.dims().size(), 2u);
  EXPECT_EQ(c.dim(0), 2);
  EXPECT_EQ(c.dim(1), 2);
  EXPECT_EQ(get_constant_value(c(0, 0)), 140);
  EXPECT_EQ(get_constant_value(c(0, 1)), 146);
  EXPECT_EQ(get_constant_value(c(1, 0)), 320);
  EXPECT_EQ(get_constant_value(c(1, 1)), 335);
}

TEST_F(TestTensor, TransposeSquareMatrix) {
  Tensor squareMatrix{2, 2};
  for (std::size_t i = 0; i < squareMatrix.size(); i++) squareMatrix[i] = i;
  squareMatrix.Transpose();

  EXPECT_EQ(squareMatrix.dim(0), 2);
  EXPECT_EQ(squareMatrix.dim(1), 2);
  EXPECT_EQ(get_constant_value(squareMatrix(0, 0)), 0);
  EXPECT_EQ(get_constant_value(squareMatrix(0, 1)), 2);
  EXPECT_EQ(get_constant_value(squareMatrix(1, 0)), 1);
  EXPECT_EQ(get_constant_value(squareMatrix(1, 1)), 3);
}

TEST_F(TestTensor, TransposeRectangleMatrix) {
  Tensor rectangleMatrix{2, 3};
  for (std::size_t i = 0; i < rectangleMatrix.size(); i++) rectangleMatrix[i] = i;
  rectangleMatrix.Transpose();

  EXPECT_EQ(rectangleMatrix.dim(0), 3);
  EXPECT_EQ(rectangleMatrix.dim(1), 2);
  EXPECT_EQ(get_constant_value(rectangleMatrix(0, 0)), 0);
  EXPECT_EQ(get_constant_value(rectangleMatrix(0, 1)), 3);
  EXPECT_EQ(get_constant_value(rectangleMatrix(1, 0)), 1);
  EXPECT_EQ(get_constant_value(rectangleMatrix(1, 1)), 4);
  EXPECT_EQ(get_constant_value(rectangleMatrix(2, 0)), 2);
  EXPECT_EQ(get_constant_value(rectangleMatrix(2, 1)), 5);
}

TEST_F(TestTensor, TransposeBigRectangleMatrix) {
  Tensor rectangleMatrix{3, 7};
  for (std::size_t i = 0; i < rectangleMatrix.size(); i++) rectangleMatrix[i] = i;
  rectangleMatrix.Transpose();

  EXPECT_EQ(rectangleMatrix.dim(0), 7);
  EXPECT_EQ(rectangleMatrix.dim(1), 3);
  for (std::int64_t j = 0; j < rectangleMatrix.dim(1); j++) {
    for (std::int64_t i = 0; i < rectangleMatrix.dim(0); i++) {
      EXPECT_EQ(get_constant_value(rectangleMatrix(i, j)), j * 7 + i);
    }
  }
}

TEST_F(TestTensor, TransposeRowVector) {
  Tensor rectangleMatrix{1, 9};
  for (std::size_t i = 0; i < rectangleMatrix.size(); i++) rectangleMatrix[i] = i;
  rectangleMatrix.Transpose();

  EXPECT_EQ(rectangleMatrix.dim(0), 9);
  EXPECT_EQ(rectangleMatrix.dim(1), 1);
  for (std::int64_t j = 0; j < rectangleMatrix.dim(1); j++) {
    for (std::int64_t i = 0; i < rectangleMatrix.dim(0); i++) {
      EXPECT_EQ(get_constant_value(rectangleMatrix(i, j)), j * 9 + i);
    }
  }
}

TEST_F(TestTensor, TransposeColumnVector) {
  Tensor rectangleMatrix{9};
  for (std::size_t i = 0; i < rectangleMatrix.size(); i++) rectangleMatrix[i] = i;
  rectangleMatrix.Transpose();

  EXPECT_EQ(rectangleMatrix.dim(0), 1);
  EXPECT_EQ(rectangleMatrix.dim(1), 9);
  for (std::int64_t j = 0; j < rectangleMatrix.dim(1); j++) {
    for (std::int64_t i = 0; i < rectangleMatrix.dim(0); i++) {
      EXPECT_EQ(get_constant_value(rectangleMatrix(i, j)), j + i);
    }
  }
}

TEST_F(TestTensor, TransposeHigherDimensionTensor) {
  Tensor tensor{2, 3, 4};
  EXPECT_THROW(tensor.Transpose(), std::runtime_error);
}

TEST_F(TestTensor, Pad) {
  xt::xarray<Expression> values{{1, 2, 3}, {4, 5, 6}};
  Tensor tensor{values};
  Tensor padded{tensor.Pad({1, 1, 1, 1})};

  ASSERT_EQ(padded.dims().size(), 2u);
  EXPECT_EQ(padded.dim(0), 4);
  EXPECT_EQ(padded.dim(1), 5);

  for (std::int64_t j = 0; j < padded.dim(1); j++) {
    for (std::int64_t i = 0; i < padded.dim(0); i++) {
      if (i == 0 || i == 3 || j == 0 || j == 4) {
        EXPECT_TRUE(padded(i, j).EqualTo(0));
      } else {
        EXPECT_TRUE(padded(i, j).EqualTo(values(i - 1, j - 1)));
      }
    }
  }
}

TEST_F(TestTensor, PadLessThanTwoDimensions) {
  xt::xarray<Expression> values{{1, 2, 3}, {4, 5, 6}};
  Tensor tensor{values};
  Tensor padded{tensor.Pad({1, 1})};

  ASSERT_EQ(padded.dims().size(), 2u);
  EXPECT_EQ(padded.dim(0), 4);
  EXPECT_EQ(padded.dim(1), 3);

  for (std::int64_t j = 0; j < padded.dim(1); j++) {
    for (std::int64_t i = 0; i < padded.dim(0); i++) {
      if (i == 0 || i == 3) {
        EXPECT_TRUE(padded(i, j).EqualTo(0));
      } else {
        EXPECT_TRUE(padded(i, j).EqualTo(values(i - 1, j)));
      }
    }
  }
}

TEST_F(TestTensor, PadDifferentDimensions) {
  xt::xarray<Expression> values{{1, 2, 3}, {4, 5, 6}};
  Tensor tensor{values};
  Tensor padded{tensor.Pad({1, 3, 2, 4})};

  ASSERT_EQ(padded.dims().size(), 2u);
  EXPECT_EQ(padded.dim(0), 5);
  EXPECT_EQ(padded.dim(1), 10);

  for (std::int64_t j = 0; j < padded.dim(1); j++) {
    for (std::int64_t i = 0; i < padded.dim(0); i++) {
      if (i == 0 || i >= 3 || j <= 2 || j >= 6) {
        EXPECT_TRUE(padded(i, j).EqualTo(0));
      } else {
        EXPECT_TRUE(padded(i, j).EqualTo(values(i - 1, j - 3)));
      }
    }
  }
}

TEST_F(TestTensor, PadHigherDimensions) {
  xt::xarray<Expression> values{{{{1, 2, 3}, {4, 5, 6}}}};
  Tensor tensor{values};
  Tensor padded{tensor.Pad({0, 0, 1, 3, 0, 0, 2, 4})};

  ASSERT_EQ(padded.dims().size(), 4u);
  EXPECT_EQ(padded.dim(0), 1);
  EXPECT_EQ(padded.dim(1), 1);
  EXPECT_EQ(padded.dim(2), 5);
  EXPECT_EQ(padded.dim(3), 10);

  for (std::int64_t l = 0; l < padded.dim(3); l++) {
    for (std::int64_t k = 0; k < padded.dim(2); k++) {
      for (std::int64_t j = 0; j < padded.dim(1); j++) {
        for (std::int64_t i = 0; i < padded.dim(0); i++) {
          if (i == 0 || i >= 3 || j <= 2 || j >= 6) {
            EXPECT_TRUE(padded(i, j, k).EqualTo(0));
          } else {
            EXPECT_TRUE(padded(i, j, k).EqualTo(values(i, j, k - 1, l - 3)));
          }
        }
      }
    }
  }
}

TEST_F(TestTensor, PaddOdd) {
  xt::xarray<Expression> values{{1, 2, 3}, {4, 5, 6}};
  Tensor tensor{values};
  EXPECT_THROW(Tensor{tensor.Pad({1, 2, 3, 4, 5})}, std::out_of_range);
}
