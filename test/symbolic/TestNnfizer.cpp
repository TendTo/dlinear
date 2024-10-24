/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "TestSymbolicUtils.h"
#include "dlinear/symbolic/Nnfizer.h"

using dlinear::Nnfizer;

class NnfizerTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};

  const Config config_{};
  const Nnfizer nnfizer_{config_};
};

TEST_F(NnfizerTest, NNFNoChanges) {
  // No Changes: True
  EXPECT_PRED2(FormulaEqual, nnfizer_(Formula::True()), Formula::True());

  // No Changes: False
  EXPECT_PRED2(FormulaEqual, nnfizer_(Formula::False()), Formula::False());

  // No Changes: Variables
  EXPECT_PRED2(FormulaEqual, nnfizer_(Formula{b1_}), Formula{b1_});
  EXPECT_PRED2(FormulaEqual, nnfizer_(!b1_), !b1_);

  // No Changes: x ≥ y ∧ y ≤ z
  const Formula f1{x_ >= y_ && y_ <= z_};
  EXPECT_PRED2(FormulaEqual, nnfizer_(f1), f1);

  // No Changes.: x > y ∨ y < z
  const Formula f2{x_ > y_ || y_ < z_};
  EXPECT_PRED2(FormulaEqual, nnfizer_(f2), f2);

  // No Changes: ∀x. x + y ≥ x
  const Formula f4{forall({x_}, x_ + y_ >= x_)};
  EXPECT_PRED2(FormulaEqual, nnfizer_(f4), f4);
  EXPECT_PRED2(FormulaEqual, nnfizer_(!f4), !f4);
}

TEST_F(NnfizerTest, NNFRelational) {
  // ¬(x ≥ y) ∧ ¬(y ≤ z)  ==>  ¬(x ≥ y) ∧ ¬(y ≤ z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ >= y_) && !(y_ <= z_)), !(x_ >= y_) && !(y_ <= z_));

  // ¬(x ≥ y ∧ y ≤ z)  ==>  ¬(x ≥ y) ∨ ¬(y ≤ z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ >= y_ && y_ <= z_)), !(x_ >= y_) || !(y_ <= z_));

  // ¬(x > y) ∨ ¬(y < z)  ==>  ¬(x > y) ∨ ¬(y < z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ > y_) || !(y_ < z_)), !(x_ > y_) || !(y_ < z_));

  // ¬(x > y ∨ y < z)  ==>  ¬(x > y) ∧ ¬(y < z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ > y_ || y_ < z_)), !(x_ > y_) && !(y_ < z_));

  // ¬(x ≠ y) ∧ ¬(y = z)  ==>  ¬(x ≠ y) ∧ ¬(y = z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ != y_) && !(y_ == z_)), !(x_ != y_) && !(y_ == z_));

  // ¬(x ≠ y ∧ y = z)  ==>  ¬(x ≠ y) ∧ ¬(y = z)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(x_ != y_ && y_ == z_)), !(x_ != y_) || !(y_ == z_));
}

TEST_F(NnfizerTest, NNFBoolean) {
  // ¬(b₁ ∨ ¬(b₂ ∧ b₃))  ==>  ¬b₁ ∧ b₂ ∧ b₃
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(b1_ || !(b2_ && b3_))), !b1_ && b2_ && b3_);

  // ¬(b₁ ∨ ¬(b₂ ∨ b₃))  ==>  ¬b₁ ∧ (b₂ ∨ b₃)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(b1_ || !(b2_ || b3_))), !b1_ && (b2_ || b3_));

  // ¬(b₁ ∧ ¬(b₂ ∨ b₃))  ==>  ¬b₁ ∨ b₂ ∨ b₃
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(b1_ && !(b2_ || b3_))), !b1_ || b2_ || b3_);

  // ¬(b₁ ∧ ¬(b₂ ∧ b₃))  ==>  ¬b₁ ∨ (b₂ ∧ b₃)
  EXPECT_PRED2(FormulaEqual, nnfizer_(!(b1_ && !(b2_ && b3_))), !b1_ || (b2_ && b3_));
}