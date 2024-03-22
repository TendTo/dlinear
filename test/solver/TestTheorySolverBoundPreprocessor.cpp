/**
 * @file TestTheorySolverBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <numeric>
#include <vector>

#include "dlinear/solver/TheorySolver.h"
#include "dlinear/solver/TheorySolverBoundPreprocessor.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Config;
using dlinear::Formula;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::PredicateAbstractor;
using dlinear::TheorySolver;
using dlinear::TheorySolverBoundPreprocessor;
using dlinear::TheorySolverBoundVector;
using dlinear::TheorySolverBoundVectorVector;
using dlinear::Variable;

class MockTheorySolver : public TheorySolver {
 public:
  explicit MockTheorySolver(PredicateAbstractor &abstractor, const Config &config) : TheorySolver{abstractor, config} {}
  static TheorySolver::Bound GetBoundMock(const Formula &formula) { return TheorySolver::GetBound(formula, true); }
  static bool IsSimpleBound(const Formula &formula) { return TheorySolver::IsSimpleBound(formula); }
};

class MockTheorySolverBoundPreprocessor : public TheorySolverBoundPreprocessor {
 public:
  MockTheorySolverBoundPreprocessor(PredicateAbstractor &abstractor, std::vector<Variable> &theory_cols,
                                    std::map<Variable::Id, int> &var_to_theory_col, std::vector<Literal> &theory_rows,
                                    TheorySolverBoundVectorVector &theory_bounds)
      : TheorySolverBoundPreprocessor{Config{},          abstractor,  theory_cols,
                                      var_to_theory_col, theory_rows, theory_bounds} {}
  auto ShouldEvaluate(const Formula &formula) { return TheorySolverBoundPreprocessor::ShouldEvaluate(formula); }
  auto ShouldPropagate(const Formula &formula, bool check_expr = true) {
    return TheorySolverBoundPreprocessor::ShouldPropagate(formula, check_expr);
  }
  auto ExtractEdge(const Formula &formula) { return TheorySolverBoundPreprocessor::ExtractEdge(formula); }
};

class TestTheorySolverBoundPreprocessor : public ::testing::Test {
 protected:
  const DrakeSymbolicGuard guard_;
  PredicateAbstractor pa_;
  std::vector<Variable> theory_cols_;
  std::map<Variable::Id, int> var_to_theory_col_;
  std::vector<Literal> theory_rows_;
  TheorySolverBoundVectorVector theory_bounds_;
  MockTheorySolverBoundPreprocessor bound_preprocessor_;
  const Variable x1_{"x1"}, x2_{"x2"}, x3_{"x3"}, x4_{"x4"}, x5_{"x5"}, x6_{"x6"}, x7_{"x7"}, x8_{"x8"}, x9_{"x9"},
      x10_{"x10"};
  const mpq_class inf_{100};
  const mpq_class ninf_{-100};

  TestTheorySolverBoundPreprocessor()
      : bound_preprocessor_{pa_, theory_cols_, var_to_theory_col_, theory_rows_, theory_bounds_} {
    DLINEAR_LOG_INIT_VERBOSITY(0);
  }

  void AddConstraints(std::initializer_list<Formula> formulas) {
    for (const auto &formula : formulas) {
      for (const auto &variable : formula.GetFreeVariables()) {
        if (std::find_if(theory_cols_.begin(), theory_cols_.end(),
                         [&variable](const auto &var) { return variable.equal_to(var); }) == theory_cols_.end()) {
          theory_cols_.emplace_back(variable);
          var_to_theory_col_.emplace(variable.get_id(), static_cast<int>(theory_cols_.size()) - 1);
          theory_bounds_.emplace_back(ninf_, inf_);
        }
      }
      const Formula converted_formula = pa_.Convert(formula);
      theory_rows_.emplace_back(get_variable(converted_formula), true);
      bound_preprocessor_.AddConstraint(static_cast<int>(theory_rows_.size()) - 1, formula);
      if (MockTheorySolver::IsSimpleBound(formula)) {
        auto bound = MockTheorySolver::GetBoundMock(formula);
        const auto &var = std::get<0>(bound);
        const auto &type = std::get<1>(bound);
        const auto &value = std::get<2>(bound);
        const auto it = std::find_if(theory_cols_.begin(), theory_cols_.end(),
                                     [&var](const auto &variable) { return var.equal_to(variable); });

        const int theory_col = static_cast<int>(std::distance(theory_cols_.begin(), it));
        theory_bounds_.at(theory_col).AddBound(value, type, static_cast<int>(theory_rows_.size() - 1));
      }
    }
  }
  void EnableConstraints(std::initializer_list<Formula> formulas) {
    for (int i = 0; i < static_cast<int>(formulas.size()); i++) bound_preprocessor_.EnableConstraint(i);
  }
  void AddEnableConstraints(std::initializer_list<Formula> formulas) {
    AddConstraints(formulas);
    EnableConstraints(formulas);
  }
};

TEST_F(TestTheorySolverBoundPreprocessor, Constructor) {
  TheorySolverBoundPreprocessor bound_preprocessor{Config{},           pa_,          theory_cols_,
                                                   var_to_theory_col_, theory_rows_, theory_bounds_};
  EXPECT_EQ(&bound_preprocessor.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor.theory_cols(), &theory_cols_);
  EXPECT_EQ(&bound_preprocessor.var_to_cols(), &var_to_theory_col_);
  EXPECT_EQ(&bound_preprocessor.theory_rows(), &theory_rows_);
  EXPECT_EQ(&bound_preprocessor.theory_bounds(), &theory_bounds_);
}

TEST_F(TestTheorySolverBoundPreprocessor, AddConstraints) {
  AddConstraints({x1_ == 0, x2_ == 0, x3_ == x1_ + x2_ + x4_});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_cols(), &theory_cols_);
  EXPECT_EQ(&bound_preprocessor_.var_to_cols(), &var_to_theory_col_);
  EXPECT_EQ(&bound_preprocessor_.theory_rows(), &theory_rows_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_cols().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.var_to_cols().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.theory_rows().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);

  EXPECT_EQ(bound_preprocessor_.edges().size(), 0u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 0u);
}

TEST_F(TestTheorySolverBoundPreprocessor, AddConstraintsPropagation) {
  AddConstraints({x1_ == 0, x1_ == x2_, x2_ == x3_, x3_ == 0});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_cols(), &theory_cols_);
  EXPECT_EQ(&bound_preprocessor_.var_to_cols(), &var_to_theory_col_);
  EXPECT_EQ(&bound_preprocessor_.theory_rows(), &theory_rows_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.theory_cols().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.var_to_cols().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_rows().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);

  EXPECT_EQ(bound_preprocessor_.edges().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 0u);
}

TEST_F(TestTheorySolverBoundPreprocessor, EnableConstraintsPropagation) {
  AddEnableConstraints({x1_ == 0, x1_ == x2_, x2_ == x3_, x3_ == 0});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_cols(), &theory_cols_);
  EXPECT_EQ(&bound_preprocessor_.theory_rows(), &theory_rows_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.theory_cols().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.var_to_cols().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_rows().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);

  EXPECT_EQ(bound_preprocessor_.edges().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 2);
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessSetEnvironment) {
  AddEnableConstraints({x1_ == 0, x4_ == 0});
  bound_preprocessor_.Process();

  EXPECT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 0);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], 0);
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessPropagateLinearPath) {
  const mpq_class val = 7;
  AddEnableConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_});
  bound_preprocessor_.Process();

  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 3);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessPropagateLinearPathBothEnds) {
  const mpq_class val = 7;
  AddEnableConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x4_ == val});
  bound_preprocessor_.Process();

  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 3);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessPropagateSpread) {
  const mpq_class val = 7;
  AddEnableConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x2_ == x5_, x5_ == x6_, x3_ == x7_, x1_ == x8_,
                        x8_ == x9_, x9_ == x2_});
  bound_preprocessor_.Process();

  EXPECT_EQ(bound_preprocessor_.env().size(), 9u);
  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 9);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x6_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x8_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x9_], val);
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessPropagateMultipleViolation) {
  const mpq_class val = 7;
  AddEnableConstraints({x1_ == val, x1_ == x2_, x2_ == mpq_class{val + 1}, x2_ == x3_, x3_ == x4_, x4_ == x5_,
                        x5_ == mpq_class{val + 2}, x6_ == x7_, x7_ == mpq_class{val + 3}, x7_ == x8_, x8_ == x9_,
                        x9_ == mpq_class{val + 4}, x9_ == x10_});
  const TheorySolver::Explanations explanations = bound_preprocessor_.Process();

  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 8);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val + 2);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val + 3);
  EXPECT_EQ(bound_preprocessor_.env()[x9_], val + 4);

  EXPECT_EQ(explanations.size(), 3u);
  for (const auto &explanation : explanations) {
    switch (explanation.size()) {
      case 3:
        EXPECT_THAT(explanation,
                    ::testing::UnorderedElementsAreArray({theory_rows_[0], theory_rows_[1], theory_rows_[2]}));
        break;
      case 4:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAreArray(
                                     {theory_rows_[8], theory_rows_[9], theory_rows_[10], theory_rows_[11]}));
        break;
      case 5:
        EXPECT_THAT(explanation,
                    ::testing::UnorderedElementsAreArray(
                        {theory_rows_[2], theory_rows_[3], theory_rows_[4], theory_rows_[5], theory_rows_[6]}));
        break;
      case 6:
        EXPECT_THAT(explanation,
                    ::testing::UnorderedElementsAreArray({theory_rows_[0], theory_rows_[1], theory_rows_[3],
                                                          theory_rows_[4], theory_rows_[5], theory_rows_[6]}));
        break;
      default:
        FAIL();
    }
  }
}

TEST_F(TestTheorySolverBoundPreprocessor, ProcessEvaluateViolation) {
  DLINEAR_LOG_INIT_VERBOSITY(5);
  const mpq_class val = 7;
  AddEnableConstraints({x1_ == val, x2_ == x3_, x3_ == val, x4_ == (x1_ + x5_), x6_ == x2_, x5_ == x6_,
                        x7_ == mpq_class{val + 1}, x7_ == x4_});
  std::vector<int> enabled_rows(theory_rows_.size());
  std::iota(enabled_rows.begin(), enabled_rows.end(), 0);
  const TheorySolver::Explanations explanations = bound_preprocessor_.Process(enabled_rows);

  EXPECT_EQ(bound_preprocessor_.graph().Size(), 2u * 4);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x6_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val + 1);

  EXPECT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAreArray(theory_rows_));
}

TEST_F(TestTheorySolverBoundPreprocessor, ShouldPropagateTrue) {
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ == x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ - x1_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ + x2_ == 0));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(0 == x1_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(2 * x1_ == 3 * x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ - x2_ == 0));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(-x1_ == x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 2 * x2_ == 3 * x2_));
}

TEST_F(TestTheorySolverBoundPreprocessor, ShouldPropagateFalse) {
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(Expression{} == Expression{}));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ == 0));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(0 == x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + 1));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + x3_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ + x3_ == x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ + x1_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ + x2_ == 1));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(1 == x1_ + x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 1 == 3 * x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ - x2_ == 1));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(-x1_ == x2_ - 1));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 3 * x2_ == 3 * x2_));
}

TEST_F(TestTheorySolverBoundPreprocessor, ExtractEdge) {
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x1_ == x2_), std::tuple(x1_, x2_, 1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x1_ + x2_ == 0), std::tuple(x1_, x2_, -1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(2 * x1_ == 3 * x2_), std::tuple(x1_, x2_, mpq_class(3, 2)));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x1_ - x2_ == 0), std::tuple(x1_, x2_, 1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(-x1_ == x2_), std::tuple(x1_, x2_, -1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x1_ + x2_ == 0), std::tuple(x1_, x2_, -1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(0 == x1_ + x2_), std::tuple(x1_, x2_, -1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x2_ + x1_ == x2_ + x2_), std::tuple(x1_, x2_, 1));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(x2_ + x1_ == x2_ + x2_ - x1_), std::tuple(x1_, x2_, mpq_class(1, 2)));
  EXPECT_EQ(bound_preprocessor_.ExtractEdge(2 * x1_ + 2 * x2_ == 3 * x2_), std::tuple(x1_, x2_, mpq_class(1, 2)));
}

// EXPECT_ANY_THROW(std::cout << bound_preprocessor_ << std::endl);