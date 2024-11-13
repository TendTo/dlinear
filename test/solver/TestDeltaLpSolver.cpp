/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>

#include "dlinear/parser/mps/Driver.h"
#include "dlinear/solver/theory_solver/qf_lra/LpSolver.h"
#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Box;
using dlinear::Config;
using dlinear::Context;
using dlinear::Formula;
using dlinear::GetFiles;
using dlinear::LinearFormulaFlattener;
using dlinear::LpResult;
using dlinear::LpSolver;
using dlinear::Variable;
using dlinear::mps::MpsDriver;

class TestDeltaLpSolver : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;
  std::unique_ptr<LpSolver> lp_solver_;
  std::unique_ptr<Context> context_;

  TestDeltaLpSolver() {
    const auto& [lp_solver, filename, precision] = GetParam();
    config_.m_precision() = precision;
    config_.m_complete() = false;
    config_.m_format() = Config::Format::MPS;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_verify() = true;
    lp_solver_ = LpSolver::GetInstance(config_);
    context_ = std::make_unique<Context>(config_);
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestDeltaLpSolver, TestDeltaLpSolver,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(GetFiles("test/solver/mps")),
                                            ::testing::Values(0.1, 0.001)));

TEST_P(TestDeltaLpSolver, LpInputAgainstExpectedOutput) {
  MpsDriver driver{*context_};
  driver.ParseFile(config_.filename());
  for (const Formula& assertion : context_->assertions()) {
    for (const Variable& var : assertion.GetFreeVariables()) {
      if (!lp_solver_->var_to_col().contains(var)) lp_solver_->AddColumn(var);
    }
    Formula flat_assertion = LinearFormulaFlattener{config_}.Flatten(assertion);
    if (is_negation(flat_assertion))
      flat_assertion =
          get_lhs_expression(get_operand(flat_assertion)) >= get_rhs_expression(get_operand(flat_assertion));
    lp_solver_->AddRow(flat_assertion);
  }
  lp_solver_->Consolidate();
  mpq_class precision{config_.precision()};
  lp_solver_->EnableRows();
  const LpResult result = lp_solver_->Optimise(precision);

  if (result == LpResult::ERROR) GTEST_SKIP();
  ASSERT_EQ(~result, context_->GetInfo(":status") == "sat" ? LpResult::DELTA_OPTIMAL : LpResult::INFEASIBLE);
  EXPECT_LE(precision, config_.precision());
  EXPECT_TRUE(result != LpResult::OPTIMAL || precision == 0);

  if (result == LpResult::OPTIMAL) {
    Box model{context_->model()};
    for (int i = 0; i < static_cast<int>(lp_solver_->solution().size()); ++i) {
      model.Add(lp_solver_->col_to_var().at(i));
      model[lp_solver_->col_to_var().at(i)] = lp_solver_->solution().at(i);
    }
    ASSERT_TRUE(context_->Verify(model));
  }
}