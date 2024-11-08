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
#include "test/solver/TestSolverUtils.h"

using dlinear::Box;
using dlinear::Config;
using dlinear::Context;
using dlinear::Formula;
using dlinear::GetFiles;
using dlinear::LpResult;
using dlinear::LpSolver;
using dlinear::Variable;
using dlinear::mps::MpsDriver;

class TestLpSolver : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;
  std::unique_ptr<LpSolver> lp_solver_;
  std::unique_ptr<Context> context_;

  TestLpSolver() {
    const auto& [lp_solver, filename, precision] = GetParam();
    config_.m_precision() = precision;
    config_.m_complete() = false;
    config_.m_format() = Config::Format::MPS;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_verify() = true;
    config_.m_bound_propagation_type() = Config::BoundPropagationType::AUTO;
    lp_solver_ = LpSolver::GetInstance(config_);
    context_ = std::make_unique<Context>(config_);
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestLpSolver, TestLpSolver,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(GetFiles("test/solver/mps")),
                                            ::testing::Values(0.0)));

TEST_P(TestLpSolver, MpsInputAgainstExpectedOutput) {
  MpsDriver driver{*context_};
  driver.ParseFile(config_.filename());
  for (const Formula& assertion : context_->assertions()) {
    for (const Variable& var : assertion.GetFreeVariables()) {
      lp_solver_->AddColumn(var);
    }
    lp_solver_->AddRow(assertion);
  }
  lp_solver_->Consolidate();
  mpq_class precision{config_.precision()};
  const LpResult result = lp_solver_->Optimise(precision);
  ASSERT_EQ(result, context_->GetInfo(":status") == "sat" ? LpResult::OPTIMAL : LpResult::INFEASIBLE);
  Box model{context_->model()};

  if (result == LpResult::OPTIMAL && config_.precision() == 0) {
    ASSERT_TRUE(context_->Verify(model));
  }
}
