/**
 * @file TestPicosatSatSolver.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/PicosatSatSolver.h"
#include "dlinear/solver/SolverGuard.h"
#include "dlinear/util/Infinity.h"

using dlinear::Config;
using dlinear::Formula;
using dlinear::Infinity;
using dlinear::PicosatSatSolver;
using dlinear::PredicateAbstractor;
using dlinear::SatSolver;
using dlinear::SolverGuard;
using dlinear::Variable;
using std::unique_ptr;

class TestPicosatSatSolver : public ::testing::Test {
 protected:
  Config config_;
  SolverGuard guard{config_};
  PredicateAbstractor* pa_;
  const Variable x_{"x"}, y_{"y"};
  const Formula f_{x_ > 1};
  const Formula f2_{!(y_ > 2)};
  const Formula f3_{x_ + y_ <= 3};
  const Formula f4_{f_ || f2_ || f3_};
  explicit TestPicosatSatSolver(Config::LPSolver lp_solver = dlinear::Config::QSOPTEX) : config_{} {
    DLINEAR_LOG_INIT_VERBOSITY(2);
    config_.mutable_lp_solver() = lp_solver;
    config_.mutable_filename() = "test.smt2";
    config_.mutable_format() = Config::Format::AUTO;
  }
  PredicateAbstractor& pa() { return *pa_; }
  void SetUp() override { pa_ = new PredicateAbstractor{}; }
  void TearDown() override { delete pa_; }
};

TEST_F(TestPicosatSatSolver, ConstructorDefault) { PicosatSatSolver s{pa()}; }

TEST_F(TestPicosatSatSolver, ConstructorConfig) { PicosatSatSolver s{pa(), config_}; }

TEST_F(TestPicosatSatSolver, AddFormula) {
  PicosatSatSolver s{pa(), config_};
  s.AddFormula(f_);

  EXPECT_EQ(s.theory_literals().size(), 1u);
  EXPECT_EQ(pa().var_to_formula_map().size(), 1u);
}

TEST_F(TestPicosatSatSolver, AddClauseLiteral) {
  PicosatSatSolver s{pa(), config_};
  s.AddClause(Formula{Variable{"x_", Variable::Type::BOOLEAN}});

  EXPECT_EQ(s.theory_literals().size(), 1u);
  EXPECT_EQ(pa().var_to_formula_map().size(), 0u);
}

TEST_F(TestPicosatSatSolver, AddClauseDisjunction) {
  PicosatSatSolver s{pa(), config_};
  s.AddClause(Formula{Variable{"x_", Variable::Type::BOOLEAN}} || Formula{Variable{"y_", Variable::Type::BOOLEAN}});

  EXPECT_EQ(s.theory_literals().size(), 2u);
  EXPECT_EQ(pa().var_to_formula_map().size(), 0u);
}
