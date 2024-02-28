/**
 * @file TestPicosatSatSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
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
  PredicateAbstractor pa_;
  const Variable x_{"x"}, y_{"y"};
  const Formula f_{x_ > 1};
  const Formula f2_{!(y_ > 2)};
  const Formula f3_{x_ + y_ <= 3};
  const Formula f4_{f_ || f2_ || f3_};
  explicit TestPicosatSatSolver(Config::LPSolver lp_solver = dlinear::Config::LPSolver::QSOPTEX) : config_{} {
    DLINEAR_LOG_INIT_VERBOSITY(2);
    config_.m_lp_solver() = lp_solver;
    config_.m_filename() = "test.smt2";
    config_.m_format() = Config::Format::AUTO;
  }
};

TEST_F(TestPicosatSatSolver, ConstructorDefault) { PicosatSatSolver s{pa_}; }

TEST_F(TestPicosatSatSolver, ConstructorConfig) { PicosatSatSolver s{pa_, config_}; }

TEST_F(TestPicosatSatSolver, AddFormula) {
  PicosatSatSolver s{pa_, config_};
  s.AddFormula(f_);

  EXPECT_EQ(s.theory_literals().size(), 1u);
  EXPECT_EQ(pa_.var_to_formula_map().size(), 1u);
}

TEST_F(TestPicosatSatSolver, AddClauseLiteral) {
  PicosatSatSolver s{pa_, config_};
  s.AddClause(Formula{Variable{"x_", Variable::Type::BOOLEAN}});

  EXPECT_EQ(s.theory_literals().size(), 1u);
  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}

TEST_F(TestPicosatSatSolver, AddClauseDisjunction) {
  PicosatSatSolver s{pa_, config_};
  s.AddClause(Formula{Variable{"x_", Variable::Type::BOOLEAN}} || Formula{Variable{"y_", Variable::Type::BOOLEAN}});

  EXPECT_EQ(s.theory_literals().size(), 2u);
  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}
