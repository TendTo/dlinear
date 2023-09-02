/**
 * @file gmp.cpp
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 */

#include "api.h"

#include <utility>

#include "dlinear/solver/Context.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/infty.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"

using tl::optional;

namespace dlinear {

void InitSolver(const Config &config) {
  InitSolver(config.lp_solver());
}

void InitSolver(Config::LPSolver lp_solver) {
  if (lp_solver == Config::QSOPTEX) {
    qsopt_ex::QSXStart();
    InftyStart(mpq_INFTY, mpq_NINFTY);
  } else if (lp_solver == Config::SOPLEX) {
    InftyStart(soplex::infinity);
  } else {
    DLINEAR_UNREACHABLE();
  }
  Expression::InitConstants();
}

void DeInitSolver(const Config &config) {
  DeInitSolver(config.lp_solver());
}

void DeInitSolver(Config::LPSolver lp_solver) {
  Expression::DeInitConstants();
  InftyFinish();
  if (lp_solver == Config::QSOPTEX) {
    qsopt_ex::QSXFinish();
  }
}

optional <Box> CheckSatisfiability(const Formula &f, const double delta) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, config);
}

optional <Box> CheckSatisfiability(const Formula &f, const Config &config) {
  mpq_class actual_precision = config.precision();
  Context context{config};
  for (const Variable &v : f.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(f);
  return context.CheckSat(&actual_precision);
}

bool CheckSatisfiability(const Formula &f, const double delta, Box *const box) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, config, box);
}

bool CheckSatisfiability(const Formula &f, Config config, Box *const box) {
  const optional <Box> result{CheckSatisfiability(f, std::move(config))};
  if (result) {
    DLINEAR_ASSERT(box, "box must not be a nullptr");
    *box = *result;
    return true;
  } else {
    return false;
  }
}

optional <Box> Minimize(const Expression &objective, const Formula &constraint, double delta) {
  Config config;
  config.mutable_precision() = delta;
  return Minimize(objective, constraint, config);
}

optional <Box> Minimize(const Expression &objective, const Formula &constraint, Config config) {
  mpq_class actual_precision = config.precision();
  Context context{std::move(config)};
  for (const Variable &v : constraint.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  for (const Variable &v : objective.GetVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(constraint);
  context.Minimize(objective);
  return context.CheckSat(&actual_precision);
}

bool Minimize(const Expression &objective, const Formula &constraint, const double delta, Box *const box) {
  Config config;
  config.mutable_precision() = delta;
  return Minimize(objective, constraint, config, box);
}

bool Minimize(const Expression &objective, const Formula &constraint, Config config, Box *const box) {
  const optional <Box> result{
      Minimize(objective, constraint, std::move(config))};
  if (result) {
    DLINEAR_ASSERT(box, "box must not be a nullptr");
    *box = *result;
    return true;
  } else {
    return false;
  }
}

}  // namespace dlinear

