/**
 * @file gmp.cpp
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 */

#include "api.h"

#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/solver/Context.h"
#include "dlinear/util/exception.h"

using std::optional;

namespace dlinear {

optional<Box> CheckSatisfiability(const Formula &f, const double delta) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, config);
}

optional<Box> CheckSatisfiability(const Formula &f, const Config &config) {
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

bool CheckSatisfiability(const Formula &f, const Config &config, Box *const box) {
  const optional<Box> result{CheckSatisfiability(f, config)};
  if (result) {
    DLINEAR_ASSERT(box, "box must not be a nullptr");
    *box = *result;
    return true;
  } else {
    return false;
  }
}

optional<Box> Minimize(const Expression &objective, const Formula &constraint, double delta) {
  Config config;
  config.mutable_precision() = delta;
  return Minimize(objective, constraint, config);
}

optional<Box> Minimize(const Expression &objective, const Formula &constraint, const Config &config) {
  mpq_class actual_precision = config.precision();
  Context context{config};
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

bool Minimize(const Expression &objective, const Formula &constraint, const Config &config, Box *const box) {
  const optional<Box> result{Minimize(objective, constraint, config)};
  if (result) {
    DLINEAR_ASSERT(box, "box must not be a nullptr");
    *box = *result;
    return true;
  } else {
    return false;
  }
}

}  // namespace dlinear
