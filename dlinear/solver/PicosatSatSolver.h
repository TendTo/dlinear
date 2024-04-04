/**
 * @file PicosatSatSolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief SAT solver based on PicoSAT.
 *
 * PicoSAT is a SAT solver written in C. It is used as a library in dlinear.
 */
#pragma once

#ifndef DLINEAR_ENABLED_PICOSAT
#error PicoSAT is not enabled. Please enable it by adding "--//tools:enable_picosat" to the bazel command.
#endif

#include <picosat/picosat.h>

#include <optional>
#include <set>

#include "dlinear/solver/SatSolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"

namespace dlinear {

class PicosatSatSolver : public SatSolver {
 public:
  explicit PicosatSatSolver(PredicateAbstractor &predicate_abstractor,
                            const std::string &class_name = "PicosatSatSolver");
  ~PicosatSatSolver() override;

  void AddLiteral(const Literal &l, bool learned) override;

  void AddLearnedClause(const LiteralSet &literals) override;

  void MakeSatVar(const Variable &var) override;

  std::optional<Model> CheckSat() override;

 protected:
  void AddClauseToSat(const Formula &f) override;

 private:
  [[nodiscard]] std::set<int> GetMainActiveLiterals() const override;

  PicoSAT *const sat_{};

  bool has_picosat_pop_used_;
};

}  // namespace dlinear
