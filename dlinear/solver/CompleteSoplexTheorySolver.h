/**
 * @file CompleteSoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Complete version of SoplexTheorySolver.
 *
 * The LP solver used is Soplex.
 * This solver is complete. It means that it will always solve the linear problem exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <optional>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class CompleteSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit CompleteSoplexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  std::optional<LiteralSet> EnableLiteral(const Literal& lit) override;

  void AddVariable(const Variable& var) override;

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision, LiteralSet& explanation) override;

  void Reset(const Box& box) override;

 protected:
  SatResult SpxCheckSat(mpq_class* actual_precision, LiteralSet& explanation);

  bool SetSPXVarBound(const Bound& bound, int spx_col) override;

  void UpdateExplanationStrict(LiteralSet& explanation);

  void Consolidate() override;

  int strict_variable_idx() const;

  std::vector<std::set<soplex::Rational>> spx_nq_;  ///< Vector that maps each var to the set of values they can't take
  std::vector<int> enabled_strict_theory_rows_;     ///< Vector of enabled strict theory rows
  std::map<Variable::Id, std::vector<int>> var_to_enabled_theory_rows_;  ///< variable id -> theory row
  std::vector<int> nq_row_to_theory_rows_;  ///< Index of row with a non-equal-to constraint in the order they appear
                                             ///< mapped to the corresponding spx_row
};

}  // namespace dlinear
