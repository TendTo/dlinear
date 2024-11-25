/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * QfLraTheorySolver class.
 */
#pragma once

#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/solver/theory_solver/qf_lra/BoundVector.h"

namespace dlinear {

/**
 * Ensure the Quantifier-Free Linear Real Algebra theory literals are consistent.
 */
class QfLraTheorySolver : public TheorySolver {
 public:
  explicit QfLraTheorySolver(const PredicateAbstractor& predicate_abstractor,
                             const std::string& class_name = "QfLraTheorySolver");

  /** @getter{bounds over the real variables, QfLraTheorySolver} */
  [[nodiscard]] const BoundVectorMap& vars_bounds() const { return vars_bounds_; }

 protected:
  BoundVectorMap vars_bounds_;  ///< Bounds of the real variables. Reset to the checkpoint bounds with backtracking
  BoundVectorMap vars_bounds_checkpoint_;  ///< Checkpoint bounds of the real variables. Won't change with backtracking
};

}  // namespace dlinear
