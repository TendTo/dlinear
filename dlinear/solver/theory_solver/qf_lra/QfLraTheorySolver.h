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

class QfLraTheorySolver : public TheorySolver {
 public:
  explicit QfLraTheorySolver(const PredicateAbstractor& predicate_abstractor,
                             const std::string& class_name = "QfLraTheorySolver");

 protected:
  BoundVectorMap vars_bounds_;
};

}  // namespace dlinear
