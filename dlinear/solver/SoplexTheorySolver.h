/**
 * @file SoplexTheorySolver.h
 * @author dlinear
 * @date 24 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_SOPLEXTHEORYSOLVER_H_
#define DLINEAR5_DLINEAR_SOLVER_SOPLEXTHEORYSOLVER_H_

#include <set>
#include <vector>
#include <map>
#include <functional>
#include <utility>
#include <atomic>
#include <iostream>

#include "dlinear/solver/Context.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/Config.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/soplex.h"

namespace dlinear {

class SoplexTheorySolver {
 public:
  SoplexTheorySolver() = delete;
  explicit SoplexTheorySolver(const Config &config);

  /// Checks consistency. Returns true if there is a satisfying
  /// assignment. Otherwise, return false.
  int CheckSat(const Box &box, const std::vector<Literal> &assertions,
               soplex::SoPlex *prob,
               const soplex::VectorRational &lower,
               const soplex::VectorRational &upper,
               const std::map<int, Variable> &var_map);

  /**
   * Get a satisfying Model.
   * @return satisfying Model
   */
  [[nodiscard]] const Box &GetModel() const;

  /**
   * Get a list of used constraints.
   * @return list of used constraints
   */
  [[nodiscard]] const LiteralSet &GetExplanation() const;

 private:
  const Config &config_; ///< Configuration of the solver
  Box model_; ///< Satisfying Model
  LiteralSet explanation_; ///< List of used constraints
  mpq_class precision_; ///< Precision of the delta solver
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_SOPLEXTHEORYSOLVER_H_
