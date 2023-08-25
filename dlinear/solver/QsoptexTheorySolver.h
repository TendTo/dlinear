/**
 * @file QsoptexTheorySolver.h
 * @author dlinear
 * @date 20 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_QSOPTEXTHEORYSOLVER_H_
#define DLINEAR5_DLINEAR_SOLVER_QSOPTEXTHEORYSOLVER_H_

#include <set>
#include <vector>
#include <map>
#include <functional>
#include <utility>
#include <limits>

#include "dlinear/util/Config.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/exception.h"
#include "dlinear/solver/Context.h"

namespace dlinear {

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob,
                                               mpq_t *x,
                                               const mpq_t infeas,
                                               const mpq_t delta,
                                               void *data);

/**
 * QsoptexTheorySolver class.
 * It implements the theory solver for linear theory over the Reals.
 */
class QsoptexTheorySolver {
 public:
  QsoptexTheorySolver() = delete;
  explicit QsoptexTheorySolver(const Config &config);

  /**
   * Checks consistency. Returns true if there is a satisfying, otherwise
   * returns false.
   * @param box box of variables to check
   * @param assertions assertions to verify with the assignment
   * @param prob
   * @param var_map
   * @param actual_precision actual delta precision to use
   * @return
   */
  int CheckSat(const Box &box, const std::vector<Literal> &assertions,
               const mpq_QSprob prob,
               const std::map<int, Variable> &var_map,
               mpq_class *actual_precision);

  int CheckOpt(const Box &box,
               mpq_class *obj_lo,
               mpq_class *obj_up,
               const std::vector<Literal> &assertions,
               const mpq_QSprob prob,
               const std::map<int, Variable> &var_map);

  /** Get a satisfying model. */
  [[nodiscard]] const Box &GetModel() const;

  /** Get a list of used constraints. */
  [[nodiscard]] const LiteralSet &GetExplanation() const;

 private:
  const Config &config_;
  Box model_;
  LiteralSet explanation_;
  mpq_class precision_;

  friend void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob,
                                             mpq_t *x,
                                             const mpq_t infeas,
                                             const mpq_t delta,
                                             void *data);
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_QSOPTEXTHEORYSOLVER_H_
