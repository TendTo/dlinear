/**
 * @file SmtSolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief SmtSolver interface class.
 *
 * This class provides an easy interface for using the underling solver.
 * Once the correct configuration is set, the user can simply call
 * `SmtSolver::CheckSat()` to get the result.
 * It will handle the parsing of the input.
 */
#pragma once

#include <iostream>
#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/Context.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/solver/SolverGuard.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class SmtSolver {
 public:
  SmtSolver();
  explicit SmtSolver(const std::string &filename);
  explicit SmtSolver(Config config);
  SmtSolver(const SmtSolver &) = delete;
  SmtSolver(SmtSolver &&) noexcept = default;
  SmtSolver &operator=(const SmtSolver &) = delete;
  SmtSolver &operator=(SmtSolver &&) = delete;

  [[nodiscard]] std::string GetInfo(const std::string &key) const;
  [[nodiscard]] std::string GetOption(const std::string &key) const;
  [[nodiscard]] SolverResult GetExpected() const;

  /**
   * Check the satisfiability of the current context.
   * @return SmtSolverOutput
   */
  SmtSolverOutput CheckSat();

#ifdef DLINEAR_PYDLINEAR
  /**
   * Enter the solver.
   * Allows to use the with statement in python.
   * @return SmtSolver reference
   */
  SmtSolver &Enter();

  /**
   * Cleanup the infinity values forcefully.
   * It is not necessary to call this function, as the destructor will take care of it.
   * However, it is useful for the python bindings, since the garbage collector
   * might not call the destructor in time.
   * It is idempotent, so it can be called multiple times without any problem.
   */
  void Exit();
#endif

 private:
  Config config_;            ///< Configuration of the solver.
  const SolverGuard guard_;  ///< Takes care of initializing and de-initializing the correct infinity values.
  Context context_;          ///< Context obtained from the input file and passed to the SAT and SMT solvers.
  SmtSolverOutput output_;   ///< Output of the solver.

  bool ParseInput();
  void CheckSatCore();
  void CheckObjCore();
};

}  // namespace dlinear
