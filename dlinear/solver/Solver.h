/**
 * @file Solver.h
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 * @brief Solver interface class.
 *
 * This class provides an easy interface for using the underling solver.
 * Once the correct configuration is set, the user can simply call
 * `Solver::CheckSat()` to get the result.
 * It will handle the parsing of the input.
 */
#pragma once

#include <iostream>
#include <string>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/Context.h"
#include "dlinear/solver/SolverGuard.h"
#include "dlinear/solver/SolverOutput.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class Solver {
 public:
  Solver();
  explicit Solver(const std::string &filename);
  explicit Solver(Config config);
  Solver(const Solver &) = delete;
  Solver(Solver &&) = delete;
  Solver &operator=(const Solver &) = delete;
  Solver &operator=(Solver &&) = delete;

  [[nodiscard]] std::string GetInfo(const std::string &key) const;
  [[nodiscard]] std::string GetOption(const std::string &key) const;
  [[nodiscard]] SolverResult GetExpected() const;

  /**
   * Check the satisfiability of the current context.
   * @return SolverOutput
   */
  SolverOutput CheckSat();

  void Visualize();

#ifdef DLINEAR_PYDLINEAR
  /**
   * Enter the solver.
   * Allows to use the with statement in python.
   * @return Solver reference
   */
  Solver &Enter();

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
  const Config config_;  ///< Configuration of the solver.
  SolverGuard guard_;    ///< Takes care of initializing and de-initializing the correct infinity values.
  Context context_;      ///< Context obtained from the input file and passed to the SAT and SMT solvers.
  SolverOutput output_;  ///< Output of the solver.

  bool ParseInput();
  bool ParseSmt2();
  bool ParseMps();
  void CheckSatCore();
  void CheckObjCore();
};

}  // namespace dlinear
