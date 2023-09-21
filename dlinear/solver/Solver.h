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

  /**
   * Check the satisfiability of the current context.
   * @return SolverOutput
   */
  SolverOutput CheckSat();

 private:
  const Config config_;
  SolverGuard guard_;
  Context context_;
  SolverOutput output_;

  bool ParseInput();
  bool ParseSmt2();
  bool ParseMps();
  void CheckSatCore();
  void CheckObjCore();
};

}  // namespace dlinear
