/**
 * @file SmtSolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief SmtSolver class.
 *
 * This class provides an easy interface for using the underling solver.
 * Once the correct configuration is set, the user can simply call
 * `SmtSolver::CheckSat()` to get the result.
 * It will handle the parsing of the input.
 */
#pragma once

#include <string>

#include "dlinear/solver/Context.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * This class provides an easy interface for using the underling solver.
 * Once the correct configuration is set, and the assertions loaded,
 * the user can simply call @ref CheckSat to get the result.
 * It can handle the parsing of the input file or stream
 * @code
 * SmtSolver solver;
 * // Load the problem from the file input.smt2
 * solver.Parse("input.smt2");
 * solver.CheckSat();
 * @endcode
 * or the user can assert the constraints manually
 * @code
 * SmtSolver solver;
 * // Declare the variables
 * Variable x{"x"}, y{"y"};
 * // Assert the constraint
 * solver.Assert(x + y == 10);
 * solver.CheckSat();
 * @endcode
 * @see Config
 */
class SmtSolver {
 public:
  /**
   * Construct a new SmtSolver object with the given @p config .
   * @param config configuration of the solver
   */
  explicit SmtSolver(Config config = Config{});
  /**
   * Construct a new SmtSolver object with a default configuration ready to parse the @p filename .
   * @param filename name of the file to parse
   */
  explicit SmtSolver(const std::string &filename);
  SmtSolver(const SmtSolver &) = delete;
  SmtSolver(SmtSolver &&) noexcept = default;
  SmtSolver &operator=(const SmtSolver &) = delete;
  SmtSolver &operator=(SmtSolver &&) = delete;

  [[nodiscard]] std::string GetInfo(const std::string &key) const;
  [[nodiscard]] std::string GetOption(const std::string &key) const;
  [[nodiscard]] SmtResult GetExpected() const;

  /**
   * Assert a formula to the current context.
   *
   * The formula will be added to the context and will be checked by the solver in the next call to @ref CheckSat.
   * @param f formula to assert
   * @throw std::runtime_error if the formula is not in the correct format
   */
  void Assert(const Formula &f);

  /**
   * Parse the problem from the input indicated in the configuration.
   *
   * All the variables and assertions will be added to the context.
   * If the input contains the (check-sat) command, a satisfiability check will be performed.
   * @return output of the solver, if the input contains the (check-sat) command.
   * Otherwise, the result field will be @ref SmtResult::UNSOLVED.
   * @throw std::runtime_error if the input is not in the correct format or the files contains an unsupported command
   * @throw std::out_of_range if the file try to access undeclared variables
   */
  const SmtSolverOutput &Parse();

  /**
   * Parse the problem from a file or standard input, overriding the configuration.
   *
   * All the variables and assertions will be added to the context.
   * If the input contains the (check-sat) command, a satisfiability check will be performed.
   * @warning This overrides the input in the configuration, changing it permanently.
   * @param filename name of the file to parse or an empty string for standard input
   * @return output of the solver, if the input contains the (check-sat) command.
   * Otherwise, the result field will be @ref SmtResult::UNSOLVED.
   * @throw std::runtime_error if the input is not in the correct format or the files contains an unsupported command
   * @throw std::out_of_range if the file try to access undeclared variables
   */
  const SmtSolverOutput &Parse(const std::string &filename);

  /**
   * Check the satisfiability of the current context.
   * @return output of the solver
   */
  const SmtSolverOutput &CheckSat();

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
  /**
   * Parse the problem from the input indicated in the configuration.
   *
   * All the variables and assertions will be added to the context.
   * If the input contains the (check-sat) command, a satisfiability check will be performed.
   * @return true if the input was parsed correctly
   * @return false if there was an error parsing the input
   * @throw std::runtime_error if the input is not in the correct format or the files contains an unsupported command
   * @throw std::out_of_range if the file try to access undeclared variables
   */
  bool ParseInput();

  Config config_;            ///< Configuration of the solver.
  SmtSolverOutput output_;   ///< Output of the solver.
  Context context_;          ///< Context obtained from the input file and passed to the SAT and SMT solvers.
};

}  // namespace dlinear
