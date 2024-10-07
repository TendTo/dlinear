/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SmtSolver class.
 */
#pragma once

#include <string>

#include "dlinear/solver/Context.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
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

  /**
   * Check whether the @p model satisfies all the assertions loaded in the context.
   *
   * In other words, verifies if it is a SAT assignment for the input variables.
   * @param model assignment to check
   * @return true if the @p model satisfies all assignments
   * @return false if there is at leas an assignment not satisfied by the @p model
   */
  [[nodiscard]] bool Verify(const Box &model) const;

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

  Config config_;           ///< Configuration of the solver.
  SmtSolverOutput output_;  ///< Output of the solver.
  Context context_;         ///< Context obtained from the input file and passed to the SAT and SMT solvers.
};

}  // namespace dlinear
