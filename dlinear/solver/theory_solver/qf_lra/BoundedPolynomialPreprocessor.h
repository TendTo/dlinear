/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * BoundCheckerPreprocessor class.
 */
#pragma once

#include <iosfwd>
#include <list>
#include <map>
#include <set>
#include <span>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheoryPreprocessor.h"
#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/solver/theory_solver/qf_lra/BoundVector.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {
/**
 * This class uses some basic algebraic operations to preprocess the constraints
 * and identify violations before invoking the solver.
 */
class BoundedPolynomialPreprocessor final : public TheoryPreprocessor {
 public:
  using VarToEqBinomialMap = std::unordered_map<Variable, mpq_class>;

  /**
   * Construct a new BoundedPolynomialPreprocessor object using the @p theory_solver.
   * @param theory_solver theory solver that will use this preprocessor
   * @param var_bounds bounds over each real variable. Shared with other preprocessors
   * @param env environment containing the variable's values. Shared with other preprocessors
   * @param class_name name of the subclass of the theory preprocessor used
   */
  explicit BoundedPolynomialPreprocessor(const TheorySolver &theory_solver,
                                         const std::shared_ptr<BoundVectorMap> &var_bounds,
                                         const std::shared_ptr<Environment> &env,
                                         const std::string &class_name = "BoundedPolynomialPreprocessor");

  [[nodiscard]] Config::ExecutionStep run_on_step() const override;
  void AddVariable(const Variable &var) override;
  bool EnableLiteral(const Literal &lit, const ConflictCallback &conflict_cb) override;
  bool ProcessCore(const ConflictCallback &conflict_cb) override;
  void Backtrack() override;

  /** @getter{bounds of the variables in the LP solver, BoundCheckerPreprocessor} */
  [[nodiscard]] const BoundVectorMap &var_bounds() const { return *var_bounds_; }
  /** @getter{propagated environment containing the variable's values, BoundCheckerPreprocessor} */
  [[nodiscard]] const Environment &env() const { return *env_; }

  /**
   * Propagate the bounds of the variables in the given formula.
   *
   * It only works for formulas of the form @f$ \sum_{i = 1}^n a_i x_i = c @f$
   * where the values @f$ a_i, c \in \mathbb{R} @f$ are known,
   * and all but exactly one variable among the @f$ x_i @f$ have a value assigned in the @ref env_.
   * Their values will be used to assign the value to the last unknown variable.
   * The explanation will be added to the bound vector.
   * If the new assignment is incompatible with the current one, a conflict is found.
   * @pre the formula is of the form @f$ \sum_{i = 1}^n a_i x_i = c @f$
   * @pre all but exactly one of the variables have a value assigned in the @ref env_
   * @param lit theory literal corresponding to the formula to propagate
   * @param var_to_propagate the variable to propagate
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if the propagation was successful
   * @return false if a conflict was detected
   */
  bool PropagateEqPolynomial(const Literal &lit, const Variable &var_to_propagate, const ConflictCallback &conflict_cb);
  /**
   * Propagate the bounds of the variables in the given formula.
   *
   * It only works for formulas of the form @f$ \sum_{i = 1}^n a_i x_i \bowtie c @f$
   * where the values @f$ a_i, c \in \mathbb{R} @f$ are known, @f$ \bowtie \in \{<, \le, =, \ge, >\} @f$,
   * and all but exactly one variable among the @f$ x_i @f$ are bounded.
   * Their values will be used to assign the value to the last unknown variable,
   * and a dependency edge will be added to the graph.
   * If the new assignment is incompatible with the current one, a conflict is found.
   * @pre the formula is of the form @f$ \sum_{i = 1}^n a_i x_i \bowtie c @f$
   * @pre all but exactly one of the variables are bounded
   * @param lit theory literal corresponding to the formula to propagate
   * @param var_to_propagate the variable to propagate
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if the propagation was successful
   * @return false if a conflict was detected
   */
  bool PropagateBoundsPolynomial(const Literal &lit, const Variable &var_to_propagate,
                                 const ConflictCallback &conflict_cb);

  bool PropagateBoundsPolynomial(const Literal &lit, const Variable &var_to_propagate,
                                 const std::vector<Bound> &assumptions, const ConflictCallback &conflict_cb);

 protected:
  /**
   * Go through all the @ref var_bounds_ to set the @ref env_.
   *
   * Every time a variable has an active equality bound, the value is set in the environment @ref env_ .
   */
  void SetEnvironmentFromBounds();

  [[nodiscard]] const Variable *ShouldPropagateEqPolynomial(const Literal &lit) const;
  [[nodiscard]] const Variable *ShouldPropagateEqPolynomial(const Formula &formula) const;
  [[nodiscard]] const Variable *ShouldPropagateBoundsPolynomial(const Literal &lit) const;
  [[nodiscard]] const Variable *ShouldPropagateBoundsPolynomial(const Formula &formula) const;

  bool PropagateEqConstraints(std::list<Literal> &enabled_literals, const ConflictCallback &conflict_cb);
  bool PropagateBoundConstraints(std::list<Literal> &enabled_literals, const ConflictCallback &conflict_cb);

  [[nodiscard]] std::pair<Variable, Variable> ExtractBoundEdge(const Formula &formula) const;
  /**
   * Given a formula of the form @f$ ax = by @f$, with @f$ a, b \in \mathbb{R} @f$ being constants,
   * extract the coefficient @f$ c \coloneqq cx = y @f$.
   *
   * Variables enjoy total ordering between them.
   * The leftmost variable is always the smallest.
   * @param formula the formula to extract the coefficient from
   * @return the coefficient @f$ c @f$
   */
  [[nodiscard]] mpq_class ExtractEqBoundCoefficient(const Formula &formula) const;

  /** Vector used to store the mpq_class elements obtained from more complex constraints */
  const mpq_class *StoreTemporaryMpq(const mpq_class &value);

 private:
  std::list<mpq_class>
      temporary_mpq_vector_;  ///< Vector used to store temporary mpq values obtained from more complex constraints

  std::shared_ptr<BoundVectorMap> var_bounds_;  ///< Bounds over each real variable. Shared with other preprocessors
  std::shared_ptr<Environment> env_;  ///< Environment containing the variable's values. Shared with other preprocessors

  LiteralSet enabled_literals_;  ///< Literals that should be evaluated
};

std::ostream &operator<<(std::ostream &os, const BoundedPolynomialPreprocessor &preprocessor);
}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::BoundedPolynomialPreprocessor)

#endif
