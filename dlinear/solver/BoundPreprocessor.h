/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * BoundPreprocessor class.
 *
 * This class uses some basic algebraic operations to preprocess the constraints
 * and identify violations before invoking the solver.
 * Namely, the bounds are propagated through the constraints.
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
#include "dlinear/solver/BoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * This class uses some basic algebraic operations to preprocess the constraints
 * and identify violations before invoking the solver.
 */
class BoundPreprocessor {
 public:
  using Explanations = std::set<LiteralSet>;
  using VarToEqBinomialMap = std::unordered_map<Variable, mpq_class>;

  /**
   * Construct a new Bound Preprocessor object using the @p predicate_abstractor.
   * @param predicate_abstractor predicate abstractor containing the map between the variables and the literals
   */
  explicit BoundPreprocessor(const PredicateAbstractor& predicate_abstractor);

  /**
   * Add a theory variable to the preprocessor.
   *
   * It will create a new entry in the theory_bounds_ map.
   * @param var theory variable to add
   */
  void AddVariable(const Variable& var);

  /**
   * Preprocess all the @p enabled_literals.
   *
   * It will enable the literals and propagate the bounds.
   * If a conflict is detected, it will return the set of explanations.
   * Enabled literals are cached and will not be enabled again in the future.
   * @param enabled_literals literals to enable
   * @return set of explanations from the enabled literals if a conflict is detected
   * @return empty set if no conflict is detected
   */
  std::set<LiteralSet> EnableLiterals(const std::vector<Literal>& enabled_literals);
  /**
   * Preprocess all the @p enabled_literals.
   *
   * It will enable the literals and propagate the bounds.
   * If a conflict is detected, it will return the set of explanations.
   * Enabled literals are cached and will not be enabled again in the future.
   * @param enabled_literals literals to enable
   * @param[out] explanations set of explanations from the enabled literals if a conflict is detected
   */
  void EnableLiterals(const std::vector<Literal>& enabled_literals, std::set<LiteralSet>& explanation);

  /**
   * Enable the literal @p lit.
   *
   * It will enable the literal and propagate the bounds.
   * If a conflict is detected, it will return the set of explanations.
   * Enabled literals are cached and will not be enabled again in the future.
   * @param lit literal to enable
   * @return set of explanations from the enabled literal if a conflict is detected
   * @return empty set if no conflict is detected
   */
  std::set<LiteralSet> EnableLiteral(const Literal& lit);
  /**
   * Enable the literal @p lit.
   *
   * It will enable the literal and propagate the bounds.
   * If a conflict is detected, it will return the set of explanations.
   * Enabled literals are cached and will not be enabled again in the future.
   * @param lit literal to enable
   * @param[out] explanations set of explanations from the enabled literal if a conflict is detected
   */
  void EnableLiteral(const Literal& lit, std::set<LiteralSet>& explanations);

  /**
   * Process all enabled literals.
   *
   * It will process the enabled literals and propagate the bounds.
   * The bounds are propagated based on the BoundPropagationType and the formulae will be evaluated.
   * If a conflict is detected, it will return the set of explanations.
   * @return set of explanations from the enabled literals if a conflict is detected
   * @return empty set if no conflict is detected
   */
  Explanations Process();
  /**
   * Process all enabled literals.
   *
   * It will process the enabled literals and propagate the bounds.
   * The bounds are propagated based on the BoundPropagationType and the formulae will be evaluated.
   * If a conflict is detected, it will return the set of explanations.
   * @param[out] explanations set of explanations from the enabled literals if a conflict is detected
   */
  void Process(Explanations& explanations);
  /**
   * Process the enabled literals @p enabled_literals.
   *
   * It will process the enabled literals and propagate the bounds.
   * The bounds are propagated based on the BoundPropagationType and the formulae will be evaluated.
   * If a conflict is detected, it will return the set of explanations.
   * @param enabled_literals literals to enable
   * @return set of explanations from the enabled literals if a conflict is detected
   * @return empty set if no conflict is detected
   */
  Explanations Process(const LiteralSet& enabled_literals);
  /**
   * Process the enabled literals @p enabled_literals.
   *
   * It will process the enabled literals and propagate the bounds.
   * The bounds are propagated based on the BoundPropagationType and the formulae will be evaluated.
   * If a conflict is detected, it will return the set of explanations.
   * @param enabled_literals literals to enable
   * @param[out] explanations set of explanations from the enabled literals if a conflict is detected
   */
  void Process(const LiteralSet& enabled_literals, Explanations& explanations);

  /**
   * Get the active explanation for the variable @p var.
   *
   * It will return the explanation for the variable @p var, justifying the active bounds.
   * @param var variable to get the explanation for
   * @param[out] explanation explanation for the variable @p var
   */
  void GetActiveExplanation(const Variable& var, LiteralSet& explanation);

  /**
   * Set the lower and upper infinity bounds (@p lb, ub) of the variable @p var.
   *
   * All bounds currently assigned to @p var will be removed.
   * @param var variable to fix the bounds for
   * @param lb lower infinity bound
   * @param ub upper infinity bound
   */
  void SetInfinityBounds(const Variable& var, const mpq_class& lb, const mpq_class& ub);

  /**
   * Clear the preprocessor.
   *
   * It will clear the environment, the theory bounds, and the enabled literals.
   */
  void Clear();
  /**
   * Clear the preprocessor using the @p fixed_preprocessor.
   *
   * It will clear the environment, the theory bounds, and the enabled literals by copying the values from the
   * @p fixed_preprocessor.
   * @param fixed_preprocessor preprocessor to use as a reference
   */
  void Clear(const BoundPreprocessor& fixed_preprocessor);

  /** @getter{configuration, BoundPreprocessor} */
  [[nodiscard]] const Config& config() const { return config_; }
  /** @getter{bounds of the variables in the LP solver, BoundPreprocessor} */
  [[nodiscard]] const BoundVectorMap& theory_bounds() const { return theory_bounds_; }
  /** @getter{predicate abstractor, BoundPreprocessor} */
  [[nodiscard]] const PredicateAbstractor& predicate_abstractor() const { return predicate_abstractor_; }
  /** @getter{propagated environment containing the variable's values, BoundPreprocessor} */
  [[nodiscard]] const Environment& env() const { return env_; }
  /** @getter{statistics, BoundPreprocessor} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }

  /**
   * Check whether the formula is a simple relational bound.
   *
   * A simple relational bound is a formula in the form:
   * @f[
   * a \leq b \\
   * a < b \\
   * a \geq b \\
   * a > b \\
   * a = b \\
   * a \neq b \\
   * @f]
   * Where @f$ a @f$ is a variable and @f$ b @f$ is a constant or vice versa.
   * @param formula symbolic formula to check
   * @return true if the formula is a simple relational bound
   * @return false if the formula is not a simple relational bound
   */
  static bool IsSimpleBound(const Formula& formula);
  /**
   * Check whether the formula is a simple relational bound with an equality operator (@f$ a = b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsEqualTo(const Formula& formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a non-equality operator (@f$ a \neq b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsNotEqualTo(const Formula& formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a greater than operator (@f$ a > b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsGreaterThan(const Formula& formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than operator (@f$ a < b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsLessThan(const Formula& formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than or equal to operator (@f$ a \ge b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsGreaterThanOrEqualTo(const Formula& formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than or equal to operator (@f$ a \le b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsLessThanOrEqualTo(const Formula& formula, bool truth = true);

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
   * @param explanations the explanations to be updated if a conflict is found
   * @return true if the propagation was successful
   * @return false if a conflict was detected
   */
  bool PropagateEqPolynomial(const Literal& lit, const Variable& var_to_propagate, Explanations& explanations);
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
   * @param explanations the explanations to be updated if a conflict is found
   * @return true if the propagation was successful
   * @return false if a conflict was detected
   */
  bool PropagateBoundsPolynomial(const Literal& lit, const Variable& var_to_propagate, Explanations& explanations);

  bool PropagateBoundsPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                 const std::vector<Bound>& assumptions, Explanations& explanations);

 protected:
  const Variable* ShouldPropagateEqPolynomial(const Literal& lit) const;
  const Variable* ShouldPropagateEqPolynomial(const Formula& formula) const;
  const Variable* ShouldPropagateBoundsPolynomial(const Literal& lit) const;
  const Variable* ShouldPropagateBoundsPolynomial(const Formula& formula) const;
  bool ShouldEvaluate(const Literal& lit) const;
  bool ShouldEvaluate(const Formula& formula) const;

  Bound GetSimpleBound(const dlinear::Literal& lit) const;
  Bound GetSimpleBound(const Literal& lit, const Formula& formula) const;

  void PropagateConstraints(std::list<Literal>& enabled_literals, Explanations& explanations);
  void PropagateEqConstraints(std::list<Literal>& enabled_literals, Explanations& explanations);
  void PropagateBoundConstraints(std::list<Literal>& enabled_literals, Explanations& explanations);
  void EvaluateFormulas(std::list<Literal>& enabled_literals, Explanations& explanations);
  void FormulaViolationExplanation(const Literal& lit, const Formula& formula, Explanations& explanations);

  std::pair<Variable, Variable> ExtractBoundEdge(const Formula& formula) const;
  /**
   * Given a formula of the form @f$ ax = by @f$, with @f$ a, b \in \mathbb{R} @f$ being constants,
   * extract the coefficient @f$ c \coloneqq cx = y @f$.
   *
   * Variables enjoy total ordering between them.
   * The leftmost variable is always the smallest.
   * @param formula the formula to extract the coefficient from
   * @return the coefficient @f$ c @f$
   */
  mpq_class ExtractEqBoundCoefficient(const Formula& formula) const;

  void GetExplanation(const Variable& var, LiteralSet& explanation);

  /** Vector used to store the mpq_class elements obtained from more complex constraints */
  const mpq_class* StoreTemporaryMpq(const mpq_class& value);

#if DEBUGGING_PREPROCESSOR
  std::vector<Variable> GetExplanationOrigins(const Variable& var);
#endif

 private:
  std::list<mpq_class>
      temporary_mpq_vector_;  ///< Vector used to store temporary mpq values obtained from more complex constraints

  const Config& config_;  ///< Configuration of the preprocessor
  const PredicateAbstractor&
      predicate_abstractor_;  ///< Predicate abstractor used to get the constraints from the literals

  LiteralSet enabled_literals_;

  BoundVectorMap theory_bounds_;  ///< Theory bounds for each theory variable
  Environment env_;               ///< Environment storing the values of all the variables with a fixed value

  IterationStats stats_;  ///< Statistics of the preprocessing.
};

std::ostream& operator<<(std::ostream& os, const BoundPreprocessor& preprocessor);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::BoundPreprocessor)

#endif
