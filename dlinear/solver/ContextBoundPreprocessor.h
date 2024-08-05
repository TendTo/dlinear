/**
 * @file ContextBoundPreprocessor.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief ContextBoundPreprocessor class.
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
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/ContextBoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/logging.h"

namespace dlinear {

/**
 * This class uses some basic algebraic operations to preprocess the constraints
 * and identify violations before invoking the solver.
 */
class ContextBoundPreprocessor {
 public:
  using Explanations = std::set<LiteralSet>;
  using VarToEqBinomialMap = std::unordered_map<Variable, mpq_class>;

  explicit ContextBoundPreprocessor(const PredicateAbstractor& predicate_abstractor);

  ContextBoundVector::BoundIterator AddConstraint(const Literal& lit);

  Explanations Process(const LiteralSet& enabled_literals = {});
  void Process(const LiteralSet& enabled_literals, Explanations& explanations);

  void GetActiveExplanation(const Variable& var, LiteralSet& explanation);

  void Clear();
  void Reset();

  /** @getter{configuration, ContextBoundPreprocessor} */
  [[nodiscard]] const Config& config() const { return config_; }
  /** @getter{bounds of the variables in the LP solver, ContextBoundPreprocessor} */
  [[nodiscard]] const ContextBoundVectorMap& theory_bounds() const { return theory_bounds_; }
  /** @getter{predicate abstractor, ContextBoundPreprocessor} */
  [[nodiscard]] const PredicateAbstractor& predicate_abstractor() const { return predicate_abstractor_; }
  /** @getter{propagated environment containing the variable's values, ContextBoundPreprocessor} */
  [[nodiscard]] const Environment& env() const { return env_; }

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

 protected:
  enum class PropagateResult { NO_PROPAGATION, UNCHANGED, PROPAGATED, CONFLICT };

  bool ShouldPropagateEqPolynomial(const Literal& lit) const;
  bool ShouldPropagateEqPolynomial(const Formula& formula) const;
  bool ShouldPropagateBoundsPolynomial(const Literal& lit) const;
  bool ShouldPropagateBoundsPolynomial(const Formula& formula) const;
  bool ShouldEvaluate(const Literal& lit) const;
  bool ShouldEvaluate(const Formula& formula) const;

  ContextBoundVector& GetBoundVector(const Variable& var);
  ContextBoundVector::Bound GetBound(const Literal& var) const;
  ContextBoundVector::Bound GetBound(const Literal& lit, const Formula& formula) const;

  void SetEnvironmentFromBounds();
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
   * @param explanations the explanations to be updated if a conflict is found
   * @return CONFLICT if a conflict has been found
   * @return PROPAGATED if the propagation took place
   */
  PropagateResult PropagateEqPolynomial(const Literal& lit, Explanations& explanations);
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
   * @param explanations the explanations to be updated if a conflict is found
   * @return CONFLICT if a conflict has been found
   * @return PROPAGATED if the propagation took place
   */
  PropagateResult PropagateBoundsPolynomial(const Literal& lit, Explanations& explanations);
  void PropagateConstraints(std::list<Literal>& enabled_literals, Explanations& explanations);
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

  const mpq_class* StoreTemporaryMpq(const mpq_class& value);

#if DEBUGGING_PREPROCESSOR
  std::vector<Variable> GetExplanationOrigins(const Variable& var);
#endif

 private:
  std::list<mpq_class>
      temporary_mpq_vector_;  ///< Vector used to store temporary mpq values obtained from more complex constraints

  const Config& config_;  ///< Configuration of the preprocessor
  const PredicateAbstractor& predicate_abstractor_;

  ContextBoundVectorMap theory_bounds_;
  Environment env_;

  LiteralSet fixed_literals_;
  ContextBoundVectorMap fixed_theory_bounds_;
  Environment fixed_env_;
  std::list<mpq_class> fixed_temporary_mpq_vector_;
};

std::ostream& operator<<(std::ostream& os, const ContextBoundPreprocessor& preprocessor);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::ContextBoundPreprocessor)
