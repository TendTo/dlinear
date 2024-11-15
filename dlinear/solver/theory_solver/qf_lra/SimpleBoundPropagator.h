#pragma once

#include <unordered_map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheoryPropagator.h"
#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/solver/theory_solver/qf_lra/LpRowSense.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/SortedVector.hpp"

namespace dlinear {

class SimpleBoundPropagator : public TheoryPropagator {
 public:
  explicit SimpleBoundPropagator(const TheorySolver& theory_solver,
                                 const std::string& class_name = "SimpleBoundPropagator");

  void Propagate(const AssertCallback& assert_cb) override;

 private:
  /** Bound constraint. It is a tuple of value, row_sense and boolean variable */
  struct BoundConstraint {
    mpq_class value;       ///< Value of the constraint
    LpRowSense row_sense;  ///< Type of the constraint (e.g. <=, <, =, >, >=)
    Variable variable;     ///< Boolean variable encoding the constraint

    std::strong_ordering operator<=>(const BoundConstraint& o) const;
    bool operator==(const BoundConstraint& o) const;
  };

  /**
   * Propagate the sorted constraints by adding them to the context by calling the @p assert_cb function.
   * @param assert_cb assertion function. It adds the propagated assertions to the context
   */
  void PropagateAssertions(const AssertCallback& assert_cb);

  /**
   * Add an assertion to the @ref constraints_ map.
   *
   * Based on the number of free variables in the assertion, it will call the appropriate AddAssertion method.
   * @tparam NVariables number of free variables in the assertion
   * @param assertion assertion to add
   */
  template <int NVariables>
  void AddAssertion(const Formula& assertion);
  std::unordered_map<Variable, SortedVector<BoundConstraint>> constraints_;  ///< Map of constraints for each variable
};

}  // namespace dlinear
