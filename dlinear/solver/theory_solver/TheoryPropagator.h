/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheoryPropagator class.
 */
#pragma once

#include <functional>
#include <string>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

// Forward declarations
class TheorySolver;

class TheoryPropagator {
 public:
  explicit TheoryPropagator(const TheorySolver& theory_solver, const std::string& class_name = "TheoryPropagator");
  virtual ~TheoryPropagator() = default;

  /** @getter{theory solver, TheoryPropagator} */
  [[nodiscard]] const TheorySolver& theory_solver() const { return theory_solver_; }
  /** @getter{statistics, TheoryPropagator} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }

  //  virtual void Propagate(std::span<const Literal> literals) = 0;
  //  virtual void Propagate(const LiteralSet& literals) = 0;
  virtual void Propagate(const AssertCallback& assert_cb) = 0;

 protected:
  const TheorySolver& theory_solver_;
  const IterationStats stats_;
};

}  // namespace dlinear
