/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheoryPreprocessor class.
 */
#pragma once

#include <functional>
#include <string>

#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

// Forward declaration
class TheorySolver;

class TheoryPreprocessor {
 public:
  explicit TheoryPreprocessor(const TheorySolver& theory_solver, const std::string& class_name = "TheoryPreprocessor");
  virtual ~TheoryPreprocessor() = default;

  /** @getter{theory solver, TheoryPreprocessor} */
  [[nodiscard]] const TheorySolver& theory_solver() const { return theory_solver_; }
  /** @getter{statistics, TheoryPreprocessor} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }

  virtual void AddVariable(const Variable& var) = 0;
  virtual bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) = 0;
  virtual bool Process(const ConflictCallback& conflict_cb) = 0;
  virtual bool ProcessFixed(const ConflictCallback& conflict_cb) = 0;
  virtual bool Backtrack() = 0;

 protected:
  const TheorySolver& theory_solver_;
  const IterationStats stats_;
};

}  // namespace dlinear
