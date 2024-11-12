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
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

class TheoryPropagator {
 public:
  explicit TheoryPropagator(const Config& config, const std::string& class_name = "TheoryPropagator");
  virtual ~TheoryPropagator() = default;

  /** @getter{configuration, TheoryPropagator} */
  [[nodiscard]] const Config& config() const { return config_; }
  /** @getter{statistics, TheoryPropagator} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }

  //  virtual void Propagate(std::span<const Literal> literals) = 0;
  //  virtual void Propagate(const LiteralSet& literals) = 0;
  virtual void Propagate(const AssertCallback& assert_cb) = 0;

 protected:
  const Config& config_;
  const IterationStats stats_;
};

}  // namespace dlinear
