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
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

class TheoryPreprocessor {
 public:
  explicit TheoryPreprocessor(const Config& config, const std::string& class_name = "TheoryPreprocessor");
  virtual ~TheoryPreprocessor() = default;

  virtual void AddVariable(const Variable& var) = 0;
  virtual bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) = 0;
  virtual bool Process(const ConflictCallback& conflict_cb) = 0;

 protected:
  const Config& config_;
  const IterationStats stats_;
};

}  // namespace dlinear
