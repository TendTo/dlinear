//
// Created by c3054737 on 19/01/24.
//
#pragma once

#include "dlinear/solver/QsoptexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class DeltaQsoptexTheorySolver : public QsoptexTheorySolver {
 public:
  explicit DeltaQsoptexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  void EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Literal& lit) override;
};

}  // namespace dlinear
