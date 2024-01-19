//
// Created by c3054737 on 19/01/24.
//
#pragma once

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/QsoptexTheorySolver.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class DeltaQsoptexTheorySolver : public QsoptexTheorySolver {
 public:
  explicit DeltaQsoptexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  void EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision) override;
};

}  // namespace dlinear
