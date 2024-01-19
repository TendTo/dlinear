//
// Created by c3054737 on 17/01/24.
//
#pragma once

#include <optional>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class DeltaSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit DeltaSoplexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  std::optional<LiteralSet> EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision, LiteralSet& explanation) override;
};

}  // namespace dlinear
