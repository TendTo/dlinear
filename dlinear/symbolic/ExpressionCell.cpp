#include "ExpressionCell.h"

#include "dlinear/util/hash.hpp"

namespace dlinear::symbolic {

ExpressionCell::ExpressionCell(const ExpressionKind k, const size_t hash, const bool is_poly, const bool include_ite,
                               Variables variables)
    : kind_{k},
      hash_{hash_combine(static_cast<size_t>(kind_), hash)},
      is_polynomial_{is_poly},
      include_ite_{include_ite},
      variables_{std::move(variables)} {}

Expression ExpressionCell::GetExpression() { return Expression{this}; }

}  // namespace dlinear::symbolic