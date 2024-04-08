#include "BoxedCell.h"

#include "dlinear/symbolic/ExpressionCell.h"

namespace dlinear::symbolic::internal {

BoxedCell::BoxedCell(const numeric_type& constant)
    : kind_{ExpressionKind::Constant}, value_(std::make_shared<const numeric_type>(std::move(constant))) {}
BoxedCell::BoxedCell(const std::shared_ptr<const numeric_type>& expr) : kind_{ExpressionKind::Constant}, value_{expr} {}
BoxedCell::BoxedCell(const std::shared_ptr<const ExpressionCell>& expr) : kind_{expr->kind()}, value_{expr} {}

BoxedCell& BoxedCell::operator=(const mpq_class& new_value) {
  DLINEAR_ASSERT(is_constant(), "Box must contain a constant value");
  value_ = std::make_shared<const numeric_type>(new_value);
  return *this;
}
BoxedCell& BoxedCell::operator=(const std::shared_ptr<const ExpressionCell>& new_expr) {
  DLINEAR_ASSERT(!is_constant(), "Box must not contain a constant value");
  kind_ = new_expr->kind();
  std::get<std::shared_ptr<const ExpressionCell>>(value_) = new_expr;
  return *this;
}
BoxedCell& BoxedCell::operator=(const std::shared_ptr<const mpq_class>& new_value) {
  DLINEAR_ASSERT(is_constant(), "Box must contain a constant value");
  value_ = new_value;
  return *this;
}
void BoxedCell::hash(InvocableHashAlgorithm auto& hasher) const noexcept {
  if (is_constant()) {
    hash_append(hasher, constant());
  } else {
    cell().hash(hasher);
  }
}

}  // namespace dlinear::symbolic::internal
