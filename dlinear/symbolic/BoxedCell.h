#pragma once

#include <cstdint>
#include <cstring>
#include <memory>
#include <utility>
#include <variant>

#include "dlinear/libs/gmp.h"
#include "dlinear/symbolic/ExpressionKind.h"

namespace dlinear::symbolic {

class ExpressionCell;

namespace internal {

/**
 * BoxedCell is an internal class that provides storage format for the data inside an Expression.
 *
 * Conceptually, it stores three pieces of information:
 *
 * (1) `ExpressionKind kind` -- the operation (e.g., add, mul, cos, max, ...).
 *
 * (2) `shared_ptr<mpq_class> value` -- the constant value iff `kind == ExpressionKind::Constant`.
 *
 * (3) `shared_ptr<ExpressionCell> cell` -- a copy-on-write, heap-allocated object
 * that stores the details of the expression operation (e.g., the terms to sum).
 * This is only used for expressions with `kind != ExpressionKind::Constant`; for
 * constants, the cell is conceptually nullptr.
 *
 * Instead of using two different pointers, the `value` and `cell` are stored in a variant.
 */
class BoxedCell {
 public:
  using numeric_type = mpq_class;

  /* Default constructor constructs zero. */
  BoxedCell() : BoxedCell(0.0) {}
  /* Constructs a constant. */
  explicit BoxedCell(const numeric_type& constant);
  explicit BoxedCell(const std::shared_ptr<const numeric_type>& constant);
  explicit BoxedCell(const std::shared_ptr<const ExpressionCell>& cell);

  /** @getter{kind, box} */
  [[nodiscard]] ExpressionKind kind() const { return kind_; }
  /** @checker{constant, box} */
  [[nodiscard]] bool is_constant() const { return kind_ == ExpressionKind::Constant; }

  /**
   * Check whether the kind of this BoxedCell is the same as the given kind.
   * @tparam kind The expression type to check against
   * @return true if the kind of this BoxedCell is the same as the given kind
   * @return false if the kind of this BoxedCell is not the same as the given kind
   */
  template <ExpressionKind kind>
  [[nodiscard]] bool is_kind() const {
    return kind_ == kind;
  }

  /**
   * Get the value of the constant.
   * @pre This expression is a constant.
   * @return the value of the constant.
   * @throw std::bad_variant_access if this expression is not a constant
   */
  [[nodiscard]] const numeric_type& constant() const { return *std::get<std::shared_ptr<const numeric_type>>(value_); }
  /**
   * Get the expression cell.
   * @pre This expression is not a constant expression.
   * @return the expression cell.
   * @throw std::bad_variant_access if this expression is not a non constant expression
   */
  [[nodiscard]] const ExpressionCell& cell() const { return *std::get<std::shared_ptr<const ExpressionCell>>(value_); }

  /** @getter{reference count, value in the box}  */
  [[nodiscard]] long use_count() const {
    return kind_ == ExpressionKind::Constant ? std::get<std::shared_ptr<const numeric_type>>(value_).use_count()
                                             : std::get<std::shared_ptr<const ExpressionCell>>(value_).use_count();
  }

  /** @hash{box} */
  void hash(InvocableHashAlgorithm auto& hasher) const noexcept;

  /**
   * Sets this to a new Constant value.
   * @pre This expression is already a Constant.
   * @param new_value the new value to set
   */
  BoxedCell& operator=(const numeric_type& new_value);
  /**
   * Sets this to a new Constant value.
   * @pre This expression is already a Constant.
   * @param new_value the new value to set
   */
  BoxedCell& operator=(const std::shared_ptr<const numeric_type>& new_value);
  /**
   * Sets this to point at the given cell_to_share, incrementing its use_count.
   * @pre This is a Constant (i.e., does currently not own any cell).
   * @pre cell_to_share is not null.
   */
  BoxedCell& operator=(const std::shared_ptr<const ExpressionCell>& new_cell);

 private:
  ExpressionKind kind_{};  ///< The kind of the expression.
  std::variant<std::shared_ptr<const numeric_type>, std::shared_ptr<const ExpressionCell>>
      value_;  ///< The value of the expression. It is a pointer to either a constant or an expression cell.
};

}  // namespace internal
}  // namespace dlinear::symbolic
