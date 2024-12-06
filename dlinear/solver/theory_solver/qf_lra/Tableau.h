/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyright cvc5 (Tim King, Gereon Kremer, Morgan Deters)
 * @licence BSD 3-Clause License
 * Tableau class.
 */
#pragma once

#include <functional>
#include <iosfwd>

#include "dlinear/libs/libeigen.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/literal.h"

namespace dlinear {

/**
 * A Tableau is a mpq_class matrix that keeps its rows in solved form.
 * Each row has a basic variable with coefficient -1 that is solved.
 * Tableau is optimized for pivoting.
 * The tableau should only be updated via pivot calls.
 * Inspired by the [Tableau class](https://github.com/cvc5/cvc5/blob/main/src/theory/arith/linear/tableau.h) in cvc5.
 */
class Tableau {
 public:
  using RowIndex = int;
  using ColIndex = int;
  using CoefficientChangeCallback = std::function<void(RowIndex, ColIndex, int, int)>;
  using MultiplyRowCallback = std::function<void(RowIndex, int)>;
  using Matrix = Eigen::SparseMatrix<mpq_class, Eigen::RowMajor>;
  using RowIterator = Matrix::InnerIterator;
  using Row = Matrix::InnerVectorReturnType;

 private:
  Matrix matrix_;

  std::map<Variable, RowIndex> basic_to_row_;
  std::map<RowIndex, Variable> row_to_basic_;

 public:
  Tableau() = default;
  Tableau(std::initializer_list<std::initializer_list<mpq_class>> values);

  [[nodiscard]] const Matrix& matrix() const { return matrix_; }

  [[nodiscard]] bool IsBasic(const Variable v) const { return basic_to_row_.contains(v); }

  [[nodiscard]] const std::map<Variable, RowIndex>& basic_to_row() const { return basic_to_row_; }
  [[nodiscard]] const std::map<RowIndex, Variable>& row_to_basic() const { return row_to_basic_; }

  [[nodiscard]] RowIndex GetRowIndex(const Variable x) const { return basic_to_row_.at(x); }

  [[nodiscard]] const Variable& GetBasicVariable(const RowIndex idx) const { return row_to_basic_.at(idx); }

  void SetBasicVar(const Variable& var, RowIndex ridx);

  /**
   * Adds a row to the tableau.
   * The new row is equivalent to:
   *   basicVar = \f$\sum_i\f$ coeffs[i] * variables[i]
   * preconditions:
   *   basicVar is already declared to be basic
   *   basicVar does not have a row associated with it in the tableau.
   *
   * Note: each variables[i] does not have to be non-basic.
   * Pivoting will be mimicked if it is basic.
   */
  void AddRow(const Variable& basicVar, const std::vector<mpq_class>& coeffs, const std::vector<Variable>& variables);

  /**
   * @pre @f$ x_r @f$ is basic
   * @pre @f$ x_s @f$ is non-basic
   * @pre @f$ a_{rs} \ne 0 @f$
   */
  void Pivot(const Variable& old_basic, const Variable& new_basic, const MultiplyRowCallback& cb);

  void RemoveBasicRow(const Variable& basic);

  [[nodiscard]] std::size_t BasicRowLength(const Variable basic) const {
    return matrix_.row(GetRowIndex(basic)).size();
  }

  /**
   *  to += mult * from
   * replacing from with its row.
   */
  void SubstitutePlusTimesConstant(const Variable& to, const Variable& from, const mpq_class& mult,
                                   const CoefficientChangeCallback& cb);

  void DirectlyAddToCoefficient(const Variable& rowVar, const ColIndex col, const mpq_class& mult,
                                const CoefficientChangeCallback& cb) {
    const RowIndex idx = GetRowIndex(rowVar);
    ManipulateRowEntry(idx, col, mult, cb);
  }

  void ManipulateRowEntry(RowIndex row, ColIndex col, const mpq_class& c, const CoefficientChangeCallback& cb);

  /* Returns the complexity of a row in the tableau. */
  [[nodiscard]] std::size_t RowComplexity(const Variable& basic) const;
  [[nodiscard]] std::size_t RowComplexity(RowIndex ridx) const;

  /* Returns the average complexity of the rows in the tableau. */
  [[nodiscard]] double AvgRowComplexity() const;

 private:
  /* Changes the basic variable on the row for basicOld to basicNew. */
  void RowPivot(const Variable& old_basic, const Variable& new_basic, const MultiplyRowCallback& cb);
};

std::ostream& operator<<(std::ostream& os, const Tableau& t);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Tableau)

#endif
