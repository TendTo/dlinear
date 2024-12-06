/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyright cvc5 (Tim King, Gereon Kremer, Morgan Deters)
 * @licence BSD 3-Clause License
 */
#include "Tableau.h"

#include "dlinear/util/error.h"

namespace dlinear {

Tableau::Tableau(const std::initializer_list<std::initializer_list<mpq_class>> values)
    : matrix_(static_cast<int>(values.size()), values.size() > 0 ? static_cast<int>(values.begin()->size()) : 0) {
  const int rows = static_cast<int>(values.size());
  const int cols = values.size() > 0 ? static_cast<int>(values.begin()->size()) : 0;

  for (int row = 0; row < rows; ++row) {
    for (int col = 0; col < cols; ++col) {
      matrix_.coeffRef(row, col) = *((values.begin() + row)->begin() + col);
    }
  }
}

void Tableau::AddRow(const Variable& basicVar, const std::vector<mpq_class>& coeffs,
                     const std::vector<Variable>& variables) {
  DLINEAR_TRACE_FMT("Tableau::AddRow({}, {}, {})", basicVar, coeffs, variables);
}

void Tableau::Pivot(const Variable& old_basic, const Variable& new_basic, const MultiplyRowCallback& cb) {
  DLINEAR_ASSERT(IsBasic(old_basic), "");
  DLINEAR_ASSERT(!IsBasic(new_basic), "");

  DLINEAR_TRACE_FMT("Tableau::Pivot({}, {})", old_basic, new_basic);

  const RowIndex ridx = GetRowIndex(old_basic);

  RowPivot(old_basic, new_basic, cb);
  DLINEAR_ASSERT(ridx == GetRowIndex(new_basic), "new basic variable must have the same row index as the old basic");

  const Row& row = matrix_.innerVector(ridx);
  for (int k = 0; k < matrix_.outerSize(); ++k) {
    if (k == ridx) continue;
    const mpq_class& coeff = matrix_.coeffRef(k, static_cast<int>(new_basic.get_id() - 1));
    matrix_.innerVector(k) = (matrix_.innerVector(k) - row * coeff).pruned();
  }

  DLINEAR_ASSERT(!IsBasic(old_basic), "old basic variable must not be basic anymoer");
  DLINEAR_ASSERT(IsBasic(new_basic), "new basic variable must be basic now");
}
void Tableau::RemoveBasicRow(const Variable& basic) { DLINEAR_TRACE_FMT("Tableau::RemoveBasicRow({})", basic); }
void Tableau::SubstitutePlusTimesConstant(const Variable& to, const Variable& from, const mpq_class& mult,
                                          const CoefficientChangeCallback&) {
  DLINEAR_TRACE_FMT("Tableau::SubstitutePlusTimesConstant({}, {}, {}", to, from, mult);
}
void Tableau::ManipulateRowEntry(const RowIndex row, const ColIndex col, const mpq_class& c,
                                 const CoefficientChangeCallback& cb) {
  mpq_class& coeff = matrix_.coeffRef(row, col);
  const int old_sign = mpq_sgn(coeff.get_mpq_t());
  coeff += c;
  const int new_sign = mpq_sgn(coeff.get_mpq_t());

  if (old_sign != new_sign) {
    cb(row, col, old_sign, new_sign);
  }
}
std::size_t Tableau::RowComplexity(const Variable& basic) const { return RowComplexity(GetRowIndex(basic)); }
std::size_t Tableau::RowComplexity(RowIndex ridx) const {
  std::size_t complexity = 0;
  for (RowIterator it{matrix_, ridx}; it; ++it) {
    complexity += gmp::complexity(it.valueRef());
  }
  return complexity;
}
double Tableau::AvgRowComplexity() const {
  double sum = 0;
  int rows;
  for (rows = 0; rows < matrix_.outerSize(); ++rows) {
    sum += static_cast<double>(RowComplexity(rows));
  }
  return (rows == 0) ? 0 : (sum / static_cast<double>(rows));
}

void Tableau::RowPivot(const Variable& old_basic, const Variable& new_basic, const MultiplyRowCallback& cb) {
  DLINEAR_ASSERT(IsBasic(old_basic), "old basic variable must be basic");
  DLINEAR_ASSERT(!IsBasic(new_basic), "new basic variable must not be basic");
  DLINEAR_TRACE_FMT("Tableau::RowPivot({}, {})", old_basic, new_basic);

  const RowIndex idx = GetRowIndex(old_basic);

  const mpq_class& a_rs = matrix_.coeffRef(idx, static_cast<int>(new_basic.get_id() - 1));
  const int a_rs_sgn = mpq_sgn(a_rs.get_mpq_t());
  // TODO(tend): why should this be negated???
  const mpq_class negInverseA_rs{a_rs.get_den(), a_rs.get_num()};

  for (RowIterator it{matrix_, idx}; it; ++it) {
    it.valueRef() *= negInverseA_rs;
  }

  // Change the basic variable on the row
  basic_to_row_.erase(old_basic);
  basic_to_row_.emplace(new_basic, idx);
  row_to_basic_.insert_or_assign(idx, new_basic);

  cb(idx, -a_rs_sgn);
}

void Tableau::SetBasicVar(const Variable& basic, RowIndex ridx) {
  DLINEAR_ASSERT(std::ranges::none_of(
                     basic_to_row_, [&ridx](const std::pair<Variable, RowIndex>& pair) { return pair.second == ridx; }),
                 "");
  DLINEAR_ASSERT(ridx < matrix_.rows(), "");
  basic_to_row_.emplace(basic, ridx);
  row_to_basic_.insert_or_assign(ridx, basic);
}

std::ostream& operator<<(std::ostream& os, const Tableau& t) { return os << t.matrix(); }

}  // namespace dlinear