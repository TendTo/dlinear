/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "Driver.h"

#include <iostream>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear::mps {

MpsDriver::MpsDriver(Context &context) : Driver{context, "MpsDriver"} {}

bool MpsDriver::ParseStreamCore(std::istream &in) {
  MpsScanner scanner(&in);
  scanner.set_debug(debug_scanning_);
  scanner_ = &scanner;

  MpsParser parser(*this);
  parser.set_debug_level(debug_parsing_);
  const bool res = parser.parse() == 0;
  scanner_ = nullptr;
  return res;
}

bool MpsDriver::VerifyStrictBound(const std::string &bound) {
  if (strict_mps_) {
    if (bound_name_.empty()) {
      bound_name_ = bound;
    } else if (bound_name_ != bound) {
      DLINEAR_WARN_FMT("First bound was '{}', found new bound '{}'. Skipping", bound_name_, bound);
      return false;
    }
  }
  return true;
}

bool MpsDriver::VerifyStrictRhs(const std::string &rhs) {
  if (strict_mps_) {
    if (rhs_name_.empty()) {
      rhs_name_ = rhs;
    } else if (rhs_name_ != rhs) {
      DLINEAR_WARN_FMT("First RHS was '{}', found new RHS '{}'. Skipping", rhs_name_, rhs);
      return false;
    }
  }
  return true;
}

void MpsDriver::error(const location &l, const std::string &m) { std::cerr << l << " : " << m << std::endl; }

void MpsDriver::ObjectiveSense(bool is_min) {
  DLINEAR_TRACE_FMT("Driver::ObjectiveSense {}", is_min);
  is_min_ = is_min;
}

void MpsDriver::ObjectiveName(const std::string &row) {
  DLINEAR_TRACE_FMT("Driver::ObjectiveName {}", row);
  obj_row_ = row;
}

void MpsDriver::AddRow(Sense sense, const std::string &row) {
  DLINEAR_TRACE_FMT("Driver::AddRow {} {}", sense, row);
  if (sense == Sense::N && obj_row_.empty()) {
    DLINEAR_DEBUG("Objective row not found. Adding the first row with sense N as objective row");
    obj_row_ = row;
  }
  row_senses_[row] = sense;
}

void MpsDriver::AddColumn(const std::string &column, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddColumn {} {} {}", row, column, value);
  if (columns_.find(column) == columns_.end()) {
    DLINEAR_TRACE_FMT("Added column {}", column);
    // TODO(tend): choose if the name of the variable should be the column name or index
    const Variable var{"x" + std::to_string(columns_.size())};
    columns_[column] = var;  // If not already in the map, add the variable
    context_.DeclareVariable(var);
  }
  if (!context_.config().optimize() && row == obj_row_) return;
  rows_[row].emplace(columns_[column], value);
  DLINEAR_TRACE_FMT("Updated row {}", row);
}

void MpsDriver::AddRhs(const std::string &rhs, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddRhs {} {} {}", rhs, row, value);
  if (!VerifyStrictRhs(rhs)) return;
  rhs_values_[row] = value;
  Expression row_expression = ExpressionAddFactory{0, rows_[row]}.GetExpression();
  try {
    switch (row_senses_.at(row)) {
      case Sense::L:
        rhs_[row] = row_expression <= value;
        break;
      case Sense::G:
        rhs_[row] = value <= row_expression;
        break;
      case Sense::E:
        rhs_[row] = row_expression == value;
        break;
      case Sense::N:
        DLINEAR_WARN("Sense N is used only for objective function. No action to take");
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &e) {
    DLINEAR_RUNTIME_ERROR_FMT("Row {} not found", row);
  }
  DLINEAR_TRACE_FMT("Updated rhs {}", rhs_[row]);
}

void MpsDriver::AddRange(const std::string &rhs, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddRange {} {} {}", rhs, row, value);
  if (!VerifyStrictRhs(rhs)) return;
  try {
    Expression row_expression = ExpressionAddFactory{0, rows_[row]}.GetExpression();
    switch (row_senses_.at(row)) {
      case Sense::L:
        mpq_abs(value.get_mpq_t(), value.get_mpq_t());
        rhs_[row] &= mpq_class{rhs_values_[row] - value} <= row_expression;
        break;
      case Sense::G:
        mpq_abs(value.get_mpq_t(), value.get_mpq_t());
        rhs_[row] &= row_expression <= mpq_class{rhs_values_[row] + value};
        break;
      case Sense::E:
        rhs_[row] = value > 0
                        ? rhs_values_[row] <= row_expression && row_expression <= mpq_class(rhs_values_[row] + value)
                        : mpq_class{rhs_values_[row] + value} <= row_expression && row_expression <= rhs_values_[row];
        break;
      case Sense::N:
        DLINEAR_WARN("Sense N is used only for objective function. No action to take");
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &e) {
    DLINEAR_RUNTIME_ERROR_FMT("Row {} not found", row);
  }
}

void MpsDriver::AddBound(BoundType bound_type, const std::string &bound, const std::string &column, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {} {}", bound_type, bound, column, value);
  if (!VerifyStrictBound(bound)) return;
  try {
    switch (bound_type) {
      case BoundType::UP:
      case BoundType::UI:
        bounds_[column] &= columns_.at(column) <= value;
        if (value <= 0) skip_lower_bound_[column] = true;
        break;
      case BoundType::LO:
      case BoundType::LI:
        bounds_[column] &= value <= columns_.at(column);
        skip_lower_bound_[column] = true;
        break;
      case BoundType::FX:
        bounds_[column] &= (value <= columns_.at(column)) && (columns_.at(column) <= value);
        skip_lower_bound_[column] = true;
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &e) {
    DLINEAR_RUNTIME_ERROR_FMT("Column {} not found", column);
  }

  DLINEAR_TRACE_FMT("Updated bound {}", bounds_[column]);
}

void MpsDriver::AddBound(BoundType bound_type, const std::string &bound, const std::string &column) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {}", bound_type, bound, column);
  if (!VerifyStrictBound(bound)) return;
  try {
    switch (bound_type) {
      case BoundType::BV:
        bounds_[column] = (0 <= columns_.at(column)) && (columns_.at(column) <= 1);
        skip_lower_bound_[column] = true;
        break;
      case BoundType::FR:
      case BoundType::MI:
        skip_lower_bound_[column] = true;
        break;
      case BoundType::PL:
        DLINEAR_DEBUG("Infinity bound, no action to take");
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &e) {
    DLINEAR_RUNTIME_ERROR_FMT("Column {} not found", column);
  }

  DLINEAR_TRACE_FMT("Updated bound {}", bounds_[column]);
}

void MpsDriver::End() {
  DLINEAR_DEBUG_FMT("Driver::EndData reached end of file {}", problem_name_);
  for (const auto &[row, sense] : row_senses_) {
    if (sense != Sense::N && rhs_.find(row) == rhs_.end()) {
      DLINEAR_TRACE_FMT("Row {} has no RHS. Adding 0", row);
      AddRhs(rhs_name_, row, 0);
    }
  }
  for (const auto &[column, var] : columns_) {
    if (skip_lower_bound_.find(column) == skip_lower_bound_.end()) {
      DLINEAR_TRACE_FMT("Column has no lower bound. Adding 0 <= {}", column);
      AddBound(BoundType::LO, bound_name_, column, 0);
    }
  }
  DLINEAR_DEBUG_FMT("Found {} assertions", n_assertions());
  for (const auto &[name, bound] : bounds_) {
    context_.Assert(bound);
  }
  for (const auto &[name, row] : rhs_) {
    if (row.EqualTo(Formula::True())) continue;
    context_.Assert(row);
  }
  if (context_.config().optimize() && !obj_row_.empty()) {
    Expression obj_expression = ExpressionAddFactory{0, rows_.at(obj_row_)}.GetExpression();
    if (is_min_) {
      context_.Minimize(obj_expression);
    } else {
      context_.Maximize(obj_expression);
    }
  }
}

void MpsDriver::ToSmt2(std::ostream &os) const {
  os << "(set-logic QF_LRA)\n";
  if (!context_.GetInfo(":status").empty()) os << "(set-info :status " << context_.GetInfo(":status") << ")\n";
  for (const auto &[name, column] : columns_) {
    os << "(declare-const " << column << " Real)\n";
  }
  for (const auto &[name, bound] : bounds_) {
    os << "(assert " << bound.to_smt2_string() << ")\n";
  }
  for (const auto &[name, row] : rhs_) {
    if (row.EqualTo(Formula::True())) continue;
    os << "(assert " << row.to_smt2_string() << ")\n";
  }
  os << "(check-sat)\n";
}

}  // namespace dlinear::mps
