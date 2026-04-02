/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "Driver.h"

#include <iostream>

#include "dlinear/util/error.h"
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

void MpsDriver::AddRow(const Sense sense, const std::string &row) {
  DLINEAR_TRACE_FMT("Driver::AddRow {} {}", sense, row);
  if (sense == Sense::N) {
    if (!obj_row_.empty()) {
      DLINEAR_WARN_FMT("Objective row name already set to '{}', ignoring new objective row '{}'", obj_row_, row);
      return;
    }
    DLINEAR_DEBUG("Objective row name not found. Adding the first row with sense N as objective row");
    obj_row_ = row;
    return;
  }
  rows_.emplace(row, Row{sense});
}

void MpsDriver::AddColumn(const std::string &column, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddColumn {} {} {}", row, column, value);
  auto it = columns_.find(column);
  if (columns_.end() == it) {
    DLINEAR_TRACE_FMT("Added column {}", column);
    // Integer columns are added with an implicit lower bound of 0 and upper bound of 1.
    // Non integer columns are added with an implicit lower bound of 0 and no upper bound.
    Variable var{column};
    context_.DeclareVariable(var);
    auto [insert_it, val] = columns_.emplace(column, Column{var, integer_columns_});
    it = insert_it;
  }
  if (row == obj_row_) {
    obj_.emplace(it->second.var, std::move(value));
    DLINEAR_TRACE_FMT("Updated obj function {}", row);
    return;
  }
  const auto row_it = rows_.find(row);
  if (row_it != rows_.end()) {
    row_it->second.addends.emplace(it->second.var, std::move(value));
    DLINEAR_TRACE_FMT("Updated row {}", row);
  }
}

void MpsDriver::AddRhs(const std::string &rhs, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddRhs {} {} {}", rhs, row, value);
  if (!VerifyStrictRhs(rhs)) return;
  try {
    switch (Row &row_data = rows_.at(row); row_data.sense) {
      case Sense::L:
        row_data.ub = std::move(value);
        break;
      case Sense::G:
        row_data.lb = std::move(value);
        break;
      case Sense::E:
        row_data.lb = row_data.ub = std::move(value);
        break;
      case Sense::N:
        DLINEAR_WARN("SenseType N is used only for objective function. No action to take");
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &) {
    DLINEAR_RUNTIME_ERROR_FMT("Row {} not found", row);
  }
  DLINEAR_TRACE_FMT("Updated rhs {}", row);
}

void MpsDriver::AddRange(const std::string &rhs, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddRange {} {} {}", rhs, row, value);
  if (!VerifyStrictRhs(rhs)) return;
  try {
    switch (Row &row_data = rows_.at(row); row_data.sense) {
      case Sense::L:
        mpq_abs(value.get_mpq_t(), value.get_mpq_t());
        row_data.lb = row_data.ub.value_or(0) - value;
        if (!row_data.ub.has_value()) row_data.ub = 0;  // If there was no upper bound, set it to 0
        break;
      case Sense::G:
        mpq_abs(value.get_mpq_t(), value.get_mpq_t());
        row_data.ub = row_data.lb.value_or(0) + value;
        if (!row_data.lb.has_value()) row_data.lb = 0;  // If there was no lower bound, set it to 0
        break;
      case Sense::E:
        if (value > 0) {
          row_data.ub = row_data.ub.value_or(0) + value;
          if (!row_data.lb.has_value()) row_data.lb = 0;  // If there was no lower bound, set it to 0
        } else {
          row_data.lb = row_data.lb.value_or(0) + value;
          if (!row_data.ub.has_value()) row_data.ub = 0;  // If there was no upper bound, set it to 0
        }
        break;
      case Sense::N:
        DLINEAR_WARN("Sense N is used only for objective function. No action to take");
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &) {
    DLINEAR_RUNTIME_ERROR_FMT("Row {} not found", row);
  }
}

void MpsDriver::AddBound(const BoundType type, const std::string &bound, const std::string &column, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {} {}", type, bound, column, value);
  if (!VerifyStrictBound(bound)) return;
  try {
    switch (Column &column_data = columns_.at(column); type) {
      case BoundType::UI:
        column_data.is_integer = true;
        [[fallthrough]];
      case BoundType::UP:
        column_data.ub = std::move(value);
        break;
      case BoundType::LI:
        column_data.is_integer = true;
        column_data.is_infinite_ub_integer = true;
        [[fallthrough]];
      case BoundType::LO:
        column_data.lb = std::move(value);
        break;
      case BoundType::FX:
        column_data.lb = column_data.ub = std::move(value);
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &) {
    DLINEAR_RUNTIME_ERROR_FMT("Column {} not found", column);
  }

  DLINEAR_TRACE_FMT("Updated bound {}", column);
}

void MpsDriver::AddBound(const BoundType type, const std::string &bound, const std::string &column) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {}", type, bound, column);
  if (!VerifyStrictBound(bound)) return;
  try {
    switch (Column &column_data = columns_.at(column); type) {
      case BoundType::BV:
        column_data.lb = 0;
        column_data.ub = 1;
        break;
      case BoundType::FR:
      case BoundType::MI:
        column_data.is_infinite_lb = true;
        break;
      case BoundType::PL:
        column_data.is_infinite_ub_integer = true;
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } catch (const std::out_of_range &) {
    DLINEAR_RUNTIME_ERROR_FMT("Column {} not found", column);
  }

  DLINEAR_TRACE_FMT("Updated bound {}", column);
}

void MpsDriver::SetMarker([[maybe_unused]] const std::string &name, const std::string &keyword) {
  DLINEAR_TRACE_FMT("Driver::SetMarker({} {})", name, keyword);
  if (keyword == "INTORG") {
    DLINEAR_DEBUG("Integers start");
    integer_columns_ = true;
    return;
  }
  if (keyword == "INTEND") {
    DLINEAR_DEBUG("Integers end");
    integer_columns_ = false;
    return;
  }
  DLINEAR_WARN_FMT("Unknown marker '{}'. Ignoring", keyword);
}

void MpsDriver::End() {
  DLINEAR_DEBUG_FMT("Driver::EndData reached end of file {}", problem_name_);
  DLINEAR_DEBUG_FMT("Found {} variables and {} constraints", columns_.size(), rows_.size());

  // Add colomn bounds
  for (const auto &[name, column_data] : columns_) {
    const mpq_class *const lb = column_data.ComputeLb();
    const mpq_class *const ub = column_data.ComputeUb();

    // Case I - Fixed bound
    if (lb != nullptr && ub != nullptr && *lb == *ub) {
      DLINEAR_TRACE_FMT("Column {} == {}", name, *lb);
      context_.Assert(column_data.var == *lb);
      continue;
    }
    // Case II: The bounds are different or only one is set
    if (lb != nullptr) {
      DLINEAR_TRACE_FMT("Column {} >= {}", name, *lb);
      context_.Assert(column_data.var >= *lb);
    }
    if (ub != nullptr) {
      DLINEAR_TRACE_FMT("Column {} <= {}", name, *ub);
      context_.Assert(column_data.var <= *ub);
    }
  }

  for (auto &[row, row_data] : rows_) {
    DLINEAR_ASSERT(row_data.sense != Sense::N, "Only the objective row can have sense N");
    if (row_data.addends.empty()) continue;  // No point in adding empty rows
    if (!row_data.lb.has_value() && !row_data.ub.has_value()) {
      DLINEAR_TRACE_FMT("Row {} has no RHS. Adding 0", row);
      AddRhs(rhs_name_, row, 0);
    }
    const Expression constr = ExpressionAddFactory{0, std::move(row_data.addends)}.GetExpression();

    // Case I - Fixed row
    if (row_data.lb.has_value() && row_data.ub.has_value() && row_data.lb.value() == row_data.ub.value()) {
      context_.Assert(constr == row_data.lb.value());
      continue;
    }
    // Case II: The bounds are different or only one is set
    if (row_data.lb.has_value()) {
      context_.Assert(constr >= row_data.lb.value());
    }
    if (row_data.ub.has_value()) {
      context_.Assert(constr <= row_data.ub.value());
    }
  }

  if (context_.config().optimize() && !obj_row_.empty()) {
    Expression obj_expression = ExpressionAddFactory{0, obj_}.GetExpression();
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
    os << "(declare-const " << name << " Real)\n";
  }
  for (const auto &f : context_.assertions()) {
    if (f.EqualTo(Formula::True())) continue;
    os << "(assert " << f.to_smt2_string() << ")\n";
  }
  if (!obj_row_.empty() && !obj_.empty()) {
    const Expression obj_expression = ExpressionAddFactory{0, obj_}.GetExpression();
    if (is_min_)
      os << "(minimize (+ " << obj_expression.to_smt2_string() << "))\n";
    else
      os << "(maximize (+ " << obj_expression.to_smt2_string() << "))\n";
  }
  os << "(check-sat)\n";
  if (!obj_row_.empty() && !obj_.empty()) os << "(get-objectives)\n";
}

}  // namespace dlinear::mps
