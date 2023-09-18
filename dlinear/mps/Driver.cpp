/**
 * @file Driver.cpp
 * @author dlinear
 * @date 15 Sep 2023
 * @copyright 2023 dlinear
 */

#include "Driver.h"

#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <utility>
#include <vector>
// Optional is a header-only library for optional/maybe values.
#include <tl/optional.hpp>

#include "dlinear/mps/parser.yy.hpp"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

using std::cerr;
using std::cin;
using std::cout;
using std::endl;
using std::ifstream;
using std::istream;
using std::istringstream;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::string;
using std::vector;
using tl::optional;

namespace dlinear::mps {
MpsDriver::MpsDriver(Context *context) : context_{context} {}

bool MpsDriver::parse_stream(istream &in, const string &sname) {
  stream_name_ = sname;

  MpsScanner scanner(&in);
  scanner.set_debug(debug_scanning_);
  this->scanner_ = &scanner;

  MpsParser parser(*this);
  parser.set_debug_level(debug_parsing_);
  return parser.parse() == 0;
}

bool MpsDriver::parse_file(const string &filename) {
  ifstream in(filename.c_str());
  if (!in.good()) {
    return false;
  }
  return parse_stream(in, filename);
}

bool MpsDriver::parse_string(const string &input, const string &sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

bool MpsDriver::VerifyStrictBound(const std::string &bound) {
  if (strict_mps_) [[unlikely]] {            // NOLINT
    if (bound_name_.empty()) [[unlikely]] {  // NOLINT
      bound_name_ = bound;
    } else if (bound_name_ != bound) [[unlikely]] {  // NOLINT
      DLINEAR_WARN_FMT("First bound was '{}', found new bound '{}'. Skipping", bound_name_, bound);
      return false;
    }
  }
  return true;
}

bool MpsDriver::VerifyStrictRhs(const std::string &rhs) {
  if (strict_mps_) [[unlikely]] {          // NOLINT
    if (rhs_name_.empty()) [[unlikely]] {  // NOLINT
      rhs_name_ = rhs;
    } else if (rhs_name_ != rhs) [[unlikely]] {  // NOLINT
      DLINEAR_WARN_FMT("First RHS was '{}', found new RHS '{}'. Skipping", rhs_name_, rhs);
      return false;
    }
  }
  return true;
}

void MpsDriver::error(const location &l, const string &m) { cerr << l << " : " << m << endl; }
void MpsDriver::error(const string &m) { cerr << m << endl; }

void MpsDriver::AddRow(Sense sense, const std::string &row) {
  DLINEAR_TRACE_FMT("Driver::AddRow {} {}", sense, row);
  row_senses_[row] = sense;
}

void MpsDriver::AddColumn(const std::string &column, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddColumn {} {} {}", row, column, value);
  if (columns_.find(column) == columns_.end()) {
    DLINEAR_TRACE_FMT("Added column {}", column);
    const Variable var = Variable{column};
    columns_[column] = var;  // If not already in the map, add the variable
    context_->DeclareVariable(var);
  }
  rows_[row] += Expression{value * columns_[column]};
  DLINEAR_TRACE_FMT("Updated row {}", rows_[row]);
}

void MpsDriver::AddRhs(const std::string &rhs, const std::string &row, mpq_class value) {
  DLINEAR_TRACE_FMT("Driver::AddRhs {} {} {}", rhs, row, value);
  if (!VerifyStrictRhs(rhs)) return;
  rhs_values_[row] = value;
  try {
    switch (row_senses_.at(row)) {
      case Sense::L:
        rhs_[row] = rows_[row] <= value;
        break;
      case Sense::G:
        rhs_[row] = value <= rows_[row];
        break;
      case Sense::E:
        rhs_[row] = rows_[row] == value;
        break;
      case Sense::N:
        // TODO(Tend): Check if this is correct
        DLINEAR_DEBUG("Sense N is used only for objective function. No action to take");
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
    switch (row_senses_.at(row)) {
      case Sense::L:
        rhs_[row] = rhs_[row] && (rhs_values_[row] - Expression{value} <= rows_[row]);
        break;
      case Sense::G:
        rhs_[row] = rhs_[row] && (rows_[row] <= rhs_values_[row] + Expression{value});
        break;
      case Sense::E:
        rhs_[row] = value > 0 ? rhs_values_[row] <= rows_[row] && rows_[row] <= rhs_values_[row] + Expression{value}
                              : rhs_values_[row] + Expression{value} <= rows_[row] && rows_[row] <= rhs_values_[row];
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
  if (bounds_.find(column) == bounds_.end())
    bounds_[column] = Formula::True();  // If not already in the map, add a placeholder formula
  try {
    switch (bound_type) {
      case BoundType::UP:
      case BoundType::UI:
        bounds_[column] = bounds_[column] && (columns_.at(column) <= value);
        if (value <= 0) skip_lower_bound_[column] = true;
        break;
      case BoundType::LO:
      case BoundType::LI:
        bounds_[column] = bounds_[column] && (value <= columns_.at(column));
        skip_lower_bound_[column] = true;
        break;
      case BoundType::FX:
        bounds_[column] = bounds_[column] && (columns_.at(column) == value);
        skip_lower_bound_[column] = true;
        break;
      case BoundType::PL:
        skip_lower_bound_[column] = true;
        [[fallthrough]];
      case BoundType::FR:
      case BoundType::MI:
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

void MpsDriver::AddBound(BoundType bound_type, const std::string &bound, const std::string &column) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {} {}", bound_type, bound, column);
  if (!VerifyStrictBound(bound)) return;
  if (bounds_.find(column) == bounds_.end())
    bounds_[column] = Formula::True();  // If not already in the map, add a placeholder formula
  try {
    switch (bound_type) {
      case BoundType::BV:
        bounds_[column] = (0 <= columns_.at(column)) && (columns_.at(column) <= 1);
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

void MpsDriver::End() {
  DLINEAR_TRACE("Driver::EndData");
  for (const auto &[row, sense] : row_senses_) {
    if (rhs_.find(row) == rhs_.end()) {
      DLINEAR_DEBUG_FMT("Row {} has no RHS. Adding 0", row);
      AddRhs(rhs_name_, row, 0);
    }
  }
  for (const auto &[column, var] : columns_) {
    if (skip_lower_bound_.find(column) == skip_lower_bound_.end()) {
      DLINEAR_DEBUG_FMT("Column has no lower bound. Adding 0 <= {}", column);
      AddBound(BoundType::LO, bound_name_, column, 0);
    }
  }
  DLINEAR_DEBUG_FMT("Found {} assertions", n_assertions());
  for (const auto &[name, bound] : bounds_) {
    DLINEAR_DEBUG_FMT("Assertion {}", bound);
    context_->Assert(bound);
  }
  for (const auto &[name, row] : rhs_) {
    if (row.EqualTo(Formula::True())) continue;
    DLINEAR_DEBUG_FMT("Assertion {}", row);
    context_->Assert(row);
  }
  CheckSat();
}

void MpsDriver::CheckSat() {}

}  // namespace dlinear::mps
