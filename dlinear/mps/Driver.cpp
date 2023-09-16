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
#include <tl/optional.hpp>
#include <utility>
#include <vector>

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
MpsDriver::MpsDriver(Context context) : context_{std::move(context)} {}

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
  if (strict_mps_) [[unlikely]] {
    if (bound_name_.empty()) [[unlikely]] {
      bound_name_ = bound;
    } else if (bound_name_ != bound) [[unlikely]] {
      DLINEAR_WARN_FMT("First bound was '{}', found new bound '{}'. Skipping", bound_name_, bound);
      return false;
    }
  }
  return true;
}

bool MpsDriver::VerifyStrictRhs(const std::string &rhs) {
  if (strict_mps_) [[unlikely]] {
    if (rhs_name_.empty()) [[unlikely]] {
      rhs_name_ = rhs;
    } else if (rhs_name_ != rhs) [[unlikely]] {
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
  rows_[row] = Expression::Zero();
  row_senses_[row] = sense;
}

void MpsDriver::AddColumn(const std::string &row, const std::string &column, double value) {
  DLINEAR_TRACE_FMT("Driver::AddColumn {} {} {}", row, column, value);
  if (columns_.find(column) == columns_.end()) {
    DLINEAR_TRACE_FMT("Added column {}", column);
    const Variable var = Variable{column};
    columns_[column] = var;  // If not already in the map, add the variable
    context_.DeclareVariable(var);
  }
  rows_[row] += Expression{value * columns_[column]};
  DLINEAR_TRACE_FMT("Updated row {}", rows_[row]);
}

void MpsDriver::AddRhs(const std::string &row, const std::string &rhs, double value) {
  DLINEAR_TRACE_FMT("Driver::AddRhs {} {} {}", row, rhs, value);
  if (!VerifyStrictRhs(rhs)) return;
  rhs_values_[row] = value;
  switch (row_senses_[row]) {
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
  };
  DLINEAR_TRACE_FMT("Updated rhs {}", rhs_[row]);
}

void MpsDriver::AddRange(const std::string &row, const std::string &rhs, double value) {
  DLINEAR_TRACE_FMT("Driver::AddRange {} {} {}", row, rhs, value);
  if (!VerifyStrictRhs(rhs)) return;
  switch (row_senses_[row]) {
    case Sense::L:
      rhs_[row] = rhs_[row] && (rhs_values_[row] - value <= rows_[row]);
      break;
    case Sense::G:
      rhs_[row] = rhs_[row] && (rows_[row] <= rhs_values_[row] + value);
      break;
    case Sense::E:
      rhs_[row] = value > 0 ? rhs_values_[row] <= rows_[row] && rows_[row] <= rhs_values_[row] + value
                            : rhs_values_[row] + value <= rows_[row] && rows_[row] <= rhs_values_[row];
      break;
    case Sense::N:
      DLINEAR_WARN("Sense N is used only for objective function. No action to take");
      break;
    default:
      DLINEAR_UNREACHABLE();
  };
}

void MpsDriver::AddBound(const std::string &column, const std::string &bound, double value, BoundType bound_type) {
  DLINEAR_TRACE_FMT("Driver::AddBound {} {} {} {}", column, bound, value, bound_type);
  if (!VerifyStrictBound(bound)) return;
  if (bounds_.find(column) == bounds_.end())
    bounds_[column] = Formula::True();  // If not already in the map, add a placeholder formula
  switch (bound_type) {
    case BoundType::UP:
    case BoundType::UI:
      bounds_[column] = bounds_[column] && (columns_[column] <= value);
      if (value <= 0) skip_lower_bound_[column] = true;
      break;
    case BoundType::LO:
    case BoundType::LI:
      bounds_[column] = bounds_[column] && (value <= columns_[column]);
      skip_lower_bound_[column] = true;
      break;
    case BoundType::FX:
      bounds_[column] = bounds_[column] && (columns_[column] == value);
      skip_lower_bound_[column] = true;
      break;
    case BoundType::PL:
      skip_lower_bound_[column] = true;
      [[fallthrough]];
    case BoundType::FR:
    case BoundType::MI:
      DLINEAR_DEBUG("Infinity bound, no action to take");
      break;
    case BoundType::BV:
      DLINEAR_RUNTIME_ERROR("Binary variable bound not supported");
      bounds_[column] = (columns_[column] == 0) || (columns_[column] == 1);
      skip_lower_bound_[column] = false;
      break;
    default:
      DLINEAR_UNREACHABLE();
  };
  DLINEAR_TRACE_FMT("Updated bound {}", bounds_[column]);
}

void MpsDriver::End() {
  DLINEAR_TRACE("Driver::EndData");
  for (const auto &[name, sense] : row_senses_) {
    if (rhs_.find(name) == rhs_.end()) {
      DLINEAR_DEBUG_FMT("Row {} has no RHS. Adding 0", name);
      AddRhs(name, rhs_name_, 0);
    }
  }
  for (const auto &[name, column] : columns_) {
    if (skip_lower_bound_.find(name) == skip_lower_bound_.end()) {
      DLINEAR_DEBUG_FMT("Column has no lower bound. Adding 0 <= {}", name);
      AddBound(name, bound_name_, 0, BoundType::LO);
    }
  }
  DLINEAR_DEBUG_FMT("Found {} assertions", n_assertions());
  for (const auto &[name, bound] : bounds_) {
    DLINEAR_DEBUG_FMT("Assertion {}", bound);
    context_.Assert(bound);
  }
  for (const auto &[name, row] : rhs_) {
    if (row.EqualTo(Formula::True())) continue;
    DLINEAR_DEBUG_FMT("Assertion {}", row);
    context_.Assert(row);
  }
  CheckSat();
}

void MpsDriver::CheckSat() {
  mpq_class actual_precision = context_.config().precision();
  const optional<Box> model{context_.CheckSat(&actual_precision)};
  double actual_precision_upper = nextafter(actual_precision.get_d(), numeric_limits<double>::infinity());
  this->actual_precision_ = actual_precision.get_d();
  if (model) {
    // fmt::print uses shortest round-trip format for doubles, by default
    fmt::print("delta-sat with delta = {} ( > {})", actual_precision_upper, actual_precision);
  } else {
    fmt::print("unsat");
  }
  if (context_.config().with_timings()) {
    fmt::print(" after {} seconds", main_timer.seconds());
  }
  fmt::print("\n");
  if (model && context_.config().produce_models()) {
    fmt::print("{}\n", *model);
  }
}

}  // namespace dlinear::mps
