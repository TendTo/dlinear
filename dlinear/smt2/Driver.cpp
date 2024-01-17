/**
 * @file Driver.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Driver.h"

#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <utility>
#include <vector>

#include "dlinear/util/Stats.h"
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
using std::nextafter;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::string;
using std::vector;

namespace dlinear::smt2 {

Smt2Driver::Smt2Driver(Context &context)
    : context_{context},
      debug_scanning_{context_.config().debug_scanning()},
      debug_parsing_{context_.config().debug_parsing()} {}

bool Smt2Driver::parse_stream(istream &in, const string &sname) {
  static Stats stat{DLINEAR_INFO_ENABLED, "SMT2 Driver", "Total time spent in SMT2 parsing"};
  TimerGuard check_sat_timer_guard(&stat.mutable_timer(), stat.enabled(), true);
  streamname_ = sname;

  Smt2Scanner scanner(&in);
  scanner.set_debug(debug_scanning_);
  this->scanner_ = &scanner;

  Smt2Parser parser(*this);
  parser.set_debug_level(debug_parsing_);
  return parser.parse() == 0;
}

bool Smt2Driver::parse_file(const string &filename) {
  if (context_.config().read_from_stdin()) {
    // Option --in passed to dreal.
    return parse_stream(cin, "(stdin)");
  }
  ifstream in(filename.c_str());
  if (!in.good()) {
    return false;
  }
  return parse_stream(in, filename);
}

bool Smt2Driver::parse_string(const string &input, const string &sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

void Smt2Driver::error(const location &l, const string &m) { cerr << l << " : " << m << endl; }

void Smt2Driver::error(const string &m) { cerr << m << endl; }

void Smt2Driver::CheckSat() {}

void Smt2Driver::GetModel() {}

void Smt2Driver::Maximize(const Expression &f) {
  if (context_.config().produce_models()) context_.Maximize(f);
}
void Smt2Driver::Minimize(const Expression &f) {
  if (context_.config().produce_models()) context_.Minimize(f);
}

Variable Smt2Driver::RegisterVariable(const string &name, const Sort sort) {
  const Variable v{ParseVariableSort(name, sort)};
  scope_.insert(v.get_name(), VariableOrConstant(v));
  return v;
}

Variable Smt2Driver::DeclareVariable(const string &name, const Sort sort) {
  Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v);
  return v;
}

void Smt2Driver::DeclareVariable(const string &name, const Sort sort, const Term &lb, const Term &ub) {
  const Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v, lb.expression(), ub.expression());
}

string Smt2Driver::MakeUniqueName(const string &name) {
  ostringstream oss;
  // The \ character ensures that the name cannot occur in an SMT-LIBv2 file.
  oss << "L" << nextUniqueId_++ << "\\" << name;
  return oss.str();
}

Variable Smt2Driver::DeclareLocalVariable(const string &name, const Sort sort) {
  const Variable v{ParseVariableSort(MakeUniqueName(name), sort)};
  scope_.insert(name, VariableOrConstant(v));  // v is not inserted under its own name.
  context_.DeclareVariable(v, false /* This local variable is not a model variable. */);
  return v;
}

const Smt2Driver::VariableOrConstant &Smt2Driver::lookup_variable(const string &name) {
  const auto it = scope_.find(name);
  if (it == scope_.cend()) {
    DLINEAR_RUNTIME_ERROR_FMT("{} is an undeclared variable.", name);
  }
  return it->second;
}

Variable Smt2Driver::ParseVariableSort(const string &name, const Sort s) { return Variable{name, SortToType(s)}; }

void Smt2Driver::DefineLocalConstant(const string &name, const Expression &value) {
  DLINEAR_ASSERT(is_constant(value), "Value must be a constant expression.");
  scope_.insert(name, VariableOrConstant(value));
}

}  // namespace dlinear::smt2
