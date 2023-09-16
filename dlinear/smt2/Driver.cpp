/**
 * @file Driver.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Driver.h"

#include <iostream>
#include <limits>
#include <sstream>
#include <utility>
#include <vector>
// Optional is a header-only library for optional/maybe values.
#include <tl/optional.hpp>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"

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
using tl::optional;

namespace dlinear {

Smt2Driver::Smt2Driver(Context context) : context_{std::move(context)} {}

bool Smt2Driver::parse_stream(istream &in, const string &sname) {
  streamname_ = sname;

  Smt2Scanner scanner(&in);
  scanner.set_debug(trace_scanning_);
  this->scanner_ = &scanner;

  Smt2Parser parser(*this);
  parser.set_debug_level(trace_parsing_);
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

void Smt2Driver::CheckSat() {
  if (context_.have_objective()) {
    mpq_class obj_lo, obj_up;
    Box model;
    int status = context_.CheckOpt(&obj_lo, &obj_up, &model);
    if (LP_DELTA_OPTIMAL == status) {
      mpq_class diff = obj_up - obj_lo;
      // fmt::print uses shortest round-trip format for doubles, by default
      fmt::print("delta-optimal with delta = {} ( = {}), range = [{}, {}]", diff.get_d(), diff, obj_lo, obj_up);
    } else if (LP_UNBOUNDED == status) {
      fmt::print("unbounded");
    } else if (LP_INFEASIBLE == status) {
      fmt::print("infeasible");
    } else {
      DLINEAR_UNREACHABLE();
    }
    if (context_.config().with_timings()) {
      fmt::print(" after {} seconds", main_timer.seconds());
    }
    fmt::print("\n");
    if (LP_DELTA_OPTIMAL == status && context_.config().produce_models()) {
      fmt::print("{}\n", model);
    }
  } else {
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
}

namespace {
ostream &PrintModel(ostream &os, const Box &box) {
  os << "(model\n";
  for (int i = 0; i < box.size(); ++i) {
    const Variable &var{box.variable(i)};
    os << "  (define-fun " << var << " () ";
    switch (var.get_type()) {
      case Variable::Type::CONTINUOUS:
        os << Sort::Real;
        break;
      case Variable::Type::BINARY:
        os << Sort::Binary;
        break;
      case Variable::Type::INTEGER:
        os << Sort::Int;
        break;
      case Variable::Type::BOOLEAN:
        os << Sort::Bool;
        break;
    }
    os << " ";
    const Box::Interval &iv{box[i]};
    if (iv.is_degenerated()) {
      os << iv.lb();
    } else {
      os << iv;
    }
    os << ")\n";
  }
  return os << ")";
}
}  // namespace

void Smt2Driver::GetModel() {
  const Box &box{context_.get_model()};
  if (box.empty()) {
    cout << "(error \"model is not available\")" << endl;
  } else {
    PrintModel(cout, box) << endl;
  }
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

}  // namespace dlinear
