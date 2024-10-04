#include "dlinear/symbolic/symbolic_variable.h"

#include <atomic>
#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <utility>

using std::atomic;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::string;

namespace dlinear::drake::symbolic {

std::vector<std::string> Variable::names_{{"dummy"}};

Variable::Id Variable::get_next_id() {
  // Note that id 0 is reserved for anonymous variable which is created by the
  // default constructor, Variable(). As a result, we have an invariant
  // "get_next_id() > 0".
  static atomic<Id> next_id(1);
  return next_id++;
}

Variable::Variable(string name, const Type type) : id_{get_next_id()}, type_{type} {
  assert(id_ > 0);
  names_.push_back(std::move(name));
  assert(names_.size() == id_ + 1);
}

Variable::Id Variable::get_id() const { return id_; }
Variable::Type Variable::get_type() const { return type_; }
string Variable::get_name() const { return names_[id_]; }
string Variable::to_string() const {
  ostringstream oss;
  oss << *this;
  return oss.str();
}

ostream &operator<<(ostream &os, const Variable &var) {
  os << var.get_name();
  return os;
}

ostream &operator<<(ostream &os, Variable::Type type) {
  switch (type) {
    case Variable::Type::CONTINUOUS:
      return os << "Continuous";
    case Variable::Type::BINARY:
      return os << "Binary";
    case Variable::Type::INTEGER:
      return os << "Integer";
    case Variable::Type::BOOLEAN:
      return os << "Boolean";
  }
  // Should be unreachable.
  throw std::runtime_error("Should not be reachable.");
}
}  // namespace dlinear::drake::symbolic
