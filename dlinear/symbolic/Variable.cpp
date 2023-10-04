#include "dlinear/symbolic/Variable.h"

#include <atomic>
#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <utility>

#include "dlinear/util/exception.h"

using std::atomic;
using std::make_shared;
using std::ostream;
using std::ostringstream;
using std::string;

namespace dlinear::symbolic {

Variable::Id Variable::get_next_id() {
  // Note that id 0 is reserved for anonymous variable which is created by the
  // default constructor, Variable(). As a result, we have an invariant
  // "get_next_id() > 0".
  static atomic<Id> next_id(1);
  return next_id++;
}

Variable::Variable(string name, const Type type)
    : id_{get_next_id()}, type_{type}, name_{std::move(name)} {
  DLINEAR_ASSERT(id_ > 0,
                 "ID of a variable should be greater than 0, since 0 is "
                 "reserved for dummy variables");
}

Variable::Id Variable::get_id() const { return id_; }
Variable::Type Variable::get_type() const { return type_; }
const string &Variable::get_name() const { return name_; }
string Variable::to_string() const { return (ostringstream{} << *this).str(); }

ostream &operator<<(ostream &os, const Variable &var) {
  return os << var.get_name();
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
  DLINEAR_UNREACHABLE();
}
}  // namespace dlinear::symbolic
