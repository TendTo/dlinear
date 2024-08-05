#include "dlinear/symbolic/symbolic_environment.h"

#include <cmath>
#include <initializer_list>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

namespace dlinear::drake::symbolic {

using std::endl;
using std::initializer_list;
using std::ostream;
using std::ostringstream;
using std::runtime_error;
using std::string;

namespace {
void throw_if_dummy(const Variable &var) {
  if (var.is_dummy()) {
    ostringstream oss;
    oss << "Dummy variable (ID = 0) is detected" << "in the initialization of an environment.";
    throw runtime_error(oss.str());
  }
}
}  // anonymous namespace

Environment::Environment(const std::initializer_list<value_type> init) : map_(init) {
  for (const auto &p : init) {
    throw_if_dummy(p.first);
  }
}

Environment::Environment(const std::initializer_list<key_type> vars) {
  for (const auto &var : vars) {
    throw_if_dummy(var);
    map_.emplace(var, 0.0);
  }
}

Environment::Environment(Environment::map m) : map_{std::move(m)} {
  for (const auto &p : map_) {
    throw_if_dummy(p.first);
  }
}

Environment::Environment(const Environment::double_map &m) : map_{m.size()} {
  for (const auto &p : m) {
    throw_if_dummy(p.first);
    map_.emplace(p.first, p.second);
  }
}

std::pair<Environment::iterator, bool> Environment::insert(const key_type &key, const mapped_type &elem) {
  throw_if_dummy(key);
  return map_.emplace(key, elem);
}

Variables Environment::domain() const {
  Variables dom;
  for (const auto &p : map_) {
    dom += p.first;
  }
  return dom;
}

string Environment::to_string() const {
  ostringstream oss;
  oss << *this;
  return oss.str();
}

const Environment::mapped_type &Environment::at(const Environment::key_type &key) const {
  const auto &value = map_.at(key);
  if (key.is_dummy()) throw runtime_error("Environment::at is called with a dummy variable.");
  return value;
}

std::size_t Environment::erase(const Environment::key_type &key) { return map_.erase(key); }
void Environment::erase(const Environment::iterator &pos) { map_.erase(pos); }

bool Environment::contains(const key_type &key) const { return map_.find(key) != map_.end(); }

Environment::mapped_type &Environment::operator[](const key_type &key) {
  if (key.is_dummy()) {
    ostringstream oss;
    oss << "Environment::operator[] is called with a dummy variable.";
    throw runtime_error(oss.str());
  }
  return map_[key];
}

const Environment::mapped_type &Environment::operator[](const key_type &key) const {
  if (key.is_dummy()) {
    ostringstream oss;
    oss << "Environment::operator[] is called with a dummy variable.";
    throw runtime_error(oss.str());
  }
  if (!map_.count(key)) {
    ostringstream oss;
    oss << "Environment::operator[] was called on a const Environment " << "with a missing key \"" << key << "\".";
    throw runtime_error(oss.str());
  }
  return map_.at(key);
}

ostream &operator<<(ostream &os, const Environment &env) {
  for (const auto &p : env) {
    os << p.first << " -> " << p.second << ", ";
  }
  return os;
}

}  // namespace dlinear::drake::symbolic
