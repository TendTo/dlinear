#pragma once

#include <cstddef>
#include <functional>
#include <memory>
#include <ostream>
#include <string>

#include "dlinear/symbolic/hash.h"

namespace dlinear::drake {
namespace symbolic {

/** Represents a symbolic variable. */
class Variable {
 public:
  typedef size_t Id;

  /** Supported types of symbolic variables. */
  enum class Type {
    CONTINUOUS,  ///< A CONTINUOUS variable takes a `mpq_class` value.
    INTEGER,     ///< An INTEGER variable takes an `int` value.
    BINARY,      ///< A BINARY variable takes an integer value from {0, 1}.
    BOOLEAN,     ///< A BOOLEAN variable takes a `bool` value.
  };

  Variable(const Variable &) = default;
  Variable &operator=(const Variable &) = default;
  Variable(Variable &&) = default;
  Variable &operator=(Variable &&) = default;

  /** Default constructor. Constructs a dummy variable of CONTINUOUS type. This
   *  is needed to have Eigen::Matrix<Variable>. The objects created by the
   *  default constructor share the same ID, zero. As a result, they all are
   *  identified as a single variable by equality operator (==). They all have
   *  the same hash value as well.
   *
   *  It is allowed to construct a dummy variable but it should not be used to
   *  construct a symbolic expression.
   */
  Variable() : id_{0}, type_{Type::CONTINUOUS} {}

  /** Default destructor. */
  ~Variable() = default;

  /** Constructs a variable with a string. If not specified, it has CONTINUOUS
   * type by default.*/
  explicit Variable(std::string name, Type type = Type::CONTINUOUS);

  /** Checks if this is a dummy variable (ID = 0) which is created by
   *  the default constructor. */
  bool is_dummy() const { return get_id() == 0; }
  Id get_id() const;
  Type get_type() const;
  size_t get_hash() const { return std::hash<Id>{}(id_); }
  std::string get_name() const;
  std::string to_string() const;

  /// Checks the equality of two variables based on their ID values.
  bool equal_to(const Variable &v) const { return id_ == v.id_; }

  /// Compares two variables based on their ID values.
  bool less(const Variable &v) const { return id_ < v.id_; }

  friend std::ostream &operator<<(std::ostream &os, const Variable &var);

 private:
  static std::vector<std::string> names_;  ///< Names of variables.
  // Produces a unique ID for a variable.
  static Id get_next_id();
  Id id_{};                                      ///< Unique identifier.
  Type type_{Type::CONTINUOUS};                  ///< Type of variable.
};

std::ostream &operator<<(std::ostream &os, Variable::Type type);

}  // namespace symbolic

}  // namespace dlinear::drake

namespace std {
/* Provides std::less<dlinear::drake::symbolic::Variable>. */
template <>
struct less<dlinear::drake::symbolic::Variable> {
  bool operator()(const dlinear::drake::symbolic::Variable &lhs, const dlinear::drake::symbolic::Variable &rhs) const {
    return lhs.less(rhs);
  }
};

/* Provides std::equal_to<dlinear::drake::symbolic::Variable>. */
template <>
struct equal_to<dlinear::drake::symbolic::Variable> {
  bool operator()(const dlinear::drake::symbolic::Variable &lhs, const dlinear::drake::symbolic::Variable &rhs) const {
    return lhs.equal_to(rhs);
  }
};

template <>
struct hash<dlinear::drake::symbolic::Variable> {
  size_t operator()(const dlinear::drake::symbolic::Variable &v) const { return v.get_hash(); }
};

}  // namespace std
