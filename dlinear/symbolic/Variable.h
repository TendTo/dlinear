#pragma once

#include <functional>
#include <memory>
#include <ostream>
#include <string>

namespace dlinear::symbolic {

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

  /**
   * Default constructor. Constructs a dummy variable of CONTINUOUS type. This
   * is needed to have Eigen::Matrix<Variable>. The objects created by the
   * default constructor share the same ID, zero. As a result, they all are
   * identified as a single variable by equality operator (==). They all have
   * the same hash value as well.
   *
   * It is allowed to construct a dummy variable but it should not be used to
   * construct a symbolic expression.
   */
  Variable() : id_{0}, type_{Type::CONTINUOUS}, name_{} {}

  /**
   * Constructs a variable with a string. If not specified, it has CONTINUOUS
   * type by default
   * @param name The name of the variable.
   * @param type The type of the variable. It is CONTINUOUS by default.
   */
  explicit Variable(std::string name, Type type = Type::CONTINUOUS);

  /**
   * Check if this is a dummy variable (ID = 0) which is created by
   * the default constructor.
   * @return whether the variable is dummy.
   */
  bool is_dummy() const { return id_ == 0; }
  Id get_id() const;
  Type get_type() const;
  size_t get_hash() const { return std::hash<Id>{}(id_); }
  const std::string& get_name() const;
  std::string to_string() const;

  /**
   * Checks the equality of two variables based on their ID values.
   * @param v The variable to compare with.
   */
  bool equal_to(const Variable &v) const { return get_id() == v.get_id(); }

  /**
   * Compares two variables based on their ID values.
   * @param v The variable to compare with.
   */
  bool less(const Variable &v) const { return get_id() < v.get_id(); }

  friend std::ostream &operator<<(std::ostream &os, const Variable &var);

 private:
  static Id get_next_id();       // Produces a unique ID for a variable.
  Id id_{};                      ///< Unique identifier.
  Type type_{Type::CONTINUOUS};  ///< Type of variable.

  // Variable class has shared_ptr<string> instead of string to be
  // drake::test::IsMemcpyMovable.
  // Please check https://github.com/RobotLocomotion/drake/issues/5974
  // for more information.
  // std::shared_ptr<std::string> name_;  // Name of variable.
  std::string name_{};  ///< Name of variable.
};

std::ostream &operator<<(std::ostream &os, Variable::Type type);

}  // namespace dlinear::symbolic

namespace std {

template <>
struct less<dlinear::symbolic::Variable> {
  bool operator()(const dlinear::symbolic::Variable &lhs,
                  const dlinear::symbolic::Variable &rhs) const {
    return lhs.less(rhs);
  }
};

template <>
struct equal_to<dlinear::symbolic::Variable> {
  bool operator()(const dlinear::symbolic::Variable &lhs,
                  const dlinear::symbolic::Variable &rhs) const {
    return lhs.equal_to(rhs);
  }
};

template <>
struct hash<dlinear::symbolic::Variable> {
  size_t operator()(const dlinear::symbolic::Variable &v) const {
    return v.get_hash();
  }
};

}  // namespace std
