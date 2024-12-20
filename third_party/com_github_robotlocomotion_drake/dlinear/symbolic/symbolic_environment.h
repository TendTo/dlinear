#pragma once

#include <initializer_list>
#include <ostream>
#include <string>
#include <unordered_map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/symbolic_variable.h"
#include "dlinear/symbolic/symbolic_variables.h"

namespace dlinear::drake::symbolic {
/** Represents a symbolic environment (mapping from a variable to a value).
 *
 * This class is used when we evaluate symbolic expressions or formulas which
 * include unquantified (free) variables. Here are examples:
 *
 * \code{.cpp}
 *   const Variable var_x{"x"};
 *   const Variable var_y{"y"};
 *   const Expression x{var_x};
 *   const Expression y{var_x};
 *   const Expression e1{x + y};
 *   const Expression e2{x - y};
 *   const Formula f{e1 > e2};
 *
 *   // env maps var_x to 2.0 and var_y to 3.0
 *   const Environment env{{var_x, 2.0}, {var_y, 3.0}};
 *
 *   const mpq_class& res1 = e1.Evaluate(env);  // x + y => 2.0 + 3.0 =>  5.0
 *   const mpq_class& res2 = e2.Evaluate(env);  // x - y => 2.0 - 3.0 => -1.0
 *   const bool res = f.Evaluate(env);  // x + y > x - y => 5.0 >= -1.0 => True
 * \endcode
 *
 * Note that it is not allowed to have a dummy variable in an environment. It
 * throws std::runtime_error for the attempts to create an environment with a
 * dummy variable, to insert a dummy variable to an existing environment, or to
 * take a reference to a value mapped to a dummy variable. See the following
 * examples.
 *
 * \code{.cpp}
 *   Variable    var_dummy{};           // OK to have a dummy variable
 *   Environment e1{var_dummy};         // throws std::runtime_error exception
 *   Environment e2{{var_dummy, 1.0}};  // throws std::runtime_error exception
 *   Environment e{};
 *   e.insert(var_dummy, 1.0);          // throws std::runtime_error exception
 *   e[var_dummy] = 3.0;                // throws std::runtime_error exception
 * \endcode
 *
 */
class Environment {
 public:
  Environment(const Environment &) = default;
  Environment &operator=(const Environment &) = default;
  Environment(Environment &&) = default;
  Environment &operator=(Environment &&) = default;

  typedef Variable key_type;
  typedef mpq_class mapped_type;
  typedef typename std::unordered_map<key_type, mapped_type> map;
  typedef typename std::unordered_map<key_type, double> double_map;
  /** std::pair<key_type, mapped_type> */
  typedef typename map::value_type value_type;
  typedef typename map::iterator iterator;
  typedef typename map::const_iterator const_iterator;

  /** Default constructor. */
  Environment() = default;

  /** Default destructor. */
  ~Environment() = default;

  /** List constructor. Constructs an environment from a list of (Variable *
   * mpq_class). */
  Environment(std::initializer_list<value_type> init);

  /** List constructor. Constructs an environment from a list of
   * Variable. Initializes the variables with 0.0. */
  Environment(std::initializer_list<key_type> vars);

  /** Constructs an environment from @p m*/
  explicit Environment(map m);
  explicit Environment(const double_map &m);

  /** Returns an iterator to the beginning. */
  iterator begin() { return map_.begin(); }
  /** Returns an iterator to the end. */
  iterator end() { return map_.end(); }
  /** Returns a const iterator to the beginning. */
  const_iterator begin() const { return map_.cbegin(); }
  /** Returns a const iterator to the end. */
  const_iterator end() const { return map_.cend(); }
  /** Returns a const iterator to the beginning. */
  const_iterator cbegin() const { return map_.cbegin(); }
  /** Returns a const iterator to the end. */
  const_iterator cend() const { return map_.cend(); }

  /** Inserts a pair (@p key, @p elem). */
  std::pair<Environment::iterator, bool> insert(const key_type &key, const mapped_type &elem);
  /** Checks whether the container is empty.  */
  bool empty() const { return map_.empty(); }
  /** Returns the number of elements. */
  size_t size() const { return map_.size(); }

  /** Finds element with specific key. */
  iterator find(const key_type &key) { return map_.find(key); }
  /** Finds element with specific key. */
  const_iterator find(const key_type &key) const { return map_.find(key); }

  /** Returns the value that is mapped to a key equivalent to @p key. */
  const mapped_type &at(const key_type &key) const;

  /** Erases the element with specific @p key */
  std::size_t erase(const key_type &key);
  /** Erases the element at the specified @p pos */
  void erase(const iterator &pos);

  /** Returns the domain of this environment. */
  Variables domain() const;

  /** Returns string representation. */
  std::string to_string() const;

  /** Returns a reference to the value that is mapped to a key equivalent to
   *  @p key, performing an insertion if such key does not already exist.
   */
  mapped_type &operator[](const key_type &key);

  /** As above, but returns a constref and does not perform an insertion
   * (throwing a runtime error instead) if the key does not exist. */
  const mapped_type &operator[](const key_type &key) const;

  /** Checks whether the environment contains a variable @p key. */
  bool contains(const key_type &key) const;

  friend std::ostream &operator<<(std::ostream &os, const Environment &env);

 private:
  map map_;
};
}  // namespace dlinear::drake::symbolic
