/**
 * @file Environment.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @copyright 2019 Drake (https://drake.mit.edu)
 * @licence Apache-2.0 license
 * @brief Environment class
 * 
 * Represents a symbolic environment (mapping from a variable to a value).
 */
#pragma once

#include <initializer_list>
#include <ostream>
#include <unordered_map>

#include "dlinear/libs/gmp.h"
#include "dlinear/symbolic/Variable.h"
#include "dlinear/symbolic/Variables.h"

namespace dlinear::symbolic {
/** Represents a symbolic environment (mapping from a variable to a value).
 *
 * This class is used when we evaluate symbolic expressions or formulas which
 * include unquantified (free) variables. Here are examples:
 * @code
 * const Variable var_x{"x"};
 * const Variable var_y{"y"};
 * const Expression x{var_x};
 * const Expression y{var_x};
 * const Expression e1{x + y};
 * const Expression e2{x - y};
 * const Formula f{e1 > e2};
 *
 * // env maps var_x to 2.0 and var_y to 3.0
 * const Environment env{{var_x, 2.0}, {var_y, 3.0}};
 *
 * const mpq_class res1 = e1.Evaluate(env);  // x + y => 2.0 + 3.0 =>  5.0
 * const mpq_class res2 = e2.Evaluate(env);  // x - y => 2.0 - 3.0 => -1.0
 * const bool res = f.Evaluate(env);  // x + y > x - y => 5.0 >= -1.0 => True
 * @endcode
 */
class Environment {
 public:
  using key_type = Variable;
  using mapped_type = mpq_class;
  using map = std::unordered_map<key_type, mapped_type>;
  /** std::pair<key_type, mapped_type> */
  using value_type = map::value_type;
  using iterator = map::iterator;
  using const_iterator = map::const_iterator;

  /** @constructor{environment} */
  Environment() = default;

  /**
   * Construct a new environment object from a list of (Variable, double).
   * @param init initializer list of (Variable, double)
   * @throws std::runtime_exception if @p init include a dummy variable or a NaN value.
   */
  Environment(std::initializer_list<value_type> init);

  /**
   * Construct a new environment object from a list of variables.
   *
   * Initializes the variables with 0.0.
   * @param vars initializer list of variables
   * @throws std::runtime_exception if @p vars include a dummy variable.
   */
  Environment(std::initializer_list<key_type> vars);

  /**
   * Construct a new environment object from the map @p m between variables and values.
   * @param m map between variables and values
   * @throws std::runtime_exception if @p m include a dummy variable or a NaN value.
   */
  explicit Environment(map m);

  /** @getter{iterator to the beginning, environment} */
  iterator begin() { return map_.begin(); }
  /** @getter{iterator to the end, environment} */
  iterator end() { return map_.end(); }
  /** @getter{const iterator to the beginning, environment} */
  [[nodiscard]] const_iterator begin() const { return map_.cbegin(); }
  /** @getter{const iterator to the end, environment} */
  [[nodiscard]] const_iterator end() const { return map_.cend(); }
  /** @getter{const iterator to the beginning, environment} */
  [[nodiscard]] const_iterator cbegin() const { return map_.cbegin(); }
  /** @getter{const iterator to the end, environment} */
  [[nodiscard]] const_iterator cend() const { return map_.cend(); }

  /**
   * Insert a pair (@p key, @p elem) if this environment doesn't contain @p key.
   *
   * Similar to insert function in map,
   * if the key already exists in this environment, then calling insert(key, elem) doesn't change
   * the existing key-value in this environment.
   * @param key key to insert
   * @param elem value to insert
   */
  void insert(const key_type& key, const mapped_type& elem);
  /**
   * Insert a pair (@p key, @p elem) or assign @p elem to the existing key if it exists.
   * @param key key to insert
   * @param elem value to insert
   */
  void insert_or_assign(const key_type& key, const mapped_type& elem);

  /** @checker{empty, environment} */
  [[nodiscard]] bool empty() const { return map_.empty(); }
  /** @getter{number of elements, environment} */
  [[nodiscard]] size_t size() const { return map_.size(); }
  /** @getter{domain, environment} */
  [[nodiscard]] Variables domain() const;

  /**
   * Finds element with specific key.
   * @param key key to find
   * @return iterator to the element with key equivalent to @p key.
   */
  iterator find(const key_type& key) { return map_.find(key); }
  /**
   * Finds element with specific key.
   * @param key key to find
   * @return const_iterator to the element with key equivalent to @p key.
   */
  [[nodiscard]] const_iterator find(const key_type& key) const { return map_.find(key); }

  /**
   * Get a reference to the value that is mapped to a key equivalent to @p key.
   * @param key key of the element to find
   * @return reference to the mapped value of the requested key
   * @throws std::out_of_range if the key does not exist
   */
  [[nodiscard]] const mapped_type& at(const key_type& key) const;

  /**
   * Returns a reference to the value that is mapped to a key equivalent to @p key,
   * performing an insertion if such key does not already exist.
   * @param key key of the element to find or insert
   */
  mapped_type& operator[](const key_type& key);

  /**
   * Returns a constant reference to the value that is mapped to a key equivalent to @p key.
   * @param key key of the element to find
   * @return reference to the mapped value of the requested key
   * @throws std::out_of_range if the key does not exist
   */
  const mapped_type& operator[](const key_type& key) const;

 private:
  map map_;  ///< map between variables and values
};

std::ostream& operator<<(std::ostream& os, const Environment& env);

}  // namespace dlinear::symbolic
