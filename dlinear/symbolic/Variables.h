#pragma once

#include <functional>
#include <initializer_list>
#include <ostream>
#include <set>
#include <string>

#include "dlinear/symbolic/Variable.h"

namespace dlinear::symbolic {

/** Represents a set of variables.
 *
 * This class is based on std::set<Variable>. The intent is to add things that
 * we need including set-union (Variables::insert, operator+, operator+=),
 * set-minus (Variables::erase, operator-, operator-=), and subset/superset
 * checking functions (Variables::IsSubsetOf, Variables::IsSupersetOf,
 * Variables::IsStrictSubsetOf, Variables::IsStrictSupersetOf).
 */
class Variables {
 public:
  using size_type = std::set<Variable>::size_type;
  using iterator = std::set<Variable>::iterator;
  using const_iterator = std::set<Variable>::const_iterator;
  using reverse_iterator = std::set<Variable>::reverse_iterator;
  using const_reverse_iterator = std::set<Variable>::const_reverse_iterator;

  Variables() = default;
  Variables(std::initializer_list<Variable> init);
  /**
   * Get the number of variables in the set.
   * @return number of variables in the set.
   */
  [[nodiscard]] size_type size() const { return vars_.size(); }

  /**
   * Check whether the set is empty.
   * @return true if the set is empty
   * @return false if the set is not empty
   */
  [[nodiscard]] bool empty() const { return vars_.empty(); }

  /** Implements the @ref hash_append concept. */
  void hash(InvocableHashAlgorithm auto& hasher) const noexcept { hash_append(hasher, vars_); }

  /** Returns an iterator to the beginning. */
  iterator begin() { return vars_.begin(); }
  /** Returns an iterator to the end. */
  iterator end() { return vars_.end(); }
  /** Returns an iterator to the beginning. */
  [[nodiscard]] const_iterator begin() const { return vars_.cbegin(); }
  /** Returns an iterator to the end. */
  [[nodiscard]] const_iterator end() const { return vars_.cend(); }
  /** Returns a const iterator to the beginning. */
  [[nodiscard]] const_iterator cbegin() const { return vars_.cbegin(); }
  /** Returns a const iterator to the end. */
  [[nodiscard]] const_iterator cend() const { return vars_.cend(); }
  /** Returns a reverse iterator to the beginning. */
  reverse_iterator rbegin() { return vars_.rbegin(); }
  /** Returns a reverse iterator to the end. */
  reverse_iterator rend() { return vars_.rend(); }
  /** Returns a reverse iterator to the beginning. */
  [[nodiscard]] const_reverse_iterator rbegin() const { return vars_.crbegin(); }
  /** Returns a reverse iterator to the end. */
  [[nodiscard]] const_reverse_iterator rend() const { return vars_.crend(); }
  /** Returns a const reverse-iterator to the beginning. */
  [[nodiscard]] const_reverse_iterator crbegin() const { return vars_.crbegin(); }
  /** Returns a const reverse-iterator to the end. */
  [[nodiscard]] const_reverse_iterator crend() const { return vars_.crend(); }

  /** Inserts a variable @p var into a set. */
  void insert(const Variable& var) { vars_.insert(var); }
  /** Inserts variables in [@p first, @p last) into a set. */
  template <class InputIt>
  void insert(InputIt first, InputIt last) {
    vars_.insert(first, last);
  }
  /** Inserts variables in @p vars into a set. */
  void insert(const Variables& vars) { vars_.insert(vars.begin(), vars.end()); }

  /** Erases @p key from a set. Return number of erased elements (0 or 1). */
  size_type erase(const Variable& key) { return vars_.erase(key); }

  /** Erases variables in @p vars from a set. Return number of erased
      elements ([0, vars.size()]). */
  size_type erase(const Variables& vars);

  /** Finds element with specific key. */
  iterator find(const Variable& key) { return vars_.find(key); }
  [[nodiscard]] const_iterator find(const Variable& key) const { return vars_.find(key); }

  /** Return true if @p key is included in the Variables. */
  [[nodiscard]] bool include(const Variable& key) const { return find(key) != end(); }

  /** Return true if @p vars is a subset of the Variables. */
  [[nodiscard]] bool IsSubsetOf(const Variables& vars) const;
  /** Return true if @p vars is a superset of the Variables. */
  [[nodiscard]] bool IsSupersetOf(const Variables& vars) const;
  /** Return true if @p vars is a strict subset of the Variables. */
  [[nodiscard]] bool IsStrictSubsetOf(const Variables& vars) const;
  /** Return true if @p vars is a strict superset of the Variables. */
  [[nodiscard]] bool IsStrictSupersetOf(const Variables& vars) const;

  bool operator==(const Variables& vars) const;
  bool operator<(const Variables& vars) const;

  Variables& operator+=(const Variables& vars);
  Variables& operator+=(const Variable& var);

  Variables& operator-=(const Variables& vars);
  Variables& operator-=(const Variable& var);

  Variables operator+(const Variables& vars) const;
  Variables operator+(const Variable& var) const;

  Variables operator-(const Variables& vars) const;
  Variables operator-(const Variable& var) const;

  [[nodiscard]] Variables intersect(const Variables& vars) const;

 private:
  explicit Variables(std::set<Variable> vars);

  std::set<Variable> vars_;  ///< Set of variables
};

Variables operator+(const Variable& var, Variables vars);

std::ostream& operator<<(std::ostream&, const Variables& vars);

}  // namespace dlinear::symbolic

namespace std {
/* Provides std::hash<drake::symbolic::Variables>. */
template <>
struct hash<dlinear::symbolic::Variables> : public dlinear::DefaultHash {};
}  // namespace std
