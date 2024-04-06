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

  /** @constructor{Variables} */
  Variables() = default;
  /**
   * Construct a new Variables object initialized with a list of variables.
   * @param init initializer list of variables
   */
  Variables(std::initializer_list<Variable> init);

  /** @getter{number of variables, set} */
  [[nodiscard]] size_type size() const { return vars_.size(); }
  /** @checker{empty, set} */
  [[nodiscard]] bool empty() const { return vars_.empty(); }
  /** @hash{variables} */
  void hash(InvocableHashAlgorithm auto& hasher) const noexcept { hash_append(hasher, vars_); }
  /** @getter{iterator to the beginning, set} */
  iterator begin() { return vars_.begin(); }
  /** @getter{iterator to the end, set} */
  iterator end() { return vars_.end(); }
  /** @getter{const iterator to the beginning, set} */
  [[nodiscard]] const_iterator begin() const { return vars_.cbegin(); }
  /** @getter{const iterator to the end, set} */
  [[nodiscard]] const_iterator end() const { return vars_.cend(); }
  /** @getter{const iterator to the beginning, set} */
  [[nodiscard]] const_iterator cbegin() const { return vars_.cbegin(); }
  /** @getter{const iterator to the end, set} */
  [[nodiscard]] const_iterator cend() const { return vars_.cend(); }
  /** @getter{reverse iterator to the beginning, set} */
  reverse_iterator rbegin() { return vars_.rbegin(); }
  /** @getter{reverse iterator to the end, set} */
  reverse_iterator rend() { return vars_.rend(); }
  /** @getter{reverse const iterator to the beginning, set} */
  [[nodiscard]] const_reverse_iterator rbegin() const { return vars_.crbegin(); }
  /** @getter{reverse const iterator to the end, set} */
  [[nodiscard]] const_reverse_iterator rend() const { return vars_.crend(); }
  /** @getter{reverse const iterator to the beginning, set} */
  [[nodiscard]] const_reverse_iterator crbegin() const { return vars_.crbegin(); }
  /** @getter{reverse const iterator to the end, set} */
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
  /**
   * Construct a new Variables object from a set of variables.
   * @param vars set of variables
   */
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
