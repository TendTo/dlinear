/**
 * @file Box.h
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 */
#pragma once

#include <iosfwd>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"  // IWYU pragma: keep for hash_value
#include "dlinear/util/Config.h"
#include "dlinear/util/Interval.h"
#include "dlinear/util/logging.h"

namespace dlinear {

class Box {
 public:
  /** Constructs an empty box. */
  explicit Box(Config::LPSolver lp_solver);

  /**
   * Construct a box from @p variables.
   * @param variables variables contained in the box
   */
  explicit Box(const std::vector<Variable> &variables, Config::LPSolver lp_solver);

  /**
   * Add the variable @p v to the box.
   * @param v variable to add
   */
  void Add(const Variable &v);

  /**
   * Add the variable @p v to the box and sets its domain using @p lb and @p ub.
   * @param v variable to add
   * @param lb lower bound
   * @param ub upper bound
   */
  void Add(const Variable &v, const mpq_class &lb, const mpq_class &ub);

  /**
   * @checker{empty, box}
   * @see set_empty
   */
  [[nodiscard]] bool empty() const;

  /**
   * Set the box to be empty.
   * @see empty
   */
  void set_empty();

  /** @getter{number of variables, box} */
  [[nodiscard]] int size() const;

  /**
   * Return the interval at index @p i.
   * @param i index of the interval
   * @return interval at index @p i
   */
  Interval &operator[](int i);

  /**
   * Return the interval associated with @p var.
   * @param var variable to get the interval from
   * @return interval associated with @p var
   */
  Interval &operator[](const Variable &var);

  /**
   * Return the interval at index @p i.
   * @param i index of the interval
   * @return interval at index @p i
   */
  const Interval &operator[](int i) const;

  /**
   * Return the interval associated with @p var.
   * @param var variable to get the interval from
   * @return interval associated with @p var
   */
  const Interval &operator[](const Variable &var) const;

  /** @getter{lower bound negative infinity, box} */
  [[nodiscard]] const mpq_class &ninfinity() const { return ninfinity_; }
  /** @getter{upper bound infinity, box} */
  [[nodiscard]] const mpq_class &infinity() const { return infinity_; }
  /** @getter{variables, box} */
  [[nodiscard]] const std::vector<Variable> &variables() const;

  /**
   * Return the @p i -th variable in the box.
   * @param i index of the variable
   * @return variable at index @p i
   */
  [[nodiscard]] const Variable &variable(int i) const;

  /**
   * Checks if this box contains @p var.
   * @param var variable to check the presence of
   * @return true if the box contains @p var
   * @return false if the box does not contain @p var
   */
  [[nodiscard]] bool has_variable(const Variable &var) const;

  /**
   * Return the interval vector of the box.
   * @return interval vector of the box
   */
  [[nodiscard]] const std::vector<Interval> &interval_vector() const;

  /**
   * Return the interval vector of the box.
   * @return interval vector of the box
   */
  std::vector<Interval> &m_interval_vector();

  /**
   * Return the index associated with @p var.
   * @param var variable to get the index from
   * @return index associated with @p var
   */
  [[nodiscard]] int index(const Variable &var) const;

  /**
   * Return the max diameter of the box and the associated index.
   * @return max diameter of the box and the associated index
   */
  [[nodiscard]] std::pair<mpq_class, int> MaxDiam() const;

  /**
   * Bisect the box at @p i -th dimension.
   * @param i dimension to bisect
   * @return pair of boxes resulting from the bisection
   * @throw std::runtime if @p i -th dimension is not bisectable
   */
  [[nodiscard]] std::pair<Box, Box> bisect(int i) const;

  /**
   * Bisect the box at @p var.
   * @param var variable to bisect
   * @return pair of boxes resulting from the bisection
   * @throw std::runtime if @p var is not bisectable
   */
  [[nodiscard]] std::pair<Box, Box> bisect(const Variable &var) const;

 private:
  /**
   * Bisects the box at @p i -th dimension.
   * @pre @p i-th variable is bisectable.
   * @pre @p i-th variable is of integer type.
   * @param i index of the dimension to bisect
   * @return pair of boxes resulting from the bisection
   */
  [[nodiscard]] std::pair<Box, Box> bisect_int(int i) const;

  /**
   * Bisects the box at @p i -th dimension.
   * @pre @p i-th variable is bisectable.
   * @pre @p i-th variable is of continuous type.
   * @param i index of the dimension to bisect
   * @return pair of boxes resulting from the bisection
   */
  [[nodiscard]] std::pair<Box, Box> bisect_continuous(int i) const;

  mpq_class ninfinity_;                                                                  ///< Lower bound of the box
  mpq_class infinity_;                                                                   ///< Upper bound of the box
  std::vector<Interval> values_;                                                         ///< Interval vector of the box
  std::shared_ptr<std::vector<Variable>> variables_;                                     ///< Variables in the box
  std::shared_ptr<std::unordered_map<Variable, int, hash_value<Variable>>> var_to_idx_;  ///< Variable to index map
  std::shared_ptr<std::unordered_map<int, Variable>> idx_to_var_;                        ///< Index to variable map

  friend std::ostream &operator<<(std::ostream &os, const Box &box);
};

std::ostream &operator<<(std::ostream &os, const Box &box);

bool operator==(const Box &b1, const Box &b2);

bool operator!=(const Box &b1, const Box &b2);

std::ostream &DisplayDiff(std::ostream &os, const std::vector<Variable> &variables, const std::vector<Interval> &old_iv,
                          const std::vector<Interval> &new_iv);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Box)
