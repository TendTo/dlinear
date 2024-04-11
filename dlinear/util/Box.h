/**
 * @file Box.h
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 */
#pragma once

#include <functional>
#include <limits>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/logging.h"

namespace dlinear {

class Box {
 public:
  class Interval {
   public:
    /**
     * Constructs an interval from a string.
     * @code
     * Box::Interval::fromString("100"); // [-100, 100]
     * @endcode
     * @param s value used to construct the interval
     * @return newly constructed interval
     */
    static Interval fromString(const std::string &s);
    Interval();
    Interval(Interval &&other) noexcept;
    Interval(const Interval &other) : lb_(other.lb_), ub_(other.ub_) {}
    explicit Interval(const mpq_class &val) : lb_(val), ub_(val) {}
    Interval(const mpq_class &lb, const mpq_class &ub);
    [[nodiscard]] bool is_empty() const { return lb_ == 1 && ub_ == 0; }
    [[nodiscard]] bool is_degenerated() const { return lb_ == ub_; }
    [[nodiscard]] bool is_bisectable() const { return lb_ < ub_; }
    [[nodiscard]] const mpq_class &lb() const { return lb_; }
    [[nodiscard]] const mpq_class &ub() const { return ub_; }
    [[nodiscard]] mpq_class mid() const { return (lb_ + ub_) / 2; }
    [[nodiscard]] mpq_class diam() const { return is_empty() ? mpq_class(0) : mpq_class(ub_ - lb_); }
    [[nodiscard]] std::pair<Interval, Interval> bisect(const mpq_class &p) const;
    bool operator==(const Interval &other) const { return lb_ == other.lb_ && ub_ == other.ub_; }
    bool operator!=(const Interval &other) const { return lb_ != other.lb_ || ub_ != other.ub_; }
    Interval &operator=(const mpq_t &val) {
      mpq_set(lb_.get_mpq_t(), val);
      mpq_set(ub_.get_mpq_t(), val);
      return *this;
    }
    Interval &operator=(const mpq_class &val) {
      lb_ = ub_ = val;
      return *this;
    }
    Interval &operator=(const Interval &other) = default;
    // Mutators
    void set_empty() {
      lb_ = 1;
      ub_ = 0;
    }
    friend std::ostream &operator<<(std::ostream &os, const Interval &iv);

   private:
    mpq_class lb_, ub_;
  };

  /** Constructs an empty box. */
  Box();

  /**
   * Construct a box from @p variables.
   * @param variables variables contained in the box
   */
  explicit Box(const std::vector<Variable> &variables);

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
   * Check if the box is empty.
   * @return true if the box is empty
   * @return false if the box is not empty
   * @see set_empty
   */
  [[nodiscard]] bool empty() const;

  /**
   * Set the box to be empty.
   * @see empty
   */
  void set_empty();

  /**
   * Return the number of variables in the box.
   * @return number of variables in the box
   */
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

  /**
   * Return the variables in the box.
   * @return vector of variables in the box
   */
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

  /// Update the current box by taking union with @p b.
  ///
  /// @pre variables() == b.variables().
  // Box& InplaceUnion(const Box& b);

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

  std::shared_ptr<std::vector<Variable>> variables_;                                     ///< Variables in the box
  std::vector<Interval> values_;                                                         ///< Interval vector of the box
  std::shared_ptr<std::unordered_map<Variable, int, hash_value<Variable>>> var_to_idx_;  ///< Variable to index map
  std::shared_ptr<std::unordered_map<int, Variable>> idx_to_var_;                        ///< Index to variable map

  friend std::ostream &operator<<(std::ostream &os, const Box &box);
};

std::ostream &operator<<(std::ostream &os, const Box::Interval &iv);

std::ostream &operator<<(std::ostream &os, const Box &box);

bool operator==(const Box &b1, const Box &b2);

bool operator!=(const Box &b1, const Box &b2);

std::ostream &DisplayDiff(std::ostream &os, const std::vector<Variable> &variables,
                          const std::vector<Box::Interval> &old_iv, const std::vector<Box::Interval> &new_iv);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Box)
OSTREAM_FORMATTER(dlinear::Box::Interval)
