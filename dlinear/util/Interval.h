/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Interval class.
 *
 * An interval assigned to a variable describes the range of values it can assume.
 */
#pragma once

#include <iosfwd>
#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/definitions.h"

namespace dlinear {

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
  explicit Interval(const mpq_class &val) : lb_(val), ub_(val) {}
  Interval(const mpq_class &lb, const mpq_class &ub);
  Interval(const Interval &other) = default;
  Interval(Interval &&other) noexcept = default;
  Interval &operator=(const Interval &other) = default;
  Interval &operator=(Interval &&other) noexcept = default;
  [[nodiscard]] bool is_empty() const { return lb_ == 1 && ub_ == 0; }
  [[nodiscard]] bool is_degenerated() const { return lb_ == ub_; }
  [[nodiscard]] bool is_bisectable() const { return lb_ < ub_; }
  [[nodiscard]] const mpq_class &lb() const { return lb_; }
  [[nodiscard]] const mpq_class &ub() const { return ub_; }
  [[nodiscard]] mpq_class mid() const { return (lb_ + ub_) / 2; }
  [[nodiscard]] mpq_class diam() const { return is_empty() ? mpq_class(0) : mpq_class(ub_ - lb_); }
  [[nodiscard]] std::pair<Interval, Interval> bisect(const mpq_class &p) const;

  bool operator==(const Interval &other) const { return lb_ == other.lb_ && ub_ == other.ub_; }
  Interval &operator=(const mpq_t &val) {
    mpq_set(lb_.get_mpq_t(), val);
    mpq_set(ub_.get_mpq_t(), val);
    return *this;
  }
  Interval &operator=(const mpq_class &val) {
    lb_ = ub_ = val;
    return *this;
  }

  void set_empty() {
    lb_ = 1;
    ub_ = 0;
  }

  ARITHMETIC_OPERATORS(Interval)
  GENERIC_ARITHMETIC_OPERATORS(Interval, mpq_class &)

  std::ostream &printToStream(std::ostream &os, const mpq_class &ninfinity, const mpq_class &infinity) const;

 private:
  mpq_class lb_, ub_;
};

std::ostream &operator<<(std::ostream &os, const Interval &iv);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Interval);

#endif
