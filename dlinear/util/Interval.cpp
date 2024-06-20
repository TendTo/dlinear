#include "Interval.h"

#include "dlinear/util/RoundingModeGuard.hpp"

namespace dlinear {

mpq_class Interval::infinity{-1};
mpq_class Interval::ninfinity{0};

Interval::Interval(const mpq_class &lb, const mpq_class &ub) : lb_(lb), ub_(ub) {
  DLINEAR_ASSERT(lb <= ub, "Interval: lb > ub");
}

std::pair<Interval, Interval> Interval::bisect(const mpq_class &p) const {
  mpq_class midpoint{lb_ + p * (ub_ - lb_)};
  return std::make_pair(Interval(lb_, midpoint), Interval(midpoint, ub_));
}

Interval &Interval::operator+=(const Interval &o) {
  lb_ += o.lb_;
  ub_ += o.ub_;
  return *this;
}
Interval &Interval::operator-=(const Interval &o) {
  lb_ -= o.ub_;
  ub_ -= o.lb_;
  return *this;
}
Interval &Interval::operator*=(const Interval &o) {
  const std::initializer_list<mpq_class> products{lb_ * o.lb_, lb_ * o.ub_, ub_ * o.lb_, ub_ * o.ub_};
  const mpq_class lb{std::min(products)};
  const mpq_class ub{std::max(products)};
  lb_ = lb;
  ub_ = ub;
  return *this;
}
Interval &Interval::operator/=(const Interval &o) {
  if (o.is_degenerated() && o.lb() == 0) DLINEAR_RUNTIME_ERROR("Division by zero");

  const std::initializer_list<mpq_class> quotients{lb_ / o.lb_, lb_ / o.ub_, ub_ / o.lb_, ub_ / o.ub_};
  const mpq_class lb{std::min(quotients)};
  const mpq_class ub{std::max(quotients)};
  lb_ = lb;
  ub_ = ub;
  return *this;
}
Interval &Interval::operator+=(const mpq_class &o) {
  lb_ += o;
  ub_ += o;
  return *this;
}
Interval &Interval::operator-=(const mpq_class &o) {
  lb_ -= o;
  ub_ -= o;
  return *this;
}
Interval &Interval::operator*=(const mpq_class &o) {
  const std::initializer_list<mpq_class> products{lb_ * o, lb_ * o, ub_ * o, ub_ * o};
  const mpq_class lb{std::min(products)};
  const mpq_class ub{std::max(products)};
  lb_ = lb;
  ub_ = ub;
  return *this;
}
Interval &Interval::operator/=(const mpq_class &o) {
  if (o == 0) DLINEAR_RUNTIME_ERROR("Division by zero");

  const std::initializer_list<mpq_class> quotients{lb_ / o, lb_ / o, ub_ / o, ub_ / o};
  const mpq_class lb{std::min(quotients)};
  const mpq_class ub{std::max(quotients)};
  lb_ = lb;
  ub_ = ub;
  return *this;
}

std::ostream &operator<<(std::ostream &os, const Interval &iv) {
  const bool inverted = Interval::infinity < Interval::ninfinity;
  if (iv.is_empty()) return os << "[ empty ]";
  if (!inverted && iv.lb() <= Interval::ninfinity && iv.ub() >= Interval::infinity) return os << "[ ENTIRE ]";

  os << "[";
  if (!inverted && iv.lb() <= Interval::ninfinity) {
    os << "-inf";
  } else {
    os << iv.lb();
  }
  os << ", ";
  if (!inverted && iv.ub() >= Interval::infinity) {
    os << "inf";
  } else {
    os << iv.ub();
  }
  return os << "]";
}

Interval Interval::fromString(const std::string &s) {
  RoundingModeGuard guard(FE_UPWARD);
  const double ub{stod(s)};
  double lb = s[0] == '-' ? -stod(s.substr(1)) : -stod("-" + s);  // TODO: shouldn't this be -stod(s) or even -ub?
  return Interval{lb, ub};
}

}  // namespace dlinear