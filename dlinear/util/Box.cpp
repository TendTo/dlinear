/**
 * @file Box.cpp
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Box.h"

#include "dlinear/util/Infinity.h"
#include "dlinear/util/RoundingModeGuard.hpp"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/math.h"

using dlinear::gmp::ceil;
using dlinear::gmp::floor;
using std::equal;
using std::find_if;
using std::make_pair;
using std::make_shared;
using std::numeric_limits;
using std::ostream;
using std::pair;
using std::unordered_map;
using std::vector;

namespace dlinear {

Box::Interval::Interval() : lb_(Infinity::Ninfty()), ub_(Infinity::Infty()) {}

Box::Interval::Interval(const mpq_class &lb, const mpq_class &ub) : lb_(lb), ub_(ub) {
  DLINEAR_ASSERT(lb <= ub, "Interval: lb > ub");
}

Box::Interval::Interval(Interval &&other) noexcept try {
  try {
    lb_.swap(other.lb_);
    ub_.swap(other.ub_);
  } catch (...) {
    DLINEAR_UNREACHABLE();
  }
} catch (...) {
  DLINEAR_UNREACHABLE();
}

std::pair<Box::Interval, Box::Interval> Box::Interval::bisect(const mpq_class &p) const {
  mpq_class midpoint{lb_ + p * (ub_ - lb_)};
  return std::make_pair(Interval(lb_, midpoint), Interval(midpoint, ub_));
}

std::ostream &operator<<(std::ostream &os, const Box::Interval &iv) {
  if (iv.is_empty()) {
    return os << "[ empty ]";
  } else if (iv.lb() <= Infinity::Ninfty() && iv.ub() >= Infinity::Infty()) {
    return os << "[ ENTIRE ]";
  } else {
    os << "[";
    if (iv.lb() <= Infinity::Ninfty()) {
      os << "-inf";
    } else {
      os << iv.lb();
    }
    os << ", ";
    if (iv.ub() >= Infinity::Infty()) {
      os << "inf";
    } else {
      os << iv.ub();
    }
    return os << "]";
  }
}

Box::Interval Box::Interval::fromString(const std::string &s) {
  RoundingModeGuard guard(FE_UPWARD);
  const double ub{stod(s)};
  double lb = s[0] == '-' ? -stod(s.substr(1)) : -stod("-" + s);  // TODO: shouldn't this be -stod(s) or even -ub?
  return Box::Interval{lb, ub};
}

Box::Box()
    : variables_{make_shared<vector<Variable>>()},
      // We have this hack here because it is not allowed to have a
      // zero interval vector. Note that because of this special case,
      // `variables_->size() == values_.size()` do not hold. We should
      // rely on `values_.size()`.
      values_(1),
      var_to_idx_{make_shared<unordered_map<Variable, int, hash_value<Variable>>>()},
      idx_to_var_{make_shared<unordered_map<int, Variable>>()} {}

Box::Box(const vector<Variable> &variables)
    : variables_{make_shared<vector<Variable>>()},
      values_(static_cast<int>(variables.size())),
      var_to_idx_{make_shared<unordered_map<Variable, int, hash_value<Variable>>>()},
      idx_to_var_{make_shared<unordered_map<int, Variable>>()} {
  for (const Variable &var : variables) {
    Add(var);
  }
}

void Box::Add(const Variable &v) {
  if (v.get_type() == Variable::Type::BINARY || v.get_type() == Variable::Type::INTEGER) {
    // QSopt_ex changes
    DLINEAR_RUNTIME_ERROR("Integer variables not supported");
  }

  // Duplicate variables are not allowed.
  DLINEAR_ASSERT(find_if(variables_->begin(), variables_->end(),
                         [&v](const Variable &var) { return v.equal_to(var); }) == variables_->end(),
                 "Duplicate variables are not allowed");

  if (!variables_.unique()) {
    // If the components of this box is shared by more than one
    // entity, we need to clone this before adding the variable `v`
    // so that these changes remain local.
    variables_ = make_shared<vector<Variable>>(*variables_);
    var_to_idx_ = make_shared<unordered_map<Variable, int, hash_value<Variable>>>(*var_to_idx_);
    idx_to_var_ = make_shared<unordered_map<int, Variable>>(*idx_to_var_);
  }
  const int n{size()};
  idx_to_var_->emplace(n, v);
  var_to_idx_->emplace(v, n);
  variables_->push_back(v);
  values_.resize(size());

  // Set up Domain.
  // TODO(soonho): For now, we allow Boolean variables in a box. Change this.
  if (v.get_type() == Variable::Type::BOOLEAN || v.get_type() == Variable::Type::BINARY) {
    values_[n] = Interval(0, 1);
  } else if (v.get_type() == Variable::Type::INTEGER) {
    values_[n] = Interval(-numeric_limits<int>::max(), numeric_limits<int>::max());
  }
}

void Box::Add(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  Add(v);

  DLINEAR_ASSERT(lb <= ub, "Lower bound must be less than or equal to upper bound");

  // Binary variable => lb, ub ∈ [0, 1].
  DLINEAR_ASSERT(v.get_type() != Variable::Type::BINARY || (0.0 <= lb && ub <= 1.0),
                 "Binary variable must be in [0, 1]");

  // Integer variable => lb, ub ∈ Z.
  DLINEAR_ASSERT(v.get_type() != Variable::Type::INTEGER || (is_integer(lb) && is_integer(ub)),
                 "Integer variable must be in Z");

  values_[(*var_to_idx_)[v]] = Interval{lb, ub};
}

bool Box::empty() const { return values_[0].is_empty(); }

void Box::set_empty() {
  for (Interval &iv : values_) {
    iv.set_empty();
  }
}

int Box::size() const { return variables_->size(); }

Box::Interval &Box::operator[](const int i) {
  DLINEAR_ASSERT(i < size(), "Index out of bound");
  return values_[i];
}
Box::Interval &Box::operator[](const Variable &var) { return values_[(*var_to_idx_)[var]]; }
const Box::Interval &Box::operator[](const int i) const {
  DLINEAR_ASSERT(i < size(), "Index out of bound");
  return values_[i];
}
const Box::Interval &Box::operator[](const Variable &var) const { return values_[(*var_to_idx_)[var]]; }

const vector<Variable> &Box::variables() const { return *variables_; }

const Variable &Box::variable(const int i) const { return (*idx_to_var_)[i]; }

bool Box::has_variable(const Variable &var) const { return var_to_idx_->count(var) > 0; }

int Box::index(const Variable &var) const { return (*var_to_idx_)[var]; }

const std::vector<Box::Interval> &Box::interval_vector() const { return values_; }
std::vector<Box::Interval> &Box::mutable_interval_vector() { return values_; }

pair<mpq_class, int> Box::MaxDiam() const {
  mpq_class max_diam{0.0};
  int idx{-1};
  for (size_t i{0}; i < variables_->size(); ++i) {
    const mpq_class &diam_i{values_[i].diam()};
    if (diam_i > max_diam && values_[i].is_bisectable()) {
      max_diam = diam_i;
      idx = i;
    }
  }
  return make_pair(max_diam, idx);
}

pair<Box, Box> Box::bisect(const int i) const {
  const Variable &var{(*idx_to_var_)[i]};
  if (!values_[i].is_bisectable()) {
    DLINEAR_RUNTIME_ERROR_FMT("Variable {} = {} is not bisectable but Box::bisect is called.", var, values_[i]);
  }
  switch (var.get_type()) {
    case Variable::Type::CONTINUOUS:
      return bisect_continuous(i);
    case Variable::Type::INTEGER:
    case Variable::Type::BINARY:
      return bisect_int(i);
    case Variable::Type::BOOLEAN:
      DLINEAR_UNREACHABLE();
  }
  DLINEAR_UNREACHABLE();
}

pair<Box, Box> Box::bisect(const Variable &var) const {
  auto it = var_to_idx_->find(var);
  if (it != var_to_idx_->end()) {
    return bisect(it->second);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Variable {} is not found in this box.", var);
  }
  return bisect((*var_to_idx_)[var]);
}

pair<Box, Box> Box::bisect_int(const int i) const {
  DLINEAR_ASSERT(idx_to_var_->at(i).get_type() == Variable::Type::INTEGER ||
                     idx_to_var_->at(i).get_type() == Variable::Type::BINARY,
                 "Variable must be integer or binary");
  const Interval &intv_i{values_[i]};
  const mpz_class &lb{ceil(intv_i.lb())};
  const mpz_class &ub{floor(intv_i.ub())};
  const mpq_class &mid{intv_i.mid()};
  const mpz_class &mid_floor{floor(mid)};
  DLINEAR_ASSERT(intv_i.lb() <= lb, "intv_i lower bound must be less than or equal to lower bound");
  DLINEAR_ASSERT(lb <= mid_floor, "lower bound must be less than or equal to mid_floor");
  DLINEAR_ASSERT(mid_floor + 1 <= ub, "mid_floor + 1 must be less than or equal to upper bound");
  DLINEAR_ASSERT(ub <= intv_i.ub(), "upper bound must be less than or equal to intv_i upper bound");

  Box b1{*this};
  Box b2{*this};
  b1[i] = Interval(lb, mid_floor);
  b2[i] = Interval(mid_floor + 1, ub);
  return make_pair(b1, b2);
}

pair<Box, Box> Box::bisect_continuous(const int i) const {
  DLINEAR_ASSERT(idx_to_var_->at(i).get_type() == Variable::Type::CONTINUOUS, "Variable must be continuous");
  Box b1{*this};
  Box b2{*this};
  const Interval intv_i{values_[i]};
  constexpr double kHalf{0.5};
  const pair<Interval, Interval> bisected_intervals{intv_i.bisect(kHalf)};
  b1[i] = bisected_intervals.first;
  b2[i] = bisected_intervals.second;
  return make_pair(b1, b2);
}

#if 0
Box& Box::InplaceUnion(const Box& b) {
  // Checks variables() == b.variables().
  DLINEAR_ASSERT(equal(variables().begin(), variables().end(),
                     b.variables().begin(), b.variables().end(),
                     std::equal_to<Variable>{}));
  values_ |= b.values_;
  return *this;
}
#endif

namespace {
// RAII which preserves the FmtFlags of an ostream.
class IosFmtFlagSaver {
 public:
  explicit IosFmtFlagSaver(ostream &os) : os_(os), flags_(os.flags()) {}
  ~IosFmtFlagSaver() { os_.flags(flags_); }

  IosFmtFlagSaver(const IosFmtFlagSaver &rhs) = delete;
  IosFmtFlagSaver(IosFmtFlagSaver &&rhs) = delete;
  IosFmtFlagSaver &operator=(const IosFmtFlagSaver &rhs) = delete;
  IosFmtFlagSaver &operator=(IosFmtFlagSaver &&rhs) = delete;

 private:
  ostream &os_;
  std::ios::fmtflags flags_;
};
}  // namespace

ostream &operator<<(ostream &os, const Box &box) {
  IosFmtFlagSaver saver{os};
  int i{0};
  for (const Variable &var : *(box.variables_)) {
    const Box::Interval interval{box.values_[i++]};
    os << var << " : ";
    switch (var.get_type()) {
      case Variable::Type::INTEGER:
      case Variable::Type::BINARY:
      case Variable::Type::CONTINUOUS:
        os << interval;
        break;
      case Variable::Type::BOOLEAN:
        if (interval.ub() == 0.0)
          os << "False";
        else if (interval.lb() == 1.0)
          os << "True";
        else
          os << "Unassigned";
        break;
    }
    if (i != box.size()) os << "\n";
  }
  return os;
}

bool operator==(const Box &b1, const Box &b2) {
  return equal(b1.variables().begin(), b1.variables().end(), b2.variables().begin(), b2.variables().end(),
               std::equal_to<Variable>{}) &&
         (b1.interval_vector() == b2.interval_vector());
}

bool operator!=(const Box &b1, const Box &b2) { return !(b1 == b2); }

ostream &DisplayDiff(ostream &os, const vector<Variable> &variables, const std::vector<Box::Interval> &old_iv,
                     const std::vector<Box::Interval> &new_iv) {
  IosFmtFlagSaver saver{os};
  for (size_t i = 0; i < variables.size(); ++i) {
    const Box::Interval &old_i{old_iv[i]};
    const Box::Interval &new_i{new_iv[i]};
    if (old_i != new_i) os << variables[i] << " : " << old_i << " -> " << new_i << "\n";
  }
  return os;
}

}  // namespace dlinear
