/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "BoundVector.h"

#include <algorithm>
#include <ostream>
#include <utility>

#include "dlinear/util/exception.h"

#define TRACE_VIOLATED_BOUNDS(it)                                                                                    \
  DLINEAR_TRACE_FMT("BoundVector::ViolatedBounds: ({} {}) incompatible with ({} {})", value, lp_bound, *(it)->value, \
                    (it)->lp_bound)

namespace dlinear {

#define FindLowerBoundValue(value_ptr) bounds_.lower_bound({value_ptr, LpColBound::L, {}})
#define FindLowerBound(value_ptr, bound) bounds_.lower_bound({value_ptr, bound, {}})
#define FindUpperBoundValue(value_ptr) bounds_.upper_bound({value_ptr, LpColBound::U, {}})
#define FindUpperBound(value_ptr, bound) bounds_.upper_bound({value_ptr, bound, {}})
#define FindLowerNqBoundValue(value_ptr) nq_bounds_.lower_bound({value_ptr, LpColBound::D, {}})
#define FindUpperNqBoundValue(value_ptr) nq_bounds_.upper_bound({value_ptr, LpColBound::D, {}})

BoundVector::BoundVector(const mpq_class& inf_l, const mpq_class& inf_u)
    : n_lower_bounds_{0},
      bounds_{},
      nq_bounds_{},
      inf_l_{&inf_l},
      inf_u_{&inf_u},
      active_lower_bound_{inf_l_},
      active_upper_bound_{inf_u_} {}

BoundIterator BoundVector::AddBound(const Bound& bound) {
  return AddBound(*bound.value, bound.lp_bound, bound.theory_literal, bound.explanation);
}
BoundIterator BoundVector::AddBound(const mpq_class& value, LpColBound lp_bound, const Literal& theory_lit,
                                    const LiteralSet& explanation) {
  DLINEAR_ASSERT_FMT(lp_bound == LpColBound::L || lp_bound == LpColBound::U || lp_bound == LpColBound::B ||
                         lp_bound == LpColBound::SL || lp_bound == LpColBound::SU || lp_bound == LpColBound::D,
                     "Valid must be L, U, B, SL, SU or D. Received: {}", lp_bound);
  const BoundIterator violation{ViolatedBounds(value, lp_bound)};
  if (!violation.empty()) return violation;

  // Add the new lp_bound
  auto it = bounds_.end();
  switch (lp_bound) {
    case LpColBound::SL:
    case LpColBound::L:
      ++n_lower_bounds_;
      it = bounds_.emplace(&value, lp_bound, theory_lit, explanation);
      break;
    case LpColBound::SU:
    case LpColBound::U:
      it = bounds_.emplace(false, &value, lp_bound, theory_lit, explanation);
      break;
    case LpColBound::B:
      // Check if adding this lp_bound will cause a violation
      if (ViolatedNqBounds(value, value))
        return {bounds_.cend(), bounds_.cend(), FindLowerNqBoundValue(&value), FindUpperNqBoundValue(&value)};
      ++n_lower_bounds_;
      active_lower_bound_ = active_upper_bound_ = &value;
      bounds_.emplace(false, &value, LpColBound::L, theory_lit, explanation);
      bounds_.emplace(&value, LpColBound::U, theory_lit, explanation);
      return {};
    case LpColBound::D:
      if (IsActiveEquality(value)) return {FindLowerBoundValue(&value), FindUpperBoundValue(&value)};
      nq_bounds_.emplace(&value, lp_bound, theory_lit, explanation);
      return {};
    default:
      break;
  }

  bool changed_active_bounds = false;
  const mpq_class* backup_active_lower_bound = active_lower_bound_;
  const mpq_class* backup_active_upper_bound = active_upper_bound_;
  // Check if there has been a change in the active bounds
  if ((lp_bound == LpColBound::L || lp_bound == LpColBound::SL) && value > *active_lower_bound_) {
    active_lower_bound_ = &value;
    changed_active_bounds = true;
  } else if ((lp_bound == LpColBound::U || lp_bound == LpColBound::SU) && value < *active_upper_bound_) {
    active_upper_bound_ = &value;
    changed_active_bounds = true;
  }

  if (changed_active_bounds) {
    if (ViolatedNqBounds()) {
      bounds_.erase(it);
      if (lp_bound == LpColBound::L || lp_bound == LpColBound::SL) --n_lower_bounds_;
      const BoundIterator nq_violation{
          FindLowerBoundValue(active_lower_bound_), FindUpperBoundValue(active_upper_bound_),
          FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
      active_lower_bound_ = backup_active_lower_bound;
      active_upper_bound_ = backup_active_upper_bound;
      return nq_violation;
    }
  }

  return {};
}
bool BoundVector::RemoveBound(const mpq_class& value, const LpColBound lp_bound, const Literal& theory_literal,
                              const LiteralSet& explanation) {
  return RemoveBound({&value, lp_bound, theory_literal, explanation});
}
bool BoundVector::RemoveBound(const Bound& bound) {
  if (bound.lp_bound == LpColBound::D) {
    for (auto it = nq_bounds_.find(bound); it != nq_bounds_.end() && *it->value == *bound.value; ++it) {
      if (it->theory_literal == bound.theory_literal && it->explanation == bound.explanation) {
        return nq_bounds_.erase(it);
      }
    }
    return false;
  }
  if (bound.lp_bound == LpColBound::B) {
    // Modify the bound temporarily to avoid pointless copies
    Bound& modified_bound = const_cast<Bound&>(bound);
    modified_bound.lp_bound = LpColBound::L;
    const bool l_res = RemoveBound(modified_bound);
    modified_bound.lp_bound = LpColBound::U;
    const bool u_res = RemoveBound(modified_bound);
    // Restore the original lp_bound value
    modified_bound.lp_bound = LpColBound::B;
    return l_res || u_res;
  }

  bool res = false;
  for (auto it = FindLowerBound(bound.value, bound.lp_bound);
       it != bounds_.cend() && *it->value == *bound.value && it->lp_bound == bound.lp_bound; ++it) {
    if (it->theory_literal == bound.theory_literal && it->explanation == bound.explanation) {
      res = bounds_.erase(it);
      DLINEAR_ASSERT(res, "Bound must be removed");
      break;
    }
  }
  if (!res) return res;
  if (bound.lp_bound == LpColBound::L || bound.lp_bound == LpColBound::SL) {
    --n_lower_bounds_;
    active_lower_bound_ = n_lower_bounds_ == 0 ? inf_l_ : bounds_[n_lower_bounds_ - 1].value;
  } else {
    DLINEAR_ASSERT(bound.lp_bound == LpColBound::U || bound.lp_bound == LpColBound::SU, "Invalid bound");
    active_upper_bound_ = bounds_.size() == n_lower_bounds_ ? inf_u_ : bounds_[n_lower_bounds_].value;
  }
  return res;
}
BoundIterator BoundVector::ViolatedBounds(const mpq_class& value, LpColBound lp_bound) const {
  if (lp_bound == LpColBound::D) return {};
  DLINEAR_ASSERT_FMT(lp_bound == LpColBound::L || lp_bound == LpColBound::U || lp_bound == LpColBound::B ||
                         lp_bound == LpColBound::SL || lp_bound == LpColBound::SU,
                     "Valid must be L, U, B, SL or SU. Received: {}", lp_bound);

  DLINEAR_TRACE_FMT("BoundVector::ViolatedBounds: checking ({} {})", value, lp_bound);
  Bounds::const_iterator it;

  switch (lp_bound) {
    case LpColBound::SL:
    case LpColBound::L:
      if (value > *active_upper_bound_) return {LowerBoundEnd(), FindUpperBound(&value, !lp_bound)};
      it = bounds_.upper_bound({&value, lp_bound, {}});
      if (it == bounds_.cend() || *it->value != value) return {};
      if (lp_bound == LpColBound::L && it->lp_bound != LpColBound::SU) return {};
      TRACE_VIOLATED_BOUNDS(it);
      DLINEAR_ASSERT(LowerBoundEnd() < FindUpperBound(&value, !lp_bound), "Bounds must not be inverted");
      return {LowerBoundEnd(), FindUpperBound(&value, !lp_bound)};
    case LpColBound::SU:
    case LpColBound::U:
      if (value < *active_lower_bound_) return {FindLowerBound(&value, !lp_bound), LowerBoundEnd()};
      it = bounds_.lower_bound({&value, lp_bound, {}});
      if (it == bounds_.cbegin() || *(std::prev(it))->value != value) return {};
      if (lp_bound == LpColBound::U && (std::prev(it))->lp_bound != LpColBound::SL) return {};
      TRACE_VIOLATED_BOUNDS((std::prev(it)));
      DLINEAR_ASSERT(FindLowerBound(&value, !lp_bound) < LowerBoundEnd(), "Bounds must not be inverted");
      return {FindLowerBound(&value, !lp_bound), LowerBoundEnd()};
    case LpColBound::B:
      if (value < *active_lower_bound_) return {FindLowerBound(&value, LpColBound::SL), LowerBoundEnd()};
      if (value > *active_upper_bound_) return {LowerBoundEnd(), FindUpperBound(&value, LpColBound::SU)};
      it = bounds_.upper_bound({&value, LpColBound::L, {}});
      if ((it != bounds_.cend() && *it->value == value && it->lp_bound == LpColBound::SU)) {
        TRACE_VIOLATED_BOUNDS(it);
        DLINEAR_ASSERT(LowerBoundEnd() < FindUpperBound(&value, LpColBound::SU), "Bounds must not be inverted");
        return {LowerBoundEnd(), FindUpperBound(&value, LpColBound::SU)};
      }
      it = bounds_.lower_bound({&value, LpColBound::U, {}});
      if ((it != bounds_.cbegin() && *(std::prev(it))->value == value && (std::prev(it))->lp_bound == LpColBound::SL)) {
        TRACE_VIOLATED_BOUNDS(std::prev(it));
        DLINEAR_ASSERT(FindLowerBound(&value, LpColBound::SL) < LowerBoundEnd(), "Bounds must not be inverted");
        return {FindLowerBound(&value, LpColBound::SL), LowerBoundEnd()};
      }
      return {};
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool BoundVector::ViolatedNqBounds() const {
  if (active_upper_bound_ != active_lower_bound_) return false;
  // The active bounds are equal, verify whether they are violated
  auto nq_value_it = nq_bounds_.find({active_upper_bound_, LpColBound::D, {}});
  // No violation, return
  if (nq_value_it == nq_bounds_.end()) return false;
  // Violated strict bound, remove the last added bound and return the interval
  return true;
}

bool BoundVector::ViolatedNqBounds(const mpq_class& lb, const mpq_class& ub) const {
  if (lb != ub) return false;
  // The active bounds are equal, verify whether they are violated
  auto nq_value_it = nq_bounds_.find({&lb, LpColBound::D, {}});
  // No violation, return
  if (nq_value_it == nq_bounds_.end()) return false;
  // Violated strict bound, remove the last added bound and return the interval
  return true;
}

void BoundVector::Clear() {
  bounds_.clear();
  n_lower_bounds_ = 0;
  nq_bounds_.clear();
  active_lower_bound_ = inf_l_;
  active_upper_bound_ = inf_u_;
}

bool BoundVector::IsActiveEquality(const mpq_class& value) const {
  if (n_lower_bounds_ == 0 || n_lower_bounds_ == bounds_.size()) return false;
  return *active_upper_bound_ == *active_lower_bound_ && *active_upper_bound_ == value;
}

bool BoundVector::IsLowerBound(const mpq_class& value) const {
  auto it = bounds_.find({&value, LpColBound::L, {}});
  if (it != bounds_.cend()) return true;
  it = bounds_.find({&value, LpColBound::SL, {}});
  return it != bounds_.cend();
}

bool BoundVector::IsUpperBound(const mpq_class& value) const {
  auto it = bounds_.find({&value, LpColBound::U, {}});
  if (it != bounds_.cend()) return true;
  it = bounds_.find({&value, LpColBound::SU, {}});
  return it != bounds_.cend();
}

bool BoundVector::IsLowerBounded() const {
  if (active_lower_bound_ == inf_l_ || bounds_.empty() || n_lower_bounds_ == 0) return false;
  return *active_lower_bound_ > *inf_l_;
}

bool BoundVector::IsUpperBounded() const {
  if (active_upper_bound_ == inf_u_ || bounds_.empty() || n_lower_bounds_ == bounds_.size()) return false;
  return *active_upper_bound_ < *inf_u_;
}

bool BoundVector::IsBounded() const { return IsLowerBounded() && IsUpperBounded(); }

BoundVector::Bounds::const_iterator BoundVector::LowerBoundEnd() const {
  return bounds_.cbegin() + static_cast<int>(n_lower_bounds_);
}

BoundIterator BoundVector::GetActiveBound() const { return GetActiveBound(*active_lower_bound_, *active_upper_bound_); }
BoundIterator BoundVector::GetActiveBound(const mpq_class& value) const { return GetActiveBound(value, value); }
BoundIterator BoundVector::GetActiveBound(const mpq_class& lb, const mpq_class& ub) const {
  DLINEAR_ASSERT(lb == ub || (lb == *active_lower_bound_ && ub == *active_upper_bound_), "Bounds must be == or active");
  DLINEAR_ASSERT(lb <= ub, "Lower bound must be less or equal to upper bound");
  auto lb_it = FindUpperBound(&lb, LpColBound::SL);
  auto ub_it = FindLowerBound(&ub, LpColBound::SU);
  // Adjust the iterators based on the state of the vector
  if (lb_it != bounds_.cbegin() && lb == *(std::prev(lb_it))->value) lb_it--;
  if (ub_it != bounds_.cend() && ub == *ub_it->value) ub_it++;
  return BoundIterator{
      lb_it, ub_it,  // The non-equal bounds become inclusive if there is no normal bounds
      lb_it == ub_it || lb_it->lp_bound != LpColBound::SL ? FindLowerNqBoundValue(&lb) : FindUpperNqBoundValue(&lb),
      lb_it == ub_it || (std::prev(ub_it))->lp_bound != LpColBound::SU ? FindUpperNqBoundValue(&ub)
                                                                       : FindLowerNqBoundValue(&ub)};
}

BoundIterator BoundVector::GetActiveBounds() const {
  return GetActiveBounds(*active_lower_bound_, *active_upper_bound_);
}
BoundIterator BoundVector::GetActiveBounds(const mpq_class& value) const { return GetActiveBounds(value, value); }
BoundIterator BoundVector::GetActiveBounds(const mpq_class& lb, const mpq_class& ub) const {
  DLINEAR_ASSERT(lb == ub || (lb == *active_lower_bound_ && ub == *active_upper_bound_), "Bounds must be == or active");
  DLINEAR_ASSERT(lb <= ub, "Lower bound must be less or equal to upper bound");
  const auto lb_it = FindLowerBoundValue(&lb);
  const auto ub_it = FindUpperBoundValue(&ub);
  // The active bounds are empty. Non-equal bounds are inclusive
  if (lb_it == ub_it) return {lb_it, ub_it, FindLowerNqBoundValue(&lb), FindUpperNqBoundValue(&ub)};
  const auto& [value_lb, type_lb, lit_lb, exp_lb] = *lb_it;
  const auto& [value_ub, type_ub, lit_ub, exp_ub] = *(std::prev(ub_it));
  // The bounds contain only one type of bound or span across multiple values. There is no equality bound
  if (type_lb != LpColBound::L || type_ub != LpColBound::U || value_lb != value_ub)
    return {lb_it, ub_it, FindUpperNqBoundValue(&lb), FindLowerNqBoundValue(&ub)};

  auto it = lb_it;
  auto [value, type, lit, exp] = *it;
  for (; type != type_ub; ++it, type = it->lp_bound, lit = it->theory_literal) {
    if (lit == lit_ub) return {it, ub_it, FindUpperNqBoundValue(&lb), FindLowerNqBoundValue(&ub)};
  }
  it = std::prev(ub_it);
  type = it->lp_bound;
  lit = it->theory_literal;
  for (; type != type_lb; --it, type = it->lp_bound, lit = it->theory_literal) {
    if (lit == lit_lb) return {lb_it, std::next(it), FindUpperNqBoundValue(&lb), FindLowerNqBoundValue(&ub)};
  }
  return {lb_it, ub_it, FindUpperNqBoundValue(&lb), FindLowerNqBoundValue(&ub)};
}

LiteralSet BoundVector::GetActiveExplanation() const {
  LiteralSet explanation;
  GetActiveExplanation(explanation);
  return explanation;
}
void BoundVector::GetActiveExplanation(LiteralSet& explanation) const {
  for (BoundIterator it = GetActiveBound(); it; ++it) {
    explanation.insert(it->explanation.cbegin(), it->explanation.cend());
    explanation.insert(it->theory_literal);
  }
}
LiteralSet BoundVector::GetActiveEqExplanation() const {
  LiteralSet explanation;
  GetActiveEqExplanation(explanation);
  return explanation;
}
void BoundVector::GetActiveEqExplanation(LiteralSet& explanation) const {
  if (GetActiveEqualityBound() == nullptr) return;
  for (BoundIterator it = GetActiveBound(); it; ++it) {
    explanation.insert(it->explanation.cbegin(), it->explanation.cend());
    explanation.insert(it->theory_literal);
  }
}

std::pair<const mpq_class&, const mpq_class&> BoundVector::GetActiveBoundsValue() const {
  return {*active_lower_bound_, *active_upper_bound_};
}

void BoundVector::SetLowerBound(const mpq_class& value) {
  if (value > *active_upper_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (value > *active_lower_bound_) active_lower_bound_ = &value;
}
void BoundVector::SetUpperBound(const mpq_class& value) {
  if (value < *active_lower_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (value < *active_upper_bound_) active_upper_bound_ = &value;
}
void BoundVector::SetBounds(const mpq_class& lb, const mpq_class& ub) {
  if (ub < std::max(lb, *active_lower_bound_) || lb > std::min(ub, *active_upper_bound_))
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (lb > *active_lower_bound_) active_lower_bound_ = &lb;
  if (ub < *active_upper_bound_) active_upper_bound_ = &ub;
}

std::ostream& operator<<(std::ostream& os, const BoundVector& bounds_vector) {
  os << "BoundVector[";
  if (bounds_vector.active_lower_bound() == bounds_vector.inf_l())
    os << "-∞";
  else
    os << bounds_vector.active_lower_bound();
  os << ", ";
  if (bounds_vector.active_upper_bound() == bounds_vector.inf_u())
    os << "∞";
  else
    os << bounds_vector.active_upper_bound();
  os << "]{ ";
  for (const auto& [value, type, lit, exp] : bounds_vector.bounds()) {
    for (const Literal& e : exp) os << e << " ";
    if (!exp.empty()) os << "=> ";
    os << lit << ": " << *value << "( " << type << " ), ";
  }
  os << "}";
  return os;
}
std::ostream& operator<<(std::ostream& os, const BoundVectorMap& bounds_vector_map) {
  os << "ContextBoundVectorMap{ ";
  for (const auto& [col, bounds_vector] : bounds_vector_map) {
    os << "id " << col << ": " << bounds_vector << ", ";
  }
  os << "}";
  return os;
}
std::ostream& operator<<(std::ostream& os, const BoundVectorVector& bounds_vector_map) {
  os << "ContextBoundVectorVector{ ";
  for (const auto& bounds_vector : bounds_vector_map) {
    os << bounds_vector << ", ";
  }
  os << "}";
  return os;
}

}  // namespace dlinear
