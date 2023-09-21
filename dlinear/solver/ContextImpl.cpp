/**
 * @file ContextImpl.cpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */

#include "ContextImpl.h"

#include <utility>

#include "dlinear/util/logging.h"

using std::string;
using std::unordered_set;
using std::vector;

namespace {

bool ParseBooleanOption(const string &key, const string &val) {
  if (val == "true") return true;
  if (val == "false") return false;
  DLINEAR_RUNTIME_ERROR_FMT("Unknown value {} is provided for option {}", val, key);
}

}  // namespace

namespace dlinear {

Context::Impl::Impl() : Impl{Config{}} {}

Context::Impl::Impl(const Config &config) : config_{config}, have_objective_{false}, is_max_{false} {
  boxes_.push_back(Box{});
}

Context::Impl::Impl(Config &&config) : config_{std::move(config)}, have_objective_{false}, is_max_{false} {
  boxes_.push_back(Box{});
}

std::optional<Box> Context::Impl::CheckSat(mpq_class *actual_precision) {
  auto result = CheckSatCore(stack_, box(), actual_precision);
  if (result) {
    // In case of delta-sat, do post-processing.
    // Tighten(&(*result), config_.precision());
    DLINEAR_DEBUG_FMT("ContextImpl::CheckSat() - Found Model\n{}", *result);
    model_ = ExtractModel(*result);
    return model_;
  } else {
    model_.set_empty();
    return result;
  }
}

int Context::Impl::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up, Box *model) {
  int result = CheckOptCore(stack_, obj_lo, obj_up, model);
  if (LP_DELTA_OPTIMAL == result) {
    DLINEAR_DEBUG_FMT("ContextImpl::CheckOpt() - Found Model\n{}", *model);
    *model = ExtractModel(*model);
    model_ = *model;  // For get_model()
    return result;
  } else {
    model->set_empty();
    model_ = *model;  // For get_model()
    return result;
  }
}

void Context::Impl::AddToBox(const Variable &v) {
  DLINEAR_DEBUG_FMT("ContextImpl::AddToBox({})", v);
  if (!box().has_variable(v)) box().Add(v);
}

void Context::Impl::DeclareVariable(const Variable &v, const bool is_model_variable) {
  DLINEAR_DEBUG_FMT("ContextImpl::DeclareVariable({})", v);
  AddToBox(v);
  if (is_model_variable) mark_model_variable(v);
}

void Context::Impl::SetDomain(const Variable &v, const Expression &lb, const Expression &ub) {
  DLINEAR_TRACE_FMT("ContextImpl::SetDomain({}, [{}, {}])", v, lb, ub);
  const mpq_class &lb_fp = lb.Evaluate();
  const mpq_class &ub_fp = ub.Evaluate();
  SetInterval(v, lb_fp, ub_fp);
}

void Context::Impl::Minimize(const vector<Expression> &functions) {
  DLINEAR_ASSERT(functions.size() == 1, "Must have exactly one objective function");

  const Expression &obj_expr{functions[0].Expand()};

  is_max_ = false;
  MinimizeCore(obj_expr);
}

void Context::Impl::Maximize(const vector<Expression> &functions) {
  DLINEAR_ASSERT(functions.size() == 1, "Must have exactly one objective function");

  // Negate objective function
  const Expression &obj_expr{(-functions[0]).Expand()};

  is_max_ = true;
  MinimizeCore(obj_expr);
}

void Context::Impl::SetInfo(const string &key, const double val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = fmt::format("{}", val);
}

void Context::Impl::SetInfo(const string &key, const string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
}

void Context::Impl::SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInterval({} = [{}, {}])", v, lb, ub);
  box()[v] = Box::Interval{lb, ub};
}

void Context::Impl::SetLogic(const Logic &logic) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetLogic({})", logic);
  logic_ = logic;
}

void Context::Impl::SetOption(const string &key, const double val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = fmt::format("{}", val);

  if (key == ":precision") {
    if (val <= 0.0) DLINEAR_RUNTIME_ERROR_FMT("Precision has to be positive (input = {}).", val);
    return config_.mutable_precision().set_from_file(val);
  }
}

void Context::Impl::SetOption(const string &key, const string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":polytope") return config_.mutable_use_polytope().set_from_file(ParseBooleanOption(key, val));
  if (key == ":forall-polytope")
    return config_.mutable_use_polytope_in_forall().set_from_file(ParseBooleanOption(key, val));
  if (key == ":local-optimization")
    return config_.mutable_use_local_optimization().set_from_file(ParseBooleanOption(key, val));
  if (key == ":worklist-fixpoint")
    return config_.mutable_use_worklist_fixpoint().set_from_file(ParseBooleanOption(key, val));
  if (key == ":produce-models") return config_.mutable_produce_models().set_from_file(ParseBooleanOption(key, val));
}

Box Context::Impl::ExtractModel(const Box &box) const {
  if (static_cast<int>(model_variables_.size()) == box.size()) {
    // Every variable is a model variable. Simply return the @p box.
    return box;
  }
  Box new_box;
  for (const Variable &v : box.variables()) {
    if (is_model_variable(v)) {
      new_box.Add(v, box[v].lb(), box[v].ub());
    }
  }
  return new_box;
}

bool Context::Impl::is_model_variable(const Variable &v) const {
  return model_variables_.find(v.get_id()) != model_variables_.end();
}

void Context::Impl::mark_model_variable(const Variable &v) { model_variables_.insert(v.get_id()); }

const ScopedVector<Formula> &Context::Impl::assertions() const { return stack_; }

bool Context::Impl::have_objective() const { return have_objective_; }

bool Context::Impl::is_max() const { return is_max_; }
}  // namespace dlinear
