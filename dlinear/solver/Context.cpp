/**
 * @file Context.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "Context.h"

#include <memory>
#include <tuple>
#include <utility>

#include "dlinear/solver/ContextImpl.h"
#include "dlinear/util/logging.h"

namespace dlinear {

Context::Context(Context &&context) noexcept : impl_{std::move(context.impl_)} {}

Context::~Context() = default;

Context::Context(const Config::SharedConfig &config) : impl_{std::make_unique<Impl>(config)} {}

void Context::Assert(const Formula &f) { impl_->Assert(f); }
SatResult Context::CheckSat(mpq_class *actual_precision) { return impl_->CheckSat(actual_precision); }
LpResult Context::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up) { return impl_->CheckOpt(obj_lo, obj_up); }
void Context::DeclareVariable(const Variable &v, const bool is_model_variable) {
  impl_->DeclareVariable(v, is_model_variable);
}
void Context::DeclareVariable(const Variable &v, const Expression &lb, const Expression &ub,
                              const bool is_model_variable) {
  impl_->DeclareVariable(v, is_model_variable);
  impl_->SetDomain(v, lb, ub);
}
void Context::Exit() { DLINEAR_DEBUG("Context::Exit()"); }
void Context::Minimize(const Expression &f) { impl_->Minimize({f}); }
void Context::Maximize(const Expression &f) { impl_->Maximize({f}); }

void Context::Pop(int n) {
  DLINEAR_DEBUG_FMT("Context::Pop({})", n);
  if (n <= 0) DLINEAR_RUNTIME_ERROR_FMT("Context::Pop(n) called with n = {} which is not positive.", n);
  while (n-- > 0) impl_->Pop();
}

void Context::Push(int n) {
  DLINEAR_DEBUG_FMT("Context::Push({})", n);
  if (n <= 0) DLINEAR_RUNTIME_ERROR_FMT("Context::Push(n) called with n = {} which is not positive.", n);
  while (n-- > 0) impl_->Push();
}

void Context::SetInfo(const std::string &key, const double val) { impl_->SetInfo(key, val); }
void Context::SetInfo(const std::string &key, const std::string &val) { impl_->SetInfo(key, val); }
std::string Context::GetInfo(const std::string &key) const { return impl_->GetInfo(key); }
void Context::SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  impl_->SetInterval(v, lb, ub);
}
void Context::SetLogic(const Logic &logic) { impl_->SetLogic(logic); }
void Context::SetOption(const std::string &key, const double val) { impl_->SetOption(key, val); }
void Context::SetOption(const std::string &key, const std::string &val) { impl_->SetOption(key, val); }
std::string Context::GetOption(const std::string &key) const { return impl_->GetOption(key); }
const Config &Context::config() const { return impl_->config(); }
const Box &Context::box() const { return impl_->box(); }
const Box &Context::model() const { return impl_->get_model(); }
const ScopedVector<Formula> &Context::assertions() const { return impl_->assertions(); }
bool Context::have_objective() const { return impl_->have_objective(); }
bool Context::is_max() const { return impl_->is_max(); }
const IterationStats &Context::sat_stats() const { return impl_->sat_stats(); }
const IterationStats &Context::theory_stats() const { return impl_->theory_stats(); }

std::tuple<const IterationStats &, const IterationStats &, const IterationStats &> Context::formula_visitors_stats()
    const {
  return impl_->formula_visitors_stats();
}

}  // namespace dlinear
