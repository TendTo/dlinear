/**
 * @file Context.cpp
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Context.h"

#include <memory>
#include <utility>

#include "dlinear/solver/QsoptexImpl.h"
#include "dlinear/solver/SoplexImpl.h"
#include "dlinear/version.h"

using std::make_unique;
using std::string;
using std::unique_ptr;
using std::vector;

namespace dlinear {

unique_ptr<Context::Impl> Context::make_impl(const Config &config) {
  if (config.lp_solver() == Config::QSOPTEX) return make_unique<Context::QsoptexImpl>(config);
  if (config.lp_solver() == Config::SOPLEX) return make_unique<Context::SoplexImpl>(config);
  DLINEAR_RUNTIME_ERROR("Unsupported LP solver");
}

Context::Context() : Context{Config{}} {}

Context::Context(Context &&context) noexcept : impl_{std::move(context.impl_)} {}

Context::~Context() = default;

Context::Context(const Config &config) : impl_{make_impl(config)} {}

void Context::Assert(const Formula &f) { impl_->Assert(f); }

SatResult Context::CheckSat(mpq_class *actual_precision, Box *model) {
  return impl_->CheckSat(actual_precision, model);
}

int Context::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up, Box *model) {
  return impl_->CheckOpt(obj_lo, obj_up, model);
}

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

void Context::Minimize(const vector<Expression> &functions) { impl_->Minimize(functions); }

void Context::Maximize(const Expression &f) { impl_->Maximize({f}); }

void Context::Pop(int n) {
  DLINEAR_DEBUG_FMT("Context::Pop({})", n);
  if (n <= 0) {
    DLINEAR_RUNTIME_ERROR_FMT("Context::Pop(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Pop();
  }
}

void Context::Push(int n) {
  DLINEAR_DEBUG_FMT("Context::Push({})", n);
  if (n <= 0) {
    DLINEAR_RUNTIME_ERROR_FMT("Context::Push(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Push();
  }
}

void Context::SetInfo(const string &key, const double val) { impl_->SetInfo(key, val); }

void Context::SetInfo(const string &key, const string &val) { impl_->SetInfo(key, val); }

void Context::SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  impl_->SetInterval(v, lb, ub);
}

void Context::SetLogic(const Logic &logic) { impl_->SetLogic(logic); }

void Context::SetOption(const string &key, const double val) { impl_->SetOption(key, val); }

void Context::SetOption(const string &key, const string &val) { impl_->SetOption(key, val); }

const Config &Context::config() const { return impl_->config(); }
Config &Context::mutable_config() { return impl_->mutable_config(); }

string Context::version() { return DLINEAR_VERSION_STRING; }

string Context::repository_status() { return DLINEAR_VERSION_REPOSTAT; }

const Box &Context::box() const { return impl_->box(); }

const Box &Context::get_model() const { return impl_->get_model(); }

const ScopedVector<Formula> &Context::assertions() const { return impl_->assertions(); }

bool Context::have_objective() const { return impl_->have_objective(); }

bool Context::is_max() const { return impl_->is_max(); }

}  // namespace dlinear
