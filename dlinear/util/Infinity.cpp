/**
 * @file Infinity.cpp
 * @author dlinear
 * @date 04 Sep 2023
 * @copyright 2023 dlinear
 */

#include "Infinity.h"

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

Infinity* Infinity::instance_{nullptr};

Infinity::Infinity(Config::LPSolver lp_solver, double value)
    : lp_solver_{lp_solver}, infty_{new mpq_class{value}}, ninfty_{new mpq_class{-value}} {}

Infinity::Infinity(Config::LPSolver lp_solver, const mpq_class& value)
    : lp_solver_{lp_solver}, infty_{new mpq_class{value}}, ninfty_{new mpq_class{-value}} {}

Infinity::Infinity(Config::LPSolver lp_solver, const mpq_t infty, const mpq_t ninfty)
    : lp_solver_{lp_solver}, infty_{new mpq_class{infty}}, ninfty_{new mpq_class{ninfty}} {}

Infinity::~Infinity() {
  delete infty_;
  delete ninfty_;
#ifdef DLINEAR_ENABLED_QSOPTEX
  if (lp_solver_ == Config::LPSolver::QSOPTEX) qsopt_ex::QSXFinish();
#endif
}

void Infinity::InftyStart(const Config& config) { InftyStart(config.lp_solver()); }

void Infinity::InftyStart(Config::LPSolver lp_solver) {
  if (instance_ != nullptr) {
    DLINEAR_WARN("Infinity already initialized! No action taken.");
    return;
  }
  switch (lp_solver) {
#ifdef DLINEAR_ENABLED_QSOPTEX
    case Config::LPSolver::QSOPTEX:
      qsopt_ex::QSXStart();
      instance_ = new Infinity(lp_solver, mpq_INFTY, mpq_NINFTY);
      break;
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    case Config::LPSolver::SOPLEX:
      instance_ = new Infinity(lp_solver, soplex::infinity);
      break;
#endif
    default:
      DLINEAR_UNREACHABLE();
  }
}

void Infinity::InftyFinish() {
  if (instance_ != nullptr) {
    delete instance_;
    instance_ = nullptr;
  } else {
    DLINEAR_WARN("Infinity not initialized! No action taken.");
  }
}

const mpq_class& Infinity::Infty() {
  DLINEAR_ASSERT(instance_ != nullptr, "Infinity not initialized!");
  return *instance_->infty_;
}

const mpq_class& Infinity::Ninfty() {
  DLINEAR_ASSERT(instance_ != nullptr, "Infinity not initialized!");
  return *instance_->ninfty_;
}

}  // namespace dlinear
