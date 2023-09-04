/**
 * @file Infinity.cpp
 * @author dlinear
 * @date 04 Sep 2023
 * @copyright 2023 dlinear
 */

#include "Infinity.h"

#include <utility>

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

Infinity* Infinity::instance_{nullptr};

Infinity::Infinity(Config::LPSolver lp_solver, mpq_class infty, mpq_class ninfty)
    : lp_solver_{lp_solver}, infty_{std::move(infty)}, ninfty_{std::move(ninfty)} {}
Infinity::~Infinity() {
  if (lp_solver_ == Config::QSOPTEX) qsopt_ex::QSXFinish();
}

void Infinity::InftyStart(Config::LPSolver lp_solver, double value) {
  mpq_class new_infty{value};
  if (instance_ == nullptr) [[likely]]
    instance_ = new Infinity(lp_solver, new_infty, -new_infty);
  else
    DLINEAR_WARN("Infinity already initialized! No action taken.");
}

void Infinity::InftyStart(Config::LPSolver lp_solver, const mpq_class& value) {
  if (instance_ == nullptr) [[likely]]
    instance_ = new Infinity(lp_solver, value, -value);
  else
    DLINEAR_WARN("Infinity already initialized! No action taken.");
}

void Infinity::InftyStart(Config::LPSolver lp_solver, const mpq_t infty, const mpq_t ninfty) {
  if (instance_ == nullptr) [[likely]]
    instance_ = new Infinity(lp_solver, mpq_class{infty}, mpq_class{ninfty});
  else
    DLINEAR_WARN("Infinity already initialized! No action taken.");
}

void Infinity::InftyStart(const Config& config) { InftyStart(config.lp_solver()); }

void Infinity::InftyStart(Config::LPSolver lp_solver) {
  switch (lp_solver) {
    case Config::QSOPTEX:
      qsopt_ex::QSXStart();
      InftyStart(lp_solver, mpq_INFTY, mpq_NINFTY);
      break;
    case Config::SOPLEX:
      InftyStart(lp_solver, soplex::infinity);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void Infinity::InftyFinish() {
  if (instance_ != nullptr) [[likely]] {
    delete instance_;
    instance_ = nullptr;
  } else {
    DLINEAR_WARN("Infinity not initialized! No action taken.");
  }
}

const mpq_class& Infinity::Infty() {
  DLINEAR_ASSERT(instance_ != nullptr, "Infinity not initialized!");
  return instance_->infty_;
}

const mpq_class& Infinity::Ninfty() {
  DLINEAR_ASSERT(instance_ != nullptr, "Infinity not initialized!");
  return instance_->ninfty_;
}

}  // namespace dlinear
