/**
 * @file MainProgram.cpp
 * @author dlinear
 * @date 12 Aug 2023
 * @copyright 2023 dlinear
 */

#include "MainProgram.h"

#include "dlinear/util/ArgParser.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/solver/Context.h"
#include "dlinear/smt2/run.h"
#include "dlinear/util/infty.h"

namespace dlinear {

void MainProgram::Init() {
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXStart();
    InftyStart(mpq_INFTY, mpq_NINFTY);
  } else if (config_.lp_solver() == Config::SOPLEX) {
    InftyStart(soplex::infinity);
  } else {
    DLINEAR_UNREACHABLE();
  }
  Expression::InitConstants();
}

void MainProgram::DeInit() {
  Expression::DeInitConstants();
  InftyFinish();
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXFinish();
  }
}

MainProgram::MainProgram(int argc, const char **argv) {
  ArgParser parser{QSopt_ex_repository_status(), soplex::getGitHash()};
  parser.parse(argc, argv);
  config_ = parser.toConfig();
}

int MainProgram::Run() {
  Init();
  RunSmt2(config_);
  DeInit();
  return 0;
}

} // namespace dlinear
