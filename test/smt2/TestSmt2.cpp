/**
 * @file TestSmt2.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"
#include "dlinear/smt2/run.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"

using dlinear::ArgParser;
using dlinear::qsopt_ex::QSXStart;
using dlinear::Expression;
using dlinear::Config;
using dlinear::smt2::RunSmt2;
using dlinear::Infinity;
using dlinear::qsopt_ex::QSXFinish;

int main(int argc, const char *argv[]) {
  ArgParser argParser;
  argParser.parse(argc, argv);
  Config config = argParser.toConfig();

  Infinity::InftyStart(config);
  Expression::InitConstants();

  RunSmt2(config);

  Expression::DeInitConstants();
  Infinity::InftyFinish();
  return 0;
}