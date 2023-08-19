/**
 * @file libs.cp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */
#include <iostream>
#include "dlinear/libs/soplex.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/gmp.h"

int main([[maybe_unused]] int argc, [[maybe_unused]] const char **argv) {
  soplex::SoPlex soplex;
  soplex.printVersion();
  dlinear::qsopt_ex::QSXStart();
  dlinear::qsopt_ex::QSXFinish();
  mpq_class a(1);
  mpq_class b(2);
  mpq_class c(3);
  std::cout << a + b + c << std::endl;
  return 0;
}
