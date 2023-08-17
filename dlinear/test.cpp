/**
 * @file test.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */
#include "picosat.h"
#include <iostream>

int main() {
  PicoSAT *sat_{};
  picosat_add(sat_, 1);
  std::cout << sat_ << std::endl;
  return 0;
}