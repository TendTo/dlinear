/**
 * @file run.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Entrypoint for the smt2 functionality of dlinear.
 *
 * Runs the smt2 driver.
 */
#ifndef DLINEAR_SMT2_RUN_H_
#define DLINEAR_SMT2_RUN_H_

#include <string>

#include "dlinear/util/Config.h"

namespace dlinear {

void RunSmt2(const Config &config);

}  // namespace dlinear

#endif  // DLINEAR_SMT2_RUN_H_
