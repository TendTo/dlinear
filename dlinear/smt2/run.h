/**
 * @file run.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Entrypoint for the smt2 functionality of dlinear.
 *
 * Runs the smt2 driver.
 */
#pragma once

#include <string>

#include "dlinear/util/Config.h"

namespace dlinear {

void RunSmt2(const Config &config);

}  // namespace dlinear
