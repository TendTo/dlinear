/**
 * @file soplex.h
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 * Soplex wrapper.
 *
 * This header includes the Soplex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Soplex library directly.
 * Instead of including <soplex.h>, include "dlinear/libs/soplex.h".
 * In the build files, instead of depending on "@soplex", depend on "//dlinear/libs:soplex".
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

// This import is unfortunately necessary to avoid a fmt clashes between spdlog and soplex.
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

#include <soplex.h>  // NOLINT
