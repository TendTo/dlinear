/**
 * @file soplex.h
 * @author tend
 * @date 09 Aug 2023
 * @copyright 2023 tend
 * @brief Soplex wrapper.
 *
 * This header includes the Soplex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Soplex library directly.
 */

#ifndef DLINEAR5_DLINEAR_LIBS_SOPLEX_H_
#define DLINEAR5_DLINEAR_LIBS_SOPLEX_H_

#include <soplex.h>

namespace dlinear::soplex {
void runExample();
} // namespace dlinear::soplex

#endif //DLINEAR5_DLINEAR_LIBS_SOPLEX_H_
