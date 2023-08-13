/**
 * @file soplex.h
 * @author tend
 * @date 09 Aug 2023
 * @copyright 2023 tend
 * Soplex wrapper.
 *
 * This header includes the Soplex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Soplex library directly.
 * Instead of including <soplex.h>, include "dlinear/libs/soplex.h".
 * In the build files, instead of depending on "@soplex", depend on "//dlinear/libs:soplex".
 */

#ifndef DLINEAR5_DLINEAR_LIBS_SOPLEX_H_
#define DLINEAR5_DLINEAR_LIBS_SOPLEX_H_

#define SOPLEX_WITH_GMP
#include <soplex.h>

namespace dlinear::soplex {

} // namespace dlinear::soplex

#endif //DLINEAR5_DLINEAR_LIBS_SOPLEX_H_
