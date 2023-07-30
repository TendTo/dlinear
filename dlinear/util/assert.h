#ifndef DLINEAR5_ASSERT_H
#define DLINEAR5_ASSERT_H

#ifdef NDEBUG
#define DLINEAR_ASSERT(condition, msg) ((void)0)
#else

#include <cassert>

#define DLINEAR_ASSERT(condition, msg) assert(condition && msg)
#endif

#endif //DLINEAR5_ASSERT_H
