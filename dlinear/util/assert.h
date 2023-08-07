/**
 * @file assert.h
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 * @brief Assert macro. Assert that the condition is true, otherwise abort.
 *
 * If NDEBUG is defined, the assert macro does nothing.
 */
#ifndef DLINEAR5_ASSERT_H
#define DLINEAR5_ASSERT_H

#ifdef NDEBUG
#define DLINEAR_ASSERT(condition, msg) ((void)0)
#else

#include <cassert>

#define DLINEAR_ASSERT(condition, msg) assert(condition && msg)
#endif

#endif //DLINEAR5_ASSERT_H
