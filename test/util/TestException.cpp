/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <stdexcept>

#include "dlinear/util/error.h"

using dlinear::DlinearAssertionException;
using dlinear::DlinearException;
using dlinear::DlinearInvalidArgumentException;
using dlinear::DlinearUnreachableException;
using std::invalid_argument;
using std::runtime_error;

#ifndef NDEBUG

TEST(TestException, AssertFail) { EXPECT_THROW(DLINEAR_ASSERT(false, "Message"), DlinearAssertionException); }

TEST(TestException, AssertFailReport) {
  EXPECT_THROW(DLINEAR_ASSERT(1 + 1 == 3, "Message"), DlinearAssertionException);
}

TEST(TestException, AssertSuccess) { EXPECT_NO_THROW(DLINEAR_ASSERT(true, "Message")); }

TEST(TestException, Unreachable) { EXPECT_THROW(DLINEAR_UNREACHABLE(), DlinearUnreachableException); }

#else

TEST(TestException, AssertFail) { EXPECT_NO_THROW(DLINEAR_ASSERT(false, "Message")); }

TEST(TestException, AssertFailReport) { EXPECT_NO_THROW(DLINEAR_ASSERT(1 + 1 == 3, "Message")); }

TEST(TestException, AssertSuccess) { EXPECT_NO_THROW(DLINEAR_ASSERT(true, "Message")); }

TEST(TestException, Unreachable) { EXPECT_DEATH(DLINEAR_UNREACHABLE()); }

#endif

TEST(TestException, RuntimeError) { EXPECT_THROW(DLINEAR_RUNTIME_ERROR("Message"), DlinearException); }

TEST(TestException, RuntimeErrorFmt) {
  EXPECT_THROW(DLINEAR_RUNTIME_ERROR_FMT("Message: {}", "format"), DlinearException);
}

TEST(TestException, InvalidArgument) {
  EXPECT_THROW(DLINEAR_INVALID_ARGUMENT("Message: {}", "actual"), DlinearInvalidArgumentException);
}

TEST(TestException, InvalidArgumentExpected) {
  EXPECT_THROW(DLINEAR_INVALID_ARGUMENT_EXPECTED("Message: {}", "actual", "expected"), DlinearInvalidArgumentException);
}
