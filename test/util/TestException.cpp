/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <stdexcept>

#include "dlinear/util/error.h"

using std::invalid_argument;
using std::runtime_error;

class TestException : public ::testing::Test {
 protected:
  void SetUp() override { DLINEAR_LOG_INIT_VERBOSITY(5); }
  void TearDown() override { DLINEAR_LOG_INIT_VERBOSITY(0); }
};

TEST_F(TestException, AssertFail) { EXPECT_DEATH(DLINEAR_ASSERT(false, "Message"), "Assertion `false` failed"); }

TEST_F(TestException, AssertFailReport) { EXPECT_DEATH(DLINEAR_ASSERT(1 + 1 == 3, "Message"), "Message"); }

TEST_F(TestException, AssertSuccess) { EXPECT_NO_THROW(DLINEAR_ASSERT(true, "Message")); }

TEST_F(TestException, Unreachable) { EXPECT_DEATH(DLINEAR_UNREACHABLE(), "Should not be reachable"); }

TEST_F(TestException, RuntimeError) { EXPECT_THROW(DLINEAR_RUNTIME_ERROR("Message"), runtime_error); }

TEST(TestLogging, RuntimeErrorFmt) { EXPECT_THROW(DLINEAR_RUNTIME_ERROR_FMT("Message: {}", "format"), runtime_error); }
