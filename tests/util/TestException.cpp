/**
 * @file TestException.cpp
 * @author dlinear
 * @date 16 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/util/exception.h"

#include <gtest/gtest.h>
#include <stdexcept>

using std::runtime_error;
using std::invalid_argument;

class TestException : public ::testing::Test {
 protected:
  void SetUp() override { DLINEAR_LOG_INIT_VERBOSITY(5); }
  void TearDown() override { DLINEAR_LOG_INIT_VERBOSITY(-1); }
};

TEST_F(TestException, AssertFail) {
  EXPECT_DEATH(DLINEAR_ASSERT(false, "Message"), "Assertion `false` failed");
}

TEST_F(TestException, AssertFailReport) {
  EXPECT_DEATH(DLINEAR_ASSERT(1 + 1 == 3, "Message"), "Message");
}

TEST_F(TestException, AssertSuccess) {
  EXPECT_NO_THROW(DLINEAR_ASSERT(true, "Message"));
}

TEST_F(TestException, Unreachable) {
  EXPECT_DEATH(DLINEAR_UNREACHABLE(), "Should not be reachable");
}

TEST_F(TestException, RuntimeError) {
  EXPECT_THROW(DLINEAR_RUNTIME_ERROR("Message"), runtime_error);
}

TEST(TestLogging, RuntimeErrorFmt) {
  EXPECT_THROW(DLINEAR_RUNTIME_ERROR_FMT("Message: {}", "format"), runtime_error);
}
