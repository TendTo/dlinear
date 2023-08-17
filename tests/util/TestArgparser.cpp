#include <gtest/gtest.h>
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;

class TestArgParser : public ::testing::Test {
 protected:
  dlinear::ArgParser parser_{};
  virtual void SetUp() {
    parser_ = ArgParser{};
  }
};

TEST_F(TestArgParser, Contructor) {
  EXPECT_NO_THROW(ArgParser parser{});
}

TEST_F(TestArgParser, DefaultValues) {
  const int argc = 2;
  const char *argv[argc] = {"dlinear", "file"};
  parser_.parse(argc, argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 9.999999999999996e-4);
  EXPECT_FALSE(parser_.get<bool>("produce-models"));
  EXPECT_EQ(parser_.get<uint32_t>("random-seed"), 0u);
  EXPECT_EQ(parser_.get<uint32_t>("jobs"), 1u);
  EXPECT_FALSE(parser_.get<bool>("continuous-output"));
  EXPECT_FALSE(parser_.get<bool>("debug-parsing"));
  EXPECT_FALSE(parser_.get<bool>("debug-scanning"));
  EXPECT_FALSE(parser_.get<bool>("exhaustive"));
  EXPECT_FALSE(parser_.get<bool>("forall-polytope"));
  EXPECT_FALSE(parser_.get<bool>("in"));
  EXPECT_FALSE(parser_.get<bool>("local-optimization"));
  EXPECT_EQ(parser_.get<Config::LPSolver>("lp-solver"), Config::LPSolver::QSOPTEX);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-ftol-abs"), 1e-6);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-ftol-rel"), 1e-6);
  EXPECT_EQ(parser_.get<uint32_t>("nlopt-maxeval"), 100u);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-maxtime"), 0.01);
  EXPECT_FALSE(parser_.get<bool>("polytope"));
  EXPECT_EQ(parser_.get<Config::SatDefaultPhase>("sat-default-phase"), Config::SatDefaultPhase::JeroslowWang);
  EXPECT_EQ(parser_.get<int>("simplex-sat-phase"), 1);
  EXPECT_FALSE(parser_.get<bool>("timings"));
  EXPECT_EQ(parser_.get<int>("verbosity"), 2);
  EXPECT_EQ(parser_.get<int>("verbose-simplex"), 0);
  EXPECT_FALSE(parser_.get<bool>("worklist-fixpoint"));
}

TEST_F(TestArgParser, ParseVerbosity) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--verbosity", "1"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<int>("verbosity"), 1);
}

TEST_F(TestArgParser, ParsePrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--precision", "2.1"};
  parser_.parse(argc, argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 2.1);
}

TEST_F(TestArgParser, ParseInvalidPrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--precision", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --precision");
}

TEST_F(TestArgParser, ParseJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--jobs", "2"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint32_t>("jobs"), 2u);
}

TEST_F(TestArgParser, ParseInvalidJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--jobs", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "pattern not found");
}

TEST_F(TestArgParser, ParseContinuousOutput) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", "file", "--continuous-output"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("continuous-output"));
}

TEST_F(TestArgParser, ParseProduceModels) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", "file", "--produce-models"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("produce-models"));
}

TEST_F(TestArgParser, ParseRandomSeed) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", "file", "--random-seed", "10"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint32_t>("random-seed"), 10ul);
}

