#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

#include <gtest/gtest.h>
#include <fstream>

using dlinear::ArgParser;
using dlinear::Config;
using std::string;
using std::ofstream;
using std::remove;

class TestArgParser : public ::testing::Test {
 protected:
  dlinear::ArgParser parser_{};
  const string filename_{"TempFile.smt2"};
  const string bad_filename_{"TempFile.err"};
  const string non_existing_filename_{"NotExistingTempFile.smt2"};
  void SetUp() override {
    parser_ = ArgParser{};
    ofstream f{filename_};
    ofstream bf{bad_filename_};
    f.close();
    bf.close();
  }
  void TearDown() override {
    remove(filename_.c_str());
    remove(bad_filename_.c_str());
  }
};

TEST_F(TestArgParser, Contructor) {
  EXPECT_NO_THROW(ArgParser parser{});
}

TEST_F(TestArgParser, DefaultValues) {
  const int argc = 2;
  const char *argv[argc] = {"dlinear", filename_.c_str()};
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
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--verbosity", "1"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<int>("verbosity"), 1);
}

TEST_F(TestArgParser, ParsePrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--precision", "2.1"};
  parser_.parse(argc, argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 2.1);
}

TEST_F(TestArgParser, ParseInvalidPrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--precision", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --precision");
}

TEST_F(TestArgParser, ParseJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--jobs", "2"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint32_t>("jobs"), 2u);
}

TEST_F(TestArgParser, ParseInvalidJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--jobs", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "pattern not found");
}

TEST_F(TestArgParser, ParseContinuousOutput) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--continuous-output"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("continuous-output"));
}

TEST_F(TestArgParser, ParseProduceModels) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--produce-models"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("produce-models"));
}

TEST_F(TestArgParser, ParseRandomSeed) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--random-seed", "10"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint32_t>("random-seed"), 10ul);
}

TEST_F(TestArgParser, InvalidInAndFile) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--in"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --in");
}

TEST_F(TestArgParser, FileNotFound) {
  const int argc = 2;
  const char *argv[argc] = {"dlinear", non_existing_filename_.c_str()};
  EXPECT_DEATH(parser_.parse(argc, argv), "cannot find file");
}

TEST_F(TestArgParser, FileNotProvided) {
  const int argc = 1;
  const char *argv[argc] = {"dlinear"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, AutoFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--format", "auto"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_);
}

TEST_F(TestArgParser, Smt2Format) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--format", "smt2"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_);
}

TEST_F(TestArgParser, WrongAutoFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", bad_filename_.c_str(), "--format", "auto"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, WrongSmt2Format) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", bad_filename_.c_str(), "--format", "smt2"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, WrongFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_.c_str(), "--format", "invalid"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --format");
}