#include <gtest/gtest.h>

#include <fstream>

#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;
using std::ofstream;
using std::remove;
using std::string;

class TestArgParser : public ::testing::Test {
 protected:
  dlinear::ArgParser parser_{};
  const string filename_smt2_{"TempFile.smt2"};
  const string filename_mps_{"TempFile.mps"};
  const string bad_filename_{"TempFile.err"};
  const string non_existing_filename_{"NotExistingTempFile.smt2"};
  void SetUp() override {
    parser_ = ArgParser{};
    ofstream f{filename_smt2_};
    ofstream m{filename_mps_};
    ofstream bf{bad_filename_};
    f.close();
    m.close();
    bf.close();
  }
  void TearDown() override {
    remove(filename_smt2_.c_str());
    remove(filename_mps_.c_str());
    remove(bad_filename_.c_str());
  }
};

TEST_F(TestArgParser, Contructor) { EXPECT_NO_THROW(ArgParser parser{}); }

TEST_F(TestArgParser, DefaultValues) {
  const int argc = 2;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str()};
  parser_.parse(argc, argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 9.999999999999996e-4);
  EXPECT_FALSE(parser_.get<bool>("produce-models"));
  EXPECT_EQ(parser_.get<uint>("random-seed"), 0u);
  EXPECT_EQ(parser_.get<uint>("jobs"), 1u);
  EXPECT_FALSE(parser_.get<bool>("continuous-output"));
  EXPECT_FALSE(parser_.get<bool>("debug-parsing"));
  EXPECT_FALSE(parser_.get<bool>("debug-scanning"));
  EXPECT_FALSE(parser_.get<bool>("forall-polytope"));
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
  EXPECT_FALSE(parser_.get<bool>("in"));
  EXPECT_FALSE(parser_.get<bool>("local-optimization"));
  EXPECT_EQ(parser_.get<Config::LPSolver>("lp-solver"), Config::LPSolver::SOPLEX);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-ftol-abs"), 1e-6);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-ftol-rel"), 1e-6);
  EXPECT_EQ(parser_.get<uint>("nlopt-maxeval"), 100u);
  EXPECT_DOUBLE_EQ(parser_.get<double>("nlopt-maxtime"), 0.01);
  EXPECT_FALSE(parser_.get<bool>("polytope"));
  EXPECT_EQ(parser_.get<Config::SatDefaultPhase>("sat-default-phase"), Config::SatDefaultPhase::JeroslowWang);
  EXPECT_EQ(parser_.get<int>("simplex-sat-phase"), 1);
  EXPECT_FALSE(parser_.get<bool>("timings"));
  EXPECT_EQ(parser_.get<int>("verbosity"), 2);
  EXPECT_EQ(parser_.get<int>("verbose-simplex"), 0);
  EXPECT_FALSE(parser_.get<bool>("worklist-fixpoint"));
  EXPECT_FALSE(parser_.get<bool>("silent"));
  EXPECT_FALSE(parser_.get<bool>("skip-check-sat"));
}

TEST_F(TestArgParser, ParseVerbosity) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--verbosity", "1"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<int>("verbosity"), 1);
}

TEST_F(TestArgParser, ParsePrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--precision", "2.1"};
  parser_.parse(argc, argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 2.1);
}

TEST_F(TestArgParser, ParseInvalidPrecision) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--precision", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --precision");
}

TEST_F(TestArgParser, ParseJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--jobs", "2"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint>("jobs"), 2u);
}

TEST_F(TestArgParser, ParseInvalidJobs) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--jobs", "-1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "pattern not found");
}

TEST_F(TestArgParser, ParseContinuousOutput) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--continuous-output"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("continuous-output"));
}

TEST_F(TestArgParser, ParseProduceModels) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--produce-models"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("produce-models"));
}

TEST_F(TestArgParser, ParseRandomSeed) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--random-seed", "10"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<uint>("random-seed"), 10ul);
}

TEST_F(TestArgParser, InvalidInAndFile) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--in"};
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

TEST_F(TestArgParser, AutoFormatSmt2) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--format", "auto"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_smt2_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
}

TEST_F(TestArgParser, AutoFormatMps) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_mps_.c_str(), "--format", "auto"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_mps_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
}

TEST_F(TestArgParser, WrongAutoFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", bad_filename_.c_str(), "--format", "auto"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, Smt2Format) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--format", "smt2"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_smt2_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::SMT2);
}

TEST_F(TestArgParser, WrongSmt2FormatErr) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", bad_filename_.c_str(), "--format", "smt2"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, WrongSmt2FormatMps) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_mps_.c_str(), "--format", "smt2"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, MpsFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_mps_.c_str(), "--format", "mps"};
  parser_.parse(argc, argv);
  EXPECT_EQ(parser_.get<string>("file"), filename_mps_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::MPS);
}

TEST_F(TestArgParser, WrongMpsFormatErr) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", bad_filename_.c_str(), "--format", "mps"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, WrongMpsFormatSmt2) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--format", "mps"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for file");
}

TEST_F(TestArgParser, WrongFormat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--format", "invalid"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --format");
}

TEST_F(TestArgParser, SkipCheckSat) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--skip-check-sat"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("skip-check-sat"));
}

TEST_F(TestArgParser, WrongSkipCheckSat) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--skip-check-sat", "--produce-models"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --produce-models");
}

TEST_F(TestArgParser, Exhaustive) {
  const int argc = 4;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--precision", "0"};
  parser_.parse(argc, argv);
  auto config = parser_.toConfig();
  EXPECT_DOUBLE_EQ(config.precision(), 0.0);
}

TEST_F(TestArgParser, Silent) {
  const int argc = 3;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--silent"};
  parser_.parse(argc, argv);
  EXPECT_TRUE(parser_.get<bool>("silent"));
}

TEST_F(TestArgParser, WrongSilentWithVerbosity) {
  const int argc = 5;
  const char *argv[argc] = {"dlinear", filename_smt2_.c_str(), "--silent", "--verbosity", "1"};
  EXPECT_DEATH(parser_.parse(argc, argv), "Invalid argument for --verbosity");
}

TEST_F(TestArgParser, In) {
  const int argc = 2;
  const char *argv[argc] = {"dlinear", "--in"};
  parser_.parse(argc, argv);
  auto config = parser_.toConfig();
  EXPECT_TRUE(config.read_from_stdin());
}
