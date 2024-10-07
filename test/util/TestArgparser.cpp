/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <fstream>

#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;

class TestArgParser : public ::testing::Test {
 protected:
  dlinear::ArgParser parser_{};
  const std::string filename_smt2_{"TempFile.smt2"};
  const std::string filename_mps_{"TempFile.mps"};
  const std::string filename_vnnlib_{"TempFile.vnnlib"};
  const std::string filename_onnx_{"TempFile.onnx"};
  const std::string bad_filename_{"TempFile.err"};
  const std::string non_existing_filename_{"NotExistingTempFile.smt2"};
  void SetUp() override {
    std::ofstream f{filename_smt2_};
    std::ofstream m{filename_mps_};
    std::ofstream v{filename_vnnlib_};
    std::ofstream o{filename_onnx_};
    std::ofstream bf{bad_filename_};
  }
  void TearDown() override {
    std::remove(filename_smt2_.c_str());
    std::remove(filename_mps_.c_str());
    std::remove(filename_vnnlib_.c_str());
    std::remove(filename_onnx_.c_str());
    std::remove(bad_filename_.c_str());
  }
};

TEST_F(TestArgParser, Contructor) { EXPECT_NO_THROW(ArgParser parser{}); }

TEST_F(TestArgParser, DefaultValues) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str()};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 9.999999999999996e-4);
  EXPECT_FALSE(parser_.get<bool>("produce-models"));
  EXPECT_EQ(parser_.get<uint>("random-seed"), 0u);
  EXPECT_EQ(parser_.get<uint>("jobs"), 1u);
  EXPECT_FALSE(parser_.get<bool>("continuous-output"));
  EXPECT_FALSE(parser_.get<bool>("debug-parsing"));
  EXPECT_FALSE(parser_.get<bool>("debug-scanning"));
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
  EXPECT_FALSE(parser_.get<bool>("in"));
  EXPECT_EQ(parser_.get<Config::LPSolver>("lp-solver"), Config::LPSolver::SOPLEX);
  EXPECT_EQ(parser_.get<Config::SatDefaultPhase>("sat-default-phase"), Config::SatDefaultPhase::JeroslowWang);
  EXPECT_EQ(parser_.get<int>("simplex-sat-phase"), 1);
  EXPECT_FALSE(parser_.get<bool>("timings"));
  EXPECT_EQ(parser_.get<int>("verbose-simplex"), 0);
  EXPECT_FALSE(parser_.get<bool>("silent"));
  EXPECT_FALSE(parser_.get<bool>("skip-check-sat"));
}

TEST_F(TestArgParser, ParseVerbosityIncreaseOne) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--verbose"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), Config::default_verbose_dlinear + 1);
}

TEST_F(TestArgParser, ParseVerbosityIncreaseMultiple) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "-VV"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), Config::default_verbose_dlinear + 2);
}

TEST_F(TestArgParser, ParseVerbosityIncreaseMax) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "-VVVVVVVVV"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), 5);
}

TEST_F(TestArgParser, ParseVerbosityDecreaseOne) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--quiet"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), Config::default_verbose_dlinear - 1);
}

TEST_F(TestArgParser, ParseVerbosityDecreaseMultiple) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "-qq"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), Config::default_verbose_dlinear - 2);
}

TEST_F(TestArgParser, ParseVerbosityDecreaseMin) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "-qqqqqqqqqqqqqq"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.toConfig().verbose_dlinear(), 0);
}

TEST_F(TestArgParser, ParsePrecision) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--precision", "2.1"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_DOUBLE_EQ(parser_.get<double>("precision"), 2.1);
}

TEST_F(TestArgParser, ParseInvalidPrecision) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--precision", "-1"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --precision");
}

TEST_F(TestArgParser, ParseJobs) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--jobs", "2"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<uint>("jobs"), 2u);
}

TEST_F(TestArgParser, ParseInvalidJobs) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--jobs", "-1"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Failed to parse '-1' as decimal integer");
}

TEST_F(TestArgParser, ParseContinuousOutput) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--continuous-output"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_TRUE(parser_.get<bool>("continuous-output"));
}

TEST_F(TestArgParser, ParseProduceModels) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--produce-models"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_TRUE(parser_.get<bool>("produce-models"));
}

TEST_F(TestArgParser, ParseRandomSeed) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--random-seed", "10"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<uint>("random-seed"), 10ul);
}

TEST_F(TestArgParser, InvalidInAndFile) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--in"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --in");
}

TEST_F(TestArgParser, FileNotFound) {
  const char *argv[] = {"dlinear", non_existing_filename_.c_str()};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "cannot find file");
}

TEST_F(TestArgParser, FileNotProvided) {
  const char *argv[] = {"dlinear"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for file");
}

TEST_F(TestArgParser, AutoFormatSmt2) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--format", "auto"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<std::string>("file"), filename_smt2_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
}

TEST_F(TestArgParser, AutoFormatMps) {
  const char *argv[] = {"dlinear", filename_mps_.c_str(), "--format", "auto"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<std::string>("file"), filename_mps_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::AUTO);
}

TEST_F(TestArgParser, WrongAutoFormat) {
  const char *argv[] = {"dlinear", bad_filename_.c_str(), "--format", "auto"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for file");
}

TEST_F(TestArgParser, Smt2Format) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--format", "smt2"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<std::string>("file"), filename_smt2_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::SMT2);
}

TEST_F(TestArgParser, MpsFormat) {
  const char *argv[] = {"dlinear", filename_mps_.c_str(), "--format", "mps"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_EQ(parser_.get<std::string>("file"), filename_mps_);
  EXPECT_EQ(parser_.get<Config::Format>("format"), Config::Format::MPS);
}

TEST_F(TestArgParser, WrongFormat) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--format", "invalid"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --format");
}

TEST_F(TestArgParser, SkipCheckSat) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--skip-check-sat"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_TRUE(parser_.get<bool>("skip-check-sat"));
}

TEST_F(TestArgParser, WrongSkipCheckSat) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--skip-check-sat", "--produce-models"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --produce-models");
}

TEST_F(TestArgParser, Exhaustive) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--precision", "0"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  auto config = parser_.toConfig();
  EXPECT_DOUBLE_EQ(config.precision(), 0.0);
}

TEST_F(TestArgParser, Silent) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--silent"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  EXPECT_TRUE(parser_.get<bool>("silent"));
}

TEST_F(TestArgParser, WrongSilentWithVerbose) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--silent", "--verbose"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --verbose");
}

TEST_F(TestArgParser, WrongSilentWithQuiet) {
  const char *argv[] = {"dlinear", filename_smt2_.c_str(), "--silent", "--quiet"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --quiet");
}

TEST_F(TestArgParser, In) {
  const char *argv[] = {"dlinear", "--in", "--format", "mps"};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  auto config = parser_.toConfig();
  EXPECT_TRUE(config.read_from_stdin());
}

TEST_F(TestArgParser, WrongInMissingFormat) {
  const char *argv[] = {"dlinear", "--in"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --in");
}

TEST_F(TestArgParser, WrongInAutoFormat) {
  const char *argv[] = {"dlinear", "--in", "--format", "auto"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --in");
}

TEST_F(TestArgParser, VnnlibOnnxFile) {
  const char *argv[] = {"dlinear",     filename_vnnlib_.c_str(), "--format", "vnnlib",
                        "--onnx-file", filename_onnx_.c_str()};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  auto config = parser_.toConfig();
  EXPECT_EQ(config.onnx_file(), filename_onnx_.c_str());
  EXPECT_EQ(config.format(), Config::Format::VNNLIB);
}

TEST_F(TestArgParser, MissingOnnxFile) {
  const char *argv[] = {"dlinear", filename_vnnlib_.c_str(), "--format", "vnnlib"};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --onnx-file");
}

TEST_F(TestArgParser, ImplicitVnnlibFormat) {
  const char *argv[] = {"dlinear", filename_vnnlib_.c_str(), "--onnx-file", filename_onnx_.c_str()};
  parser_.parse(sizeof(argv) / sizeof(argv[0]), argv);
  auto config = parser_.toConfig();
  EXPECT_EQ(config.onnx_file(), filename_onnx_.c_str());
  EXPECT_EQ(config.format(), Config::Format::AUTO);
}

TEST_F(TestArgParser, ImplicitMissingOnnxFile) {
  const char *argv[] = {"dlinear", filename_vnnlib_.c_str()};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --onnx-file");
}

TEST_F(TestArgParser, OnnxFileNotFound) {
  const char *argv[] = {"dlinear", filename_vnnlib_.c_str(), "--onnx-file", non_existing_filename_.c_str()};
  EXPECT_DEATH(parser_.parse(sizeof(argv) / sizeof(argv[0]), argv), "Invalid argument for --onnx-file");
}
