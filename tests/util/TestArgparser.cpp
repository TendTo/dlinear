#include <gtest/gtest.h>
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;

TEST(TestArgParser, Contructor) {
    EXPECT_NO_THROW(ArgParser parser{});
}

TEST(TestArgParser, DefaultValues) {
    ArgParser parser{};
    const int argc = 1;
    const char *argv[argc] = {"dlinear"};
    parser.parse(argc, argv);
    ASSERT_EQ(parser.get<int>("verbosity"), 0);
    ASSERT_DOUBLE_EQ(parser.get<double>("precision"), 1e-6);
    ASSERT_FALSE(parser.get<bool>("produce-models"));
    ASSERT_EQ(parser.get<u_int64_t>("random-seed"), 0ul);
}

TEST(TestArgParser, ParseVerbosity) {
    ArgParser parser{};
    const int argc = 3;
    const char *argv[argc] = {"dlinear", "--verbosity", "1"};
    parser.parse(argc, argv);
    ASSERT_EQ(parser.get<int>("verbosity"), 1);
}

TEST(TestArgParser, ParsePrecision) {
    ArgParser parser{};
    const int argc = 3;
    const char *argv[argc] = {"dlinear", "--precision", "2.1"};
    parser.parse(argc, argv);
    ASSERT_DOUBLE_EQ(parser.get<double>("precision"), 2.1);
}

TEST(TestArgParser, ParseProduceModels) {
    ArgParser parser{};
    const int argc = 2;
    const char *argv[argc] = {"dlinear", "--produce-models"};
    parser.parse(argc, argv);
    ASSERT_TRUE(parser.get<bool>("produce-models"));
}

TEST(TestArgParser, ParseRandomSeed) {
    ArgParser parser{};
    const int argc = 3;
    const char *argv[argc] = {"dlinear", "--random-seed", "10"};
    parser.parse(argc, argv);
    ASSERT_EQ(parser.get<u_int64_t>("random-seed"), 10ul);
}

TEST(TestArgParser, ParseAll) {
    ArgParser parser{};
    const int argc = 8;
    const char *argv[argc] = {"dlinear",
                              "--verbosity", "2",
                              "--precision", "3.1",
                              "--produce-models",
                              "--random-seed", "11"};
    parser.parse(argc, argv);
    ASSERT_EQ(parser.get<int>("verbosity"), 2);
    ASSERT_DOUBLE_EQ(parser.get<double>("precision"), 3.1);
    ASSERT_TRUE(parser.get<bool>("produce-models"));
    ASSERT_EQ(parser.get<u_int64_t>("random-seed"), 11ul);
}
