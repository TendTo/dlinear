/**
 * @file MainProgram.cpp
 * @author dlinear
 * @date 12 Aug 2023
 * @copyright 2023 dlinear
 * Brief description
 *
 * Long Description
 */

#include "MainProgram.h"

namespace dlinear {

void MainProgram::Init() {
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXStart();
    InftyStart(qsopt_ex::mpq_INFTY, qsopt_ex::mpq_NINFTY);
  } else {
    DREAL_ASSERT(config_.lp_solver() == Config::SOPLEX);
#if HAVE_SOPLEX
    InftyStart(soplex::infinity);
#else
    throw DREAL_RUNTIME_ERROR("SoPlex not enabled at compile time");
#endif
  }
  Expression::InitConstants();
}

void MainProgram::DeInit() {
  Expression::DeInitConstants();
  InftyFinish();
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXFinish();
  }
}

int MainProgram::Run() {
  if (config_.filename().empty()) {
    PrintUsage();
    return 1;
  }
}

MainProgram::MainProgram(int argc, const char **argv) {
  ArgParser parser{QSopt_ex_repository_status(), soplex::getGitHash()};
  parser.parse(argc, argv);
  config_ = parser.toConfig();
}

int MainProgram::Run() {
  if (opt_.isSet("--help")) {
    return 0;
  }
  if (opt_.isSet("--version")) {
    cout << "dLinear " << get_version_string() << endl;
    return 0;
  } else {
    cerr << "dLinear " << get_version_string() << endl;
  }
  if (!is_options_all_valid_) {
    return 1;
  }
  ExtractOptions();
  string filename;
  if (!args_.empty()) {
    filename = *args_[0];
    if (filename.empty()) {
      PrintUsage();
      return 1;
    }
  }
  if (!opt_.isSet("--in") && !file_exists(filename)) {
    cerr << "File not found: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  const string extension{get_extension(filename)};
  string format_opt;
  opt_.get("--format")->getString(format_opt);
  if (format_opt == "smt2" ||
      (format_opt == "auto" && (extension == "smt2" || opt_.isSet("--in")))) {
    Init();
    RunSmt2(filename, config_, opt_.isSet("--debug-scanning"),
            opt_.isSet("--debug-parsing"));
    DeInit();
  } else if (format_opt == "dr" ||
      (format_opt == "auto" && extension == "dr")) {
    throw DREAL_RUNTIME_ERROR("Format 'dr' not supported");
#if 0
    Init();
    RunDr(filename, config_, opt_.isSet("--debug-scanning"),
          opt_.isSet("--debug-parsing"));
    DeInit();
#endif
  } else {
    cerr << "Unknown extension: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  return 0;
}
} // dlinear