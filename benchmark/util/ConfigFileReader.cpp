/**
 * @file ConfigFileReader.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "ConfigFileReader.h"

#include <fstream>
#include <regex>

#include "dlinear/util/exception.h"

using std::string;

namespace dlinear::benchmark {

namespace {
Config::LPSolver GetLPSolver(const string &solver) {
  if (solver == "soplex") {
    return Config::LPSolver::SOPLEX;
  } else if (solver == "qsoptex") {
    return Config::LPSolver::QSOPTEX;
  }
  DLINEAR_RUNTIME_ERROR_FMT("Unknown solver {}", solver);
}

Config::LPMode GetLPMode(const string &mode) {
  if (mode == "auto") {
    return Config::LPMode::AUTO;
  } else if (mode == "pure-precision-boosting") {
    return Config::LPMode::PURE_PRECISION_BOOSTING;
  } else if (mode == "pure-iterative-refinement") {
    return Config::LPMode::PURE_ITERATIVE_REFINEMENT;
  } else if (mode == "hybrid") {
    return Config::LPMode::HYBRID;
  }
  DLINEAR_RUNTIME_ERROR_FMT("Unknown LP mode {}", mode);
}
}  // namespace

void ConfigFileReader::read() {
  std::ifstream conf_file{configFile_};
  if (!conf_file.is_open()) DLINEAR_RUNTIME_ERROR_FMT("File '{}' could not be opened", configFile_);

  const std::regex conf_regex("^(\\w+) *= *(.+?) *$");
  std::smatch conf_matches;
  string line;

  while (conf_file) {
    std::getline(conf_file, line);

    if (std::regex_match(line, conf_matches, conf_regex)) {
      if (conf_matches.size() != 3) continue;

      string parameter = conf_matches[1].str();
      std::stringstream values{conf_matches[2].str()};
      string value;
      while (values >> value) parameters_[parameter].push_back(value);
    }
  }
}

std::vector<Config::LPSolver> ConfigFileReader::solvers() const {
  std::vector<Config::LPSolver> solvers;
  solvers.reserve(parameters_.at(solver_key_).size());
  std::transform(parameters_.at(solver_key_).begin(), parameters_.at(solver_key_).end(), std::back_inserter(solvers),
                 GetLPSolver);
  return solvers;
}

std::vector<double> ConfigFileReader::precisions() const {
  std::vector<double> precisions;
  precisions.reserve(parameters_.at(precision_key_).size());
  std::transform(parameters_.at(precision_key_).begin(), parameters_.at(precision_key_).end(),
                 std::back_inserter(precisions), [](const string &precision) { return std::stod(precision); });
  return precisions;
}

std::vector<Config::LPMode> ConfigFileReader::lp_modes() const {
  std::vector<Config::LPMode> lp_modes;
  lp_modes.reserve(parameters_.at(lp_modes_key_).size());
  std::transform(parameters_.at(lp_modes_key_).begin(), parameters_.at(lp_modes_key_).end(),
                 std::back_inserter(lp_modes), GetLPMode);
  return lp_modes;
}

std::ostream &operator<<(std::ostream &os, const ConfigFileReader &configFileReader) {
  os << "ConfigFileReader{"
     << "parameters_= {" << std::endl;
  for (const auto &[key, values] : configFileReader.parameters_) {
    os << key << " : ";
    for (const auto &c : values) {
      os << c << " ";
    }
    os << std::endl;
  }
  os << "}";
  return os;
}
}  // namespace dlinear::benchmark
