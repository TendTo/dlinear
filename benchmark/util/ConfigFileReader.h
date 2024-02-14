/**
 * @file ConfigFileReader.h
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 * @brief Read the configuration file for the benchmark.
 *
 * The configuration file is expected to be in the format
 * parameter = value1 [value2 ...]
 * where parameter is one of the following:
 * - solver
 * - precision
 * - lp_mode
 */
#pragma once

#include <map>
#include <string>
#include <utility>
#include <vector>

#include "dlinear/util/Config.h"

namespace dlinear::benchmark {

class ConfigFileReader {
 public:
  explicit ConfigFileReader(std::string configFile) : configFile_(std::move(configFile)) {
    parameters_[solver_key_] = std::vector<std::string>{};
    parameters_[precision_key_] = std::vector<std::string>{};
  }

  /**
   * Parse the configuration file.
   *
   * All line are expected in the format
   * parameter = value1 [value2 ...]
   * The result is stored in the @ref parameters_ map.
   */
  void read();
  /**
   * Get the solvers indicated in the configuration file.
   * @return vector containing the solvers indicated in the configuration file.
   */
  [[nodiscard]] std::vector<Config::LPSolver> solvers() const;
  /**
   * Get the precisions indicated in the configuration file.
   * @return vector containing the precisions indicated in the configuration file.
   */
  [[nodiscard]] std::vector<double> precisions() const;
  /**
   * Get the lp_modes indicated in the configuration file.
   * @return vector containing the lp_modes indicated in the configuration file.
   */
  [[nodiscard]] std::vector<Config::LPMode> lp_modes() const;

 private:
  const std::string solver_key_{"solver"};
  const std::string precision_key_{"precision"};
  const std::string lp_modes_key_{"lp_mode"};
  const std::string configFile_;
  std::map<std::string, std::vector<std::string>>
      parameters_;  ///< Map containing all the configuration loaded from the configuration file.

  friend std::ostream &operator<<(std::ostream &os, const ConfigFileReader &configFileReader);
};

}  // namespace dlinear::benchmark
