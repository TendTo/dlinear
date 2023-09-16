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
 */
#pragma once

#include <map>
#include <string>
#include <vector>

namespace dlinear::benchmark {

class ConfigFileReader {
 public:
  explicit ConfigFileReader(const std::string &configFile) : configFile_(configFile) {
    parameters_[solver_key_] = std::vector<std::string>{};
    parameters_[precision_key_] = std::vector<std::string>{};
  }
  explicit ConfigFileReader(std::string &&configFile) : configFile_(std::move(configFile)) {}
  ~ConfigFileReader() = default;
  ConfigFileReader(const ConfigFileReader &) = delete;
  ConfigFileReader(ConfigFileReader &&) = delete;
  ConfigFileReader &operator=(const ConfigFileReader &) = delete;
  ConfigFileReader &operator=(ConfigFileReader &&) = delete;

  /**
   * Parse the configuration file.
   * All line are expected in the format
   * parameter = value1 [value2 ...]
   */
  void read();
  [[nodiscard]] const std::vector<std::string> &solvers() { return parameters_[solver_key_]; }
  [[nodiscard]] const std::vector<std::string> &precisions() { return parameters_[precision_key_]; }

 private:
  const std::string solver_key_{"solver"};
  const std::string precision_key_{"precision"};
  const std::string configFile_;
  std::map<std::string, std::vector<std::string>>
      parameters_;  ///< Map containing all the configuration loaded from the configuration file.

  friend std::ostream &operator<<(std::ostream &os, const ConfigFileReader &configFileReader);
};

}  // namespace dlinear::benchmark
