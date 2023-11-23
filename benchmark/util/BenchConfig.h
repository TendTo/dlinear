/**
 * @file Config.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Config class.
 * Used to store the configuration of the program.
 *
 * Simple dataclass to store the configuration of the program.
 * It is generated from @ref ArgParser.
 */
#pragma once

#include <iostream>
#include <string>
#include <vector>

#include "dlinear/util/exception.h"

namespace dlinear::benchmark {

class BenchConfig {
 public:
  BenchConfig() = default;
  BenchConfig(const BenchConfig &) = default;
  BenchConfig(BenchConfig &&) = default;
  BenchConfig &operator=(const BenchConfig &) = default;
  BenchConfig &operator=(BenchConfig &&) = default;
  ~BenchConfig() = default;

  [[nodiscard]] bool isDryRun() const { return isDryRun_; }
  [[nodiscard]] bool filesProvided() const { return !files_.empty(); }
  [[nodiscard]] const std::vector<std::string> &files() const { return files_; }
  [[nodiscard]] std::vector<std::string> copyFiles() const { return files_; }
  [[nodiscard]] uint timeout() const { return timeout_; }
  [[nodiscard]] const std::string &config_file() const { return config_file_; }
  [[nodiscard]] const std::string &path() const { return path_; }
  [[nodiscard]] const std::string &extension() const { return extension_; }
  [[nodiscard]] const std::string &output_file() const { return output_file_; }
  [[nodiscard]] int simplex_sat_phase() const { return simplex_sat_phase_; }

  void setDryRun(bool isDryRun) { isDryRun_ = isDryRun; }
  void setFiles(const std::vector<std::string> &files) { files_ = files; }
  void setTimeout(uint timeout) { timeout_ = timeout; }
  void setConfigFile(const std::string &configFile) { config_file_ = configFile; }
  void setPath(const std::string &path) { path_ = path; }
  void setFiles(std::vector<std::string> &&files) { files_ = std::move(files); }
  void setConfigFile(std::string &&configFile) { config_file_ = std::move(configFile); }
  void setPath(std::string &&path) { path_ = std::move(path); }
  void setExtension(const std::string &extension) { extension_ = extension; }
  void setOutputFile(const std::string &outputFile) { output_file_ = outputFile; }
  void setSimplexSatPhase(int simplexSatPhase) { simplex_sat_phase_ = simplexSatPhase; }

 private:
  std::string config_file_;
  std::string path_;
  std::string extension_;
  std::vector<std::string> files_;
  std::string output_file_;
  bool isDryRun_{};
  uint timeout_{};
  int simplex_sat_phase_{};

  friend std::ostream &operator<<(std::ostream &os, const BenchConfig &config);
};

}  // namespace dlinear::benchmark
