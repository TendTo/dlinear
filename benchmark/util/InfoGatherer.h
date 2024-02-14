#pragma once

#include <sys/mman.h>
#include <sys/wait.h>

#include <cstdio>
#include <iostream>
#include <regex>
#include <sstream>

#include "dlinear/solver/Solver.h"
#include "dlinear/util/Config.h"

namespace dlinear::benchmark {

struct shared_results {
  uint nAssertions;
  bool isSat;
  double actualPrecision;
  uint time;
  double smt_solver_time;
  double parser_time;
};

class InfoGatherer {
 public:
  InfoGatherer() = delete;
  InfoGatherer(Config config, uint timeout);

  bool run();

  [[nodiscard]] std::string filename() const { return config_.filename(); }
  [[nodiscard]] std::string solver() const { return (std::ostringstream{} << config_.lp_solver()).str(); }
  [[nodiscard]] double precision() const { return precision_; }
  [[nodiscard]] double actualPrecision() const { return actualPrecision_; }
  [[nodiscard]] uint nAssertions() const { return nAssertions_; }
  [[nodiscard]] bool isSat() const { return isSat_; }
  [[nodiscard]] uint timeout() const { return timeout_; }
  [[nodiscard]] uint time() const { return time_; }
  [[nodiscard]] double smt_solver_time() const { return smt_solver_time_; }
  [[nodiscard]] double parser_time() const { return parser_time_; }
  [[nodiscard]] int simplex_phase() const { return config_.simplex_sat_phase(); }
  [[nodiscard]] char lp_mode() const {
    switch (config_.lp_mode()) {
      case Config::LPMode::AUTO:
        return config_.lp_solver() == Config::LPSolver::QSOPTEX ? 'P' : 'H';
      case Config::LPMode::PURE_PRECISION_BOOSTING:
        return 'P';
      case Config::LPMode::PURE_ITERATIVE_REFINEMENT:
        return 'I';
      case Config::LPMode::HYBRID:
        return 'H';
      default:
        DLINEAR_UNREACHABLE();
    }
  }

 private:
  Config config_;
  double precision_{0.0};
  double actualPrecision_{0.0};
  uint nAssertions_{0};
  bool isSat_{false};
  pid_t intermediate_pid_{-1};
  uint timeout_{0};
  uint time_{0};
  double smt_solver_time_{0.0};
  double parser_time_{0.0};

  void GatherInfo(shared_results *results);
  void StartIntermediateProcess(shared_results *results);
  bool WaitChild() const;
  void ParseResults(shared_results *results);
};

std::ostream &operator<<(std::ostream &os, const InfoGatherer &info_gatherer);

}  // namespace dlinear::benchmark
