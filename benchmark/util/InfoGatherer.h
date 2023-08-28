#ifndef DLINEAR5_BENCHMARK_UTIL_INFOGATHERER_H_
#define DLINEAR5_BENCHMARK_UTIL_INFOGATHERER_H_

#include <sys/mman.h>
#include <sys/wait.h>

#include <cstdio>
#include <iostream>
#include <regex>

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/smt2/Driver.h"
#include "dlinear/smt2/run.h"
#include "dlinear/util/Config.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/util/infty.h"

namespace dlinear::benchmark {

struct shared_results {
  uint32_t nAssertions;
  bool isSat;
  double actualPrecision;
  uint32_t time;
};

class InfoGatherer {
 public:
  InfoGatherer() = delete;
  InfoGatherer(std::string filename, std::string solver, const std::string &precision);
  InfoGatherer(std::string filename, std::string solver, const std::string &precision, uint32_t timeout);
  bool run();

  [[nodiscard]] const std::string &filename() const { return filename_; }
  [[nodiscard]] const std::string &solver() const { return solver_; }
  [[nodiscard]] double precision() const { return precision_; }
  [[nodiscard]] double actualPrecision() const { return actualPrecision_; }
  [[nodiscard]] uint32_t nAssertions() const { return nAssertions_; }
  [[nodiscard]] bool isSat() const { return isSat_; }
  [[nodiscard]] uint32_t timeout() const { return timeout_; }
  [[nodiscard]] uint32_t time() const { return time_; }

 private:
  Config config_;
  const std::string filename_;
  const std::string solver_;
  double precision_{0.0};
  double actualPrecision_{0.0};
  uint32_t nAssertions_{0};
  bool isSat_{false};
  pid_t intermediate_pid_{-1};
  uint32_t timeout_{0};
  uint32_t time_{0};

  std::string GetSolverName(const Config::LPSolver solver);
  Config::LPSolver GetLPSolver(const std::string &solver);
  void Init();
  void DeInit();
  void GatherInfo(shared_results *results);
  void StartIntermediateProcess(shared_results *results);
  bool WaitChild();
  void ParseResults(shared_results *results);
};

std::ostream &operator<<(std::ostream &os, const InfoGatherer &info_gatherer);

}  // namespace dlinear::benchmark

#endif //DLINEAR5_BENCHMARK_UTIL_INFOGATHERER_H_
