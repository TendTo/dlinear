#include "InfoGatherer.h"

#include <chrono>
#include <utility>

namespace dlinear::benchmark {

InfoGatherer::InfoGatherer(Config config, uint timeout)
    : config_{std::move(config)}, precision_{config_.precision()}, timeout_{timeout} {}

bool InfoGatherer::run() {
  std::cout << "Running " << config_.filename() << " with " << config_.lp_solver() << " and " << precision_
            << std::endl;
  // Shared memory to store the results of the child process.
  auto *results = static_cast<shared_results *>(
      mmap(nullptr, sizeof(shared_results), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0));
  // Fork an intermediate process to fork a worker process and a timer process.
  StartIntermediateProcess(results);
  // Wait for the child process to finish and get the exit status
  bool res = WaitChild();
  if (res) ParseResults(results);
  // Unmap the shared memory.
  munmap(results, sizeof(shared_results));
  // Return true if the child process exits with 0, meaning no error has
  // occurred
  return res;
}

void InfoGatherer::StartIntermediateProcess(shared_results *results) {
  intermediate_pid_ = fork();
  if (intermediate_pid_ == 0) {  // Intermediate process. It will fork a worker process and a timer process.
    pid_t worker_pid = -1, timer_pid = -1;
    worker_pid = fork();
    if (worker_pid == 0) {  // Worker process. It will run the solver.
      GatherInfo(results);
      exit(0);
    }
    if (worker_pid == -1) {
      DLINEAR_RUNTIME_ERROR("Failed to fork a worker process.");
    }

    if (timeout_ > 0) {  // Timer process. It will kill the worker process if it runs for too long.
      timer_pid = fork();
      if (timer_pid == 0) {
        sleep(timeout_);
        exit(0);
      }
      if (timer_pid == -1) {
        DLINEAR_RUNTIME_ERROR("Failed to fork a timer process.");
      }
    }

    int status;
    pid_t pid = wait(&status);  // wait for the fastest process to finish
    if (pid == worker_pid) {    // Kill the other process
      if (timer_pid > 0) kill(timer_pid, SIGKILL);
    } else if (pid == timer_pid) {
      if (worker_pid > 0) kill(worker_pid, SIGKILL);
    } else
      DLINEAR_RUNTIME_ERROR_FMT("Unexpected child process {} exited with {}", pid, status);
    // Exit with the exit status of the worker process or 1 if the worker process timed out
    exit(pid == worker_pid ? status : 1);
  }
  if (intermediate_pid_ == -1) {
    DLINEAR_RUNTIME_ERROR("Failed to fork an intermediate process.");
  }
}

bool InfoGatherer::WaitChild() const {
  int status;
  int pid = waitpid(intermediate_pid_, &status, 0);
  if (pid == -1) {
    DLINEAR_RUNTIME_ERROR("Failed to wait for the worker process.");
  }
  return status == 0;
}

void InfoGatherer::ParseResults(shared_results *results) {
  nAssertions_ = results->nAssertions;
  isSat_ = results->isSat;
  actualPrecision_ = results->actualPrecision;
  time_ = results->time;
  smt_solver_time_ = results->smt_solver_time;

  parser_time_ = results->parser_time;
}

void InfoGatherer::GatherInfo(shared_results *results) {
  auto start = std::chrono::high_resolution_clock::now();
  SmtSolver solver{config_};
  auto res = solver.CheckSat();

  results->nAssertions = res.n_assertions;
  results->isSat = res.is_sat();
  results->actualPrecision = res.actual_precision.get_d();
  results->parser_time = res.parser_stats.timer().seconds();
  results->theory_solver_time = res.theory_stats.timer().seconds();
  results->bound_preprocessor_time = res.preprocessor_stats.timer().seconds();
  results->sat_solver_time = res.sat_stats.timer().seconds();
  results->smt_solver_time = res.smt_solver_timer.seconds();

  auto end = std::chrono::high_resolution_clock::now();
  results->time = std::chrono::duration_cast<std::chrono::seconds>(end - start).count();
}

std::ostream &operator<<(std::ostream &os, const InfoGatherer &info_gatherer) {
  return os << info_gatherer.filename() << ","         // Filename
            << info_gatherer.solver() << ","           // Solver
            << info_gatherer.nAssertions() << ","      // Number of assertions
            << info_gatherer.precision() << ","        // Precision
            << info_gatherer.simplex_phase() << ","    // Simplex Phase
            << info_gatherer.lp_mode() << ","          // LP Mode
            << "s,"                                    // Time unit
            << info_gatherer.time() << ","             // Time
            << info_gatherer.parser_time() << ","      // Parser time
            << info_gatherer.smt_solver_time() << ","  // SMT solver time
            << info_gatherer.actualPrecision() << ","  // Actual precision
            << info_gatherer.isSat();                  // Result
}

}  // namespace dlinear::benchmark
