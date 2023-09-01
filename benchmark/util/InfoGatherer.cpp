#include "InfoGatherer.h"

#include <utility>
#include <chrono>

using std::string;

namespace dlinear::benchmark {

InfoGatherer::InfoGatherer(string filename, string solver, const string &precision)
    : config_{}, filename_{std::move(filename)}, solver_{std::move(solver)}, timeout_{0} {
  precision_ = stod(precision);
  config_.mutable_lp_solver().set_from_command_line(GetLPSolver(solver_));
  config_.mutable_precision().set_from_command_line(precision_);
}

InfoGatherer::InfoGatherer(string filename, string solver, const string &precision, uint timeout)
    : config_{}, filename_{std::move(filename)}, solver_{std::move(solver)}, timeout_{timeout} {
  precision_ = stod(precision);
  config_.mutable_lp_solver().set_from_command_line(GetLPSolver(solver_));
  config_.mutable_precision().set_from_command_line(precision_);
}

bool InfoGatherer::run() {
  std::cout << "Running " << filename_ << " with " << solver_ << " and " << precision_ << std::endl;
  // Shared memory to store the results of the child process.
  auto *results = static_cast<shared_results *>(mmap(nullptr, sizeof(shared_results),
                                                     PROT_READ | PROT_WRITE,
                                                     MAP_SHARED | MAP_ANONYMOUS, -1,
                                                     0));
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
  if (intermediate_pid_ == 0) {
    pid_t worker_pid = -1, timer_pid = -1;
    worker_pid = fork();
    if (worker_pid == 0) {
      auto start = std::chrono::high_resolution_clock::now();
      Init();
      GatherInfo(results);
      DeInit();
      auto end = std::chrono::high_resolution_clock::now();
      results->time = std::chrono::duration_cast<std::chrono::seconds>(end - start).count();
      exit(0);
    }
    if (worker_pid == -1) {
      DLINEAR_RUNTIME_ERROR("Failed to fork a worker process.");
    }

    if (timeout_ > 0) {
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
    pid_t pid = wait(&status);
    if (pid == worker_pid) {
      if (timer_pid > 0) kill(timer_pid, SIGKILL);
    } else if (pid == timer_pid) {
      if (worker_pid > 0) kill(worker_pid, SIGKILL);
    } else
      DLINEAR_RUNTIME_ERROR_FMT("Unexpected child process {} exited with {}", pid, status);
    exit(pid == worker_pid ? status : 1);
  }
  if (intermediate_pid_ == -1) {
    DLINEAR_RUNTIME_ERROR("Failed to fork an intermediate process.");
  }
}

bool InfoGatherer::WaitChild() {
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
}

string InfoGatherer::GetSolverName(const Config::LPSolver solver) {
  switch (solver) {
    case Config::SOPLEX:return "soplex";
    case Config::QSOPTEX:return "qsoptex";
    default:DLINEAR_RUNTIME_ERROR_FMT("Unknown solver {}", solver);
  }
}

Config::LPSolver InfoGatherer::GetLPSolver(const string &solver) {
  if (solver == "soplex") {
    return Config::SOPLEX;
  } else if (solver == "qsoptex") {
    return Config::QSOPTEX;
  }
  DLINEAR_RUNTIME_ERROR_FMT("Unknown solver {}", solver);
}

void InfoGatherer::Init() {
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXStart();
    InftyStart(mpq_INFTY, mpq_NINFTY);
  } else if (config_.lp_solver() == Config::SOPLEX) {
    InftyStart(soplex::infinity);
  }
  Expression::InitConstants();
}

void InfoGatherer::DeInit() {
  Expression::DeInitConstants();
  InftyFinish();
  if (config_.lp_solver() == Config::QSOPTEX) {
    qsopt_ex::QSXFinish();
  }
}

void InfoGatherer::GatherInfo(shared_results *results) {
  Smt2Driver smt2_driver{Context{Config{config_}}};
  smt2_driver.set_trace_scanning(false);
  smt2_driver.set_trace_parsing(false);
  smt2_driver.parse_file(filename_);
  results->nAssertions = smt2_driver.context().assertions().size();
  results->isSat = !smt2_driver.context().get_model().empty();
  results->actualPrecision = smt2_driver.actual_precision();
}

std::ostream &operator<<(std::ostream &os, const InfoGatherer &info_gatherer) {
  return os << info_gatherer.filename() << ","
            << info_gatherer.solver() << ","
            << info_gatherer.nAssertions() << ","
            << info_gatherer.precision() << ","
            << "s" << ","
            << info_gatherer.time() << ","
            << info_gatherer.actualPrecision() << ","
            << info_gatherer.isSat();
}

}  // namespace dreal
