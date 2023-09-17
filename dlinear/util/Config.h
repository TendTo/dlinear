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

#include "dlinear/util/OptionValue.hpp"

#define DLINEAR_DEFAULT_PRECISION 9.999999999999996e-4
#define DLINEAR_DEFAULT_FORMAT dlinear::Config::Format::AUTO
#define DLINEAR_DEFAULT_READ_FROM_STDIN false
#define DLINEAR_DEFAULT_EXHAUSTIVE false
#define DLINEAR_DEFAULT_PRODUCE_MODELS false
#define DLINEAR_DEFAULT_USE_POLYTOPE false
#define DLINEAR_DEFAULT_USE_POLYTOPE_IN_FORALL false
#define DLINEAR_DEFAULT_USE_WORKLIST_FIXPOINT false
#define DLINEAR_DEFAULT_USE_LOCAL_OPTIMIZATION false
#define DLINEAR_DEFAULT_CONTINUOUS_OUTPUT false
#define DLINEAR_DEFAULT_WITH_TIMINGS false
#define DLINEAR_DEFAULT_LP_SOLVER dlinear::Config::LPSolver::QSOPTEX
#define DLINEAR_DEFAULT_SIMPLEX_SAT_PHASE 1
#define DLINEAR_DEFAULT_VERBOSE_SIMPLEX 0
#define DLINEAR_DEFAULT_VERBOSE_DLINEAR 2
#define DLINEAR_DEFAULT_NUMBER_OF_JOBS 1u
#define DLINEAR_DEFAULT_STACK_LEFT_BOX_FIRST false
#define DLINEAR_DEFAULT_NLOPTF_TO_REL 1e-6
#define DLINEAR_DEFAULT_NLOPTF_TO_ABS 1e-6
#define DLINEAR_DEFAULT_NLOPT_MAX_EVAL 100u
#define DLINEAR_DEFAULT_NLOPT_MAX_TIME 0.01
#define DLINEAR_DEFAULT_SAT_PHASE dlinear::Config::SatDefaultPhase::JeroslowWang
#define DLINEAR_DEFAULT_RANDOM_SEED 0u
#define DLINEAR_DEFAULT_DEBUG_SCANNING false
#define DLINEAR_DEFAULT_DEBUG_PARSING false

namespace dlinear {

class Config {
 public:
  enum LPSolver {
    SOPLEX = 0,
    QSOPTEX = 1,
  };
  enum class SatDefaultPhase {
    False = 0,
    True = 1,
    JeroslowWang = 2,  ///< Default option
    RandomInitialPhase = 3
  };
  enum class Format {
    AUTO = 0,
    SMT2 = 1,
    MPS = 2,
  };

  Config() = default;
  explicit Config(const std::string filename);
  explicit Config(bool read_from_stdin);

  /** Input file name */
  [[nodiscard]] const std::string &filename() const { return filename_.get(); }

  /** Mutable input file name */
  [[nodiscard]] OptionValue<std::string> &mutable_filename() { return filename_; }

  /** Input file name extension */
  [[nodiscard]] std::string filename_extension() const;

  /** Input format */
  [[nodiscard]] Format format() const { return format_.get(); }

  /** Mutable input format */
  [[nodiscard]] OptionValue<Format> &mutable_format() { return format_; }

  /** Whether to read from stdin */
  [[nodiscard]] bool read_from_stdin() const { return read_from_stdin_.get(); }

  /** Mutable option on whether to read from stdin */
  [[nodiscard]] OptionValue<bool> &mutable_read_from_stdin() { return read_from_stdin_; }

  /** Precision option */
  [[nodiscard]] double precision() const { return precision_.get(); }

  /** Mutable precision option */
  [[nodiscard]] OptionValue<double> &mutable_precision() { return precision_; }

  /** Produce models option */
  [[nodiscard]] bool produce_models() const { return produce_models_.get(); }

  /** Mutable produce models option */
  [[nodiscard]] OptionValue<bool> &mutable_produce_models() { return produce_models_; }

  /** Whether it uses polytope contractors or not */
  [[nodiscard]] bool use_polytope() const { return use_polytope_.get(); }

  /** Mutable option on whether to use polytope */
  [[nodiscard]] OptionValue<bool> &mutable_use_polytope() { return use_polytope_; }

  /** Whether it uses polytope contractors inside forall contractors */
  [[nodiscard]] bool use_polytope_in_forall() const { return use_polytope_in_forall_.get(); }

  /** Mutable option on whether to use polytope inside forall */
  [[nodiscard]] OptionValue<bool> &mutable_use_polytope_in_forall() { return use_polytope_in_forall_; }

  /** Whether the worklist-fixpoint algorithm is used */
  [[nodiscard]] bool use_worklist_fixpoint() const { return use_worklist_fixpoint_.get(); }

  /** Mutable option on whether to use worklist-fixpoint algorithm */
  [[nodiscard]] OptionValue<bool> &mutable_use_worklist_fixpoint() { return use_worklist_fixpoint_; }

  /** Whether the local optimization algorithm is used in exist-forall problems */
  [[nodiscard]] bool use_local_optimization() const { return use_local_optimization_.get(); }

  /** Mutable option on whether to use local optimization in exist-forall problems */
  [[nodiscard]] OptionValue<bool> &mutable_use_local_optimization() { return use_local_optimization_; }

  /** Which phase of simplex to use for linear satisfiability problems */
  [[nodiscard]] int simplex_sat_phase() const { return simplex_sat_phase_.get(); }

  /** Mutable option on which phase of simplex to use for linear satisfiability problems */
  [[nodiscard]] OptionValue<int> &mutable_simplex_sat_phase() { return simplex_sat_phase_; }

  /** Which LP solver to use */
  [[nodiscard]] LPSolver lp_solver() const { return lp_solver_.get(); }

  /** Mutable option on which LP solver to use */
  [[nodiscard]] OptionValue<LPSolver> &mutable_lp_solver() { return lp_solver_; }

  /** Verbosity level for simplex. */
  [[nodiscard]] int verbose_simplex() const { return verbose_simplex_.get(); }

  /** Mutable verbosity level for simplex. */
  [[nodiscard]] OptionValue<int> &mutable_verbose_simplex() { return verbose_simplex_; }

  /** Dlinear verbosity level. */
  [[nodiscard]] int verbose_dlinear() const { return verbose_dlinear_.get(); }

  /** Mutable dlinear verbosity level. */
  [[nodiscard]] OptionValue<int> &mutable_verbose_dlinear() { return verbose_dlinear_; }

  /** Whether to output partial results continuously, as and when available */
  [[nodiscard]] bool continuous_output() const { return continuous_output_.get(); }

  /** Mutable option on whether to output partial results continuously, as and when available */
  [[nodiscard]] OptionValue<bool> &mutable_continuous_output() { return continuous_output_; }

  /** Whether to output timings alongside the results */
  [[nodiscard]] bool with_timings() const { return with_timings_.get(); }

  /** Mutable option on whether to output timings alongside the results */
  [[nodiscard]] OptionValue<bool> &mutable_with_timings() { return with_timings_; }

  /** Number of parallel jobs */
  [[nodiscard]] uint number_of_jobs() const { return number_of_jobs_.get(); }

  /** Mutable number of parallel jobs */
  [[nodiscard]] OptionValue<uint> &mutable_number_of_jobs() { return number_of_jobs_; }

  /** Whether the ICP algorithm stacks the left box first after branching */
  [[nodiscard]] bool stack_left_box_first() const { return stack_left_box_first_.get(); }

  /** Mutable option on whether the ICP algorithm stacks the left box first after branching */
  [[nodiscard]] OptionValue<bool> &mutable_stack_left_box_first() { return stack_left_box_first_; }

  /** Relative tolerance on function value in NLopt */
  [[nodiscard]] double nlopt_ftol_rel() const { return nlopt_ftol_rel_.get(); }

  /** Mutable relative tolerance on function value in NLopt */
  [[nodiscard]] OptionValue<double> &mutable_nlopt_ftol_rel() { return nlopt_ftol_rel_; }

  /** Absolute tolerance on function value in NLopt */
  [[nodiscard]] double nlopt_ftol_abs() const { return nlopt_ftol_abs_.get(); }

  /** Mutable absolute tolerance on function value in NLopt */
  [[nodiscard]] OptionValue<double> &mutable_nlopt_ftol_abs() { return nlopt_ftol_abs_; }

  /** Number of maximum function evaluations allowed in NLopt */
  [[nodiscard]] uint nlopt_maxeval() const { return nlopt_maxeval_.get(); }

  /** Mutable number of maximum function evaluations allowed in NLopt */
  [[nodiscard]] OptionValue<uint> &mutable_nlopt_maxeval() { return nlopt_maxeval_; }

  /** Maxtime in NLopt */
  [[nodiscard]] double nlopt_maxtime() const { return nlopt_maxtime_.get(); }

  /** Mutable maxtime in NLopt */
  [[nodiscard]] OptionValue<double> &mutable_nlopt_maxtime() { return nlopt_maxtime_; }

  /** Default phase for SAT solver */
  [[nodiscard]] SatDefaultPhase sat_default_phase() const { return sat_default_phase_.get(); }

  /** Mutable default phase for SAT solver */
  [[nodiscard]] OptionValue<SatDefaultPhase> &mutable_sat_default_phase() { return sat_default_phase_; }

  /** Random seed */
  [[nodiscard]] uint random_seed() const { return random_seed_.get(); }

  /** Mutable random seed */
  [[nodiscard]] OptionValue<uint> &mutable_random_seed() { return random_seed_; }

  /** Debug scanning */
  [[nodiscard]] bool debug_scanning() const { return debug_scanning_.get(); }

  /** Mutable debug scanning */
  [[nodiscard]] OptionValue<bool> &mutable_debug_scanning() { return debug_scanning_; }

  /** Debug parsing */
  [[nodiscard]] bool debug_parsing() const { return debug_parsing_.get(); }

  /** Mutable debug parsing */
  [[nodiscard]] OptionValue<bool> &mutable_debug_parsing() { return debug_parsing_; }

  static constexpr double kDefaultPrecision{DLINEAR_DEFAULT_PRECISION};  // pred(floor("0.001"))
  static constexpr double kDefaultNloptFtolRel{DLINEAR_DEFAULT_NLOPTF_TO_REL};
  static constexpr double kDefaultNloptFtolAbs{DLINEAR_DEFAULT_NLOPTF_TO_ABS};
  static constexpr int kDefaultNloptMaxEval{DLINEAR_DEFAULT_NLOPT_MAX_EVAL};
  static constexpr double kDefaultNloptMaxTime{DLINEAR_DEFAULT_NLOPT_MAX_TIME};

 private:
  OptionValue<std::string> filename_{""};
  OptionValue<Format> format_{DLINEAR_DEFAULT_FORMAT};
  OptionValue<bool> read_from_stdin_{DLINEAR_DEFAULT_READ_FROM_STDIN};
  OptionValue<double> precision_{kDefaultPrecision};
  OptionValue<bool> produce_models_{DLINEAR_DEFAULT_PRODUCE_MODELS};
  OptionValue<bool> use_polytope_{DLINEAR_DEFAULT_USE_POLYTOPE};
  OptionValue<bool> use_polytope_in_forall_{DLINEAR_DEFAULT_USE_POLYTOPE_IN_FORALL};
  OptionValue<bool> use_worklist_fixpoint_{DLINEAR_DEFAULT_USE_WORKLIST_FIXPOINT};
  OptionValue<bool> use_local_optimization_{DLINEAR_DEFAULT_USE_LOCAL_OPTIMIZATION};
  OptionValue<int> simplex_sat_phase_{DLINEAR_DEFAULT_SIMPLEX_SAT_PHASE};
  OptionValue<LPSolver> lp_solver_{DLINEAR_DEFAULT_LP_SOLVER};
  OptionValue<int> verbose_simplex_{DLINEAR_DEFAULT_VERBOSE_SIMPLEX};
  OptionValue<int> verbose_dlinear_{DLINEAR_DEFAULT_VERBOSE_DLINEAR};
  OptionValue<bool> continuous_output_{DLINEAR_DEFAULT_CONTINUOUS_OUTPUT};
  OptionValue<bool> with_timings_{DLINEAR_DEFAULT_WITH_TIMINGS};
  OptionValue<uint> number_of_jobs_{DLINEAR_DEFAULT_NUMBER_OF_JOBS};
  OptionValue<bool> stack_left_box_first_{DLINEAR_DEFAULT_STACK_LEFT_BOX_FIRST};
  OptionValue<bool> debug_scanning_{DLINEAR_DEFAULT_DEBUG_SCANNING};
  OptionValue<bool> debug_parsing_{DLINEAR_DEFAULT_DEBUG_PARSING};
  OptionValue<uint> random_seed_{DLINEAR_DEFAULT_RANDOM_SEED};

  /**
   * NLopt options (stopping criteria)
   *
   * These options are used when we use NLopt in refining
   * counterexamples via local-optimization. The following
   * descriptions are from
   * https://nlopt.readthedocs.io/en/latest/NLopt_Reference/#stopping-criteria
   *
   * Set relative tolerance on function value: stop when an
   * optimization step (or an estimate of the optimum) changes the
   * objective function value by less than tol multiplied by the
   * absolute value of the function value. (If there is any chance
   * that your optimum function value is close to zero, you might want
   * to set an absolute tolerance with nlopt_set_ftol_abs as well.)
   * Criterion is disabled if tol is non-positive.
   */
  OptionValue<double> nlopt_ftol_rel_{kDefaultNloptFtolRel};

  /**
   * Set absolute tolerance on function value: stop when an
   * optimization step (or an estimate of the optimum) changes the
   * function value by less than tol. Criterion is disabled if tol is
   * non-positive.
   */
  OptionValue<double> nlopt_ftol_abs_{kDefaultNloptFtolAbs};

  /**
   * Stop when the number of function evaluations exceeds
   * maxeval. (This is not a strict maximum: the number of function
   * evaluations may exceed maxeval slightly, depending upon the
   * algorithm.) Criterion is disabled if maxeval is non-positive.
   */
  OptionValue<uint> nlopt_maxeval_{kDefaultNloptMaxEval};

  /**
   * Stop when the optimization time (in seconds) exceeds
   * maxtime. (This is not a strict maximum: the time may exceed
   * maxtime slightly, depending upon the algorithm and on how slow
   * your function evaluation is.) Criterion is disabled if maxtime is
   * non-positive.
   */
  OptionValue<double> nlopt_maxtime_{kDefaultNloptMaxTime};

  /**
   * Default initial phase for PICOSAT:
   *
   * 0 = false
   * 1 = true
   * 2 = Jeroslow-Wang (default)
   * 3 = random initial phase
   */
  OptionValue<SatDefaultPhase> sat_default_phase_{DLINEAR_DEFAULT_SAT_PHASE};

  friend std::ostream &operator<<(std::ostream &os, const Config &config);
  friend std::ostream &operator<<(std::ostream &os, const Config::SatDefaultPhase &sat_default_phase);
};

}  // namespace dlinear
