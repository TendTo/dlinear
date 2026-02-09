/******************************************************************************
 * Top contributors (to current version):
 *   Ernesto Casablanca
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#pragma once

#include <optional>
#include <vector>

#include "theory/arith/delta_rational.h"
#include "theory/arith/linear/arithvar.h"
#include "util/dense_map.h"
#include "util/rational.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

namespace exact {

enum class LinResult
{
  LinUnknown,    /* Unknown error */
  LinFeasible,   /* Relaxation is feasible */
  LinInfeasible, /* Relaxation is infeasible/all integer branches closed */
  LinExhausted
};

enum class MipResult
{
  MipUnknown,  /* Unknown error */
};

}

class ExactStatistics
{
 public:
  ExactStatistics(StatisticsRegistry& sr);

  IntStat d_branchMaxDepth;
  IntStat d_branchesMaxOnAVar;

  TimerStat d_gaussianElimConstructTime;
  IntStat d_gaussianElimConstruct;
  AverageStat d_averageGuesses;
};

class NodeLog;
class TreeLog;
class ArithVariables;
class CutInfo;

class ExactSimplex
{
 public:
  /** Is an exact solver (SoPlex or Qsopt_ex) enabled? */
  static bool enabled();

  /**
   * If an exact solver is enabled, creates a lp-based exact solver.
   */
  static ExactSimplex* mkExactSimplexSolver(const ArithVariables& vars,
                                            TreeLog& l,
                                            ExactStatistics& s);

  ExactSimplex() = default;
  virtual ~ExactSimplex() {}

  /** A result is either sat, unsat or unknown.*/
  struct Solution
  {
    DenseSet newBasis;
    DenseMap<DeltaRational> newValues;
    Solution() : newBasis(), newValues() {}
  };

  /* maximum branches allowed on a variable */
  virtual void setBranchingDepth(int bd) = 0;

  /* gets a branching variable */
  virtual ArithVar getBranchVar(const NodeLog& nl) const = 0;

  /**
   * Estimates a double as a Rational using continued fraction expansion that
   * cuts off the estimate once the value is approximately zero.
   * This is designed for removing rounding artifacts.
   */
  virtual std::optional<Rational> estimateWithCFE(double d) const = 0;
  virtual std::optional<Rational> estimateWithCFE(double d,
                                                  const Integer& D) const = 0;

  virtual void tryCut(int nid, CutInfo& cut) = 0;

  virtual std::vector<const CutInfo*> getValidCuts(const NodeLog& node) = 0;

  /* the maximum pivots allowed in a query. */
  virtual void setPivotLimit(int pl) = 0;

  virtual ArithRatPairVec heuristicOptCoeffs() const = 0;

  /** Sets a maximization criteria for the approximate solver.*/
  virtual void setOptCoeffs(const ArithRatPairVec& ref) = 0;

  /* maximum branches allowed on a variable */
  virtual void setBranchOnVariableLimit(int bl) = 0;

  virtual exact::LinResult solveRelaxation() = 0;

  virtual exact::MipResult solveMIP(bool activelyLog) = 0;

  virtual Solution extractMIP() const = 0;

  virtual Solution extractRelaxation() const = 0;
}; /* class ApproximateSimplex */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
