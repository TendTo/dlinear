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

#include "cut_log.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/linear/arithvar.h"
#include "util/dense_map.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {
namespace external {

enum LinResult
{
  LinUnknown,    /* Unknown error */
  LinFeasible,   /* Relaxation is feasible */
  LinInfeasible, /* Relaxation is infeasible/all integer branches closed */
  LinExhausted
};

enum MipResult
{
  MipUnknown,        /* Unknown error */
  MipBingo,          /* Integer feasible */
  MipClosed,         /* All integer branches closed */
  BranchesExhausted, /* Exhausted number of branches */
  PivotsExhauasted,  /* Exhausted number of pivots */
  ExecExhausted      /* Exhausted total operations */
};
std::ostream& operator<<(std::ostream& out, MipResult res);

/**
 * Store a solution obtained from the external simplex solver.
 * It will contain all the information needed to attempt to apply the solution
 * to the current tableau, and to extract a model if the solution is integer
 * feasible.
 * Note that only one between `newBasis` and `newNonBasis` will be populated,
 * depending on the heuristic the external simplex solver wants the internal
 * tableau to use.
 * Moreover, only one between `linResult` and `mipResult` may differ from
 * `Unknown`, depending on the type of solution obtained from the external
 * simplex solver.
 */
struct Solution
{
  DenseSet newBasis;
  DenseSet newNonBasis;
  DenseMap<DeltaRational> newValues;
  LinResult linResult;
  MipResult mipResult;
  Solution()
      : newBasis(),
        newNonBasis(),
        newValues(),
        linResult(LinUnknown),
        mipResult(MipUnknown)
  {
  }
};

class SimplexStatistics
{
 public:
  explicit SimplexStatistics(StatisticsRegistry& sr);

  IntStat d_branchMaxDepth;
  IntStat d_branchesMaxOnAVar;

  TimerStat d_gaussianElimConstructTime;
  IntStat d_gaussianElimConstruct;
  AverageStat d_averageGuesses;

  IntStat d_pivotLimit;
  IntStat d_externalSimplexType;
  IntStat d_strict;
  IntStat d_externalAdjustmentPivots;
  IntStat d_delta;
  HistogramStat<std::size_t> d_precision;
  HistogramStat<std::size_t> d_refinements;
};

class ExternalSimplex
{
 public:
  explicit ExternalSimplex(SimplexStatistics& s);
  virtual ~ExternalSimplex() = default;

  /* maximum branches allowed on a variable */
  void setBranchingDepth(int bd);

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
  void setPivotLimit(int pl);

  virtual ArithRatPairVec heuristicOptCoeffs() const = 0;

  /** Sets a maximization criteria for the approximate solver.*/
  virtual void setOptCoeffs(const ArithRatPairVec& ref) = 0;

  /* maximum branches allowed on a variable */
  void setBranchOnVariableLimit(int bl);

  virtual LinResult solveRelaxation() = 0;

  virtual MipResult solveMIP(bool activelyLog) = 0;

  virtual Solution extractMIP() = 0;

  virtual Solution extractRelaxation() = 0;

 protected:
  SimplexStatistics d_stats;
  /* the maximum pivots allowed in a query. */
  int d_pivotLimit;

  /* maxmimum branching depth allowed.*/
  int d_maxDepth;

  /* maximum branches allowed on a variable */
  int d_branchLimit;
}; /* class ApproximateSimplex */

}  // namespace external
}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
