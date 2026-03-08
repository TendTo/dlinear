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
#include "theory/arith/linear/external_simplex.h"
#include "util/dense_map.h"
#include "util/rational.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class NodeLog;
class TreeLog;
class ArithVariables;
class CutInfo;

class ExactSimplex : public external::ExternalSimplex
{
 public:
  using ExternalSimplex::ExternalSimplex;

  /** Is an exact solver (SoPlex or Qsopt_ex) enabled? */
  static bool enabled();

  /**
   * If an exact solver is enabled, creates a lp-based exact solver.
   */
  static ExternalSimplex* mkExactSoplexSolver(const ArithVariables& vars,
                                              TreeLog& l,
                                              external::SimplexStatistics& s,
                                              bool useStrict);
  /**
   * If an exact solver is enabled, creates a lp-based exact solver.
   */
  static ExternalSimplex* mkExactQsoptexSolver(const ArithVariables& vars,
                                               TreeLog& l,
                                               external::SimplexStatistics& s,
                                               bool useStrict);

}; /* class ApproximateSimplex */

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
