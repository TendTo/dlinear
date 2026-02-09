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

#include "theory/arith/delta_rational.h"
#include "util/dense_map.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {
namespace external {

enum LinResult {
  LinUnknown,  /* Unknown error */
  LinFeasible, /* Relaxation is feasible */
  LinInfeasible,   /* Relaxation is infeasible/all integer branches closed */
  LinExhausted
};

enum MipResult {
  MipUnknown,  /* Unknown error */
  MipBingo,    /* Integer feasible */
  MipClosed,   /* All integer branches closed */
  BranchesExhausted, /* Exhausted number of branches */
  PivotsExhauasted,  /* Exhausted number of pivots */
  ExecExhausted      /* Exhausted total operations */
};
std::ostream& operator<<(std::ostream& out, MipResult res);

struct Solution
{
  DenseSet newBasis;
  DenseMap<DeltaRational> newValues;
  Solution() : newBasis(), newValues() {}
};

}  // namespace external
}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
