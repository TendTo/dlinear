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
#include "theory/arith/linear/external_simplex.h"

#include <ostream>

namespace cvc5::internal {
namespace theory {
namespace arith::linear {
namespace external {

std::ostream& operator<<(std::ostream& out, MipResult res)
{
  switch (res)
  {
    case MipUnknown: out << "MipUnknown"; break;
    case MipBingo: out << "MipBingo"; break;
    case MipClosed: out << "MipClosed"; break;
    case BranchesExhausted: out << "BranchesExhausted"; break;
    case PivotsExhauasted: out << "PivotsExhauasted"; break;
    case ExecExhausted: out << "ExecExhausted"; break;
    default: out << "Unexpected Mip Value!"; break;
  }
  return out;
}

SimplexStatistics::SimplexStatistics(StatisticsRegistry& sr)
    : d_branchMaxDepth(sr.registerInt("z::approx::branchMaxDepth")),
      d_branchesMaxOnAVar(sr.registerInt("z::approx::branchesMaxOnAVar")),
      d_gaussianElimConstructTime(
          sr.registerTimer("z::approx::gaussianElimConstruct::time")),
      d_gaussianElimConstruct(
          sr.registerInt("z::approx::gaussianElimConstruct::calls")),
      d_averageGuesses(sr.registerAverage("z::approx::averageGuesses"))
{
}

}  // namespace external
}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal