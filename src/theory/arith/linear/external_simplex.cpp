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
    : d_branchMaxDepth(
          sr.registerInt("theory::arith::z::approx::branchMaxDepth")),
      d_branchesMaxOnAVar(
          sr.registerInt("theory::arith::z::approx::branchesMaxOnAVar")),
      d_gaussianElimConstructTime(sr.registerTimer(
          "theory::arith::z::approx::gaussianElimConstruct::time")),
      d_gaussianElimConstruct(sr.registerInt(
          "theory::arith::z::approx::gaussianElimConstruct::calls")),
      d_averageGuesses(
          sr.registerAverage("theory::arith::z::approx::averageGuesses")),
      d_pivotLimit(sr.registerInt("theory::arith::z::approx::pivotLimit")),
      d_externalSimplexType(
          sr.registerInt("theory::arith::z::approx::externalSimplexType")),
      d_precision(sr.registerHistogram<std::size_t>(
          "theory::arith::z::approx::precision")),
      d_refinements(sr.registerHistogram<std::size_t>(
          "theory::arith::z::approx::refinements"))
{
}

ExternalSimplex::ExternalSimplex(SimplexStatistics& s)
    : d_stats(s),
      d_pivotLimit(std::numeric_limits<int>::max()),
      d_maxDepth(std::numeric_limits<int>::max()),
      d_branchLimit(std::numeric_limits<int>::max())
{
  d_stats.d_pivotLimit.set(d_pivotLimit);
}

void ExternalSimplex::setPivotLimit(const int pl)
{
  Assert(pl >= 0);
  d_pivotLimit = pl;
  d_stats.d_pivotLimit.set(pl);
}

void ExternalSimplex::setBranchingDepth(int bd)
{
  Assert(bd >= 0);
  d_maxDepth = bd;
}

void ExternalSimplex::setBranchOnVariableLimit(int bl)
{
  Assert(bl >= 0);
  d_branchLimit = bl;
}

}  // namespace external
}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal