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

#include "bound_counts.h"
#include "normal_form.h"
#include "options/arith_options.h"
#include "theory/arith/linear/constraint.h"

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
      d_strict(sr.registerInt("theory::arith::z::approx::strictVar")),
      d_externalAdjustmentPivots(
          sr.registerInt("theory::arith::z::approx::externalAdjustmentPivots")),
      d_deltaResults(sr.registerInt("theory::arith::z::approx::deltaResults")),
      d_maxDelta(sr.registerValue<double>("theory::arith::z::approx::delta")),
      d_precision(sr.registerHistogram<std::size_t>(
          "theory::arith::z::approx::precision")),
      d_refinements(sr.registerHistogram<std::size_t>(
          "theory::arith::z::approx::refinements"))
{
}

ExternalSimplex::ExternalSimplex(SimplexStatistics& s, const Options& o)
    : d_stats(s),
      d_pivotLimit(std::numeric_limits<int>::max()),
      d_maxDepth(std::numeric_limits<int>::max()),
      d_branchLimit(std::numeric_limits<int>::max()),
      d_delta(o.arith.delta),
      d_useDelta(o.arith.delta >= 0)
{
  d_stats.d_pivotLimit.set(d_pivotLimit);
}

void ExternalSimplex::setPivotLimit(const int pl)
{
  Assert(pl >= 0);
  d_pivotLimit = pl;
  d_stats.d_pivotLimit.set(pl);
}
int ExternalSimplex::guessDir(const ArithVariables& vars, ArithVar v)
{
  if (vars.hasUpperBound(v) && !vars.hasLowerBound(v)) return -1;
  if (!vars.hasUpperBound(v) && vars.hasLowerBound(v)) return 1;
  if (!vars.hasUpperBound(v) && !vars.hasLowerBound(v)) return 0;

  const int ubSgn = vars.getUpperBound(v).sgn();
  const int lbSgn = vars.getLowerBound(v).sgn();
  if (ubSgn != 0 && lbSgn == 0) return -1;
  if (ubSgn == 0 && lbSgn != 0) return 1;
  return 1;
}

ArithRatPairVec ExternalSimplex::heuristicOptCoeffs(
    const ArithVariables& vars,
    const std::vector<ArithVar>& rowToArithVar) const
{
  ArithRatPairVec ret;

  // Strategies are guess:
  // 1 simple shared "ceiling" variable: danoint, pk1
  //  x1 >= c, x1 >= tmp1, x1 >= tmp2, ...
  // 1 large row: fixnet, vpm2, pp08a
  //  (+ .......... ) <= c
  // Not yet supported:
  // 1 complex shared "ceiling" variable: opt1217
  //  x1 >= c, x1 >= (+ ..... ), x1 >= (+ ..... )
  //  and all of the ... are the same sign

  // Candidates:
  // 1) Upper and lower bounds are not equal.
  // 2) The variable is not integer
  // 3a) For columns look for a ceiling variable
  // 3B) For rows look for a large row with

  DenseMap<BoundCounts> d_colCandidates;
  DenseMap<uint32_t> d_rowCandidates;

  double sumRowLength = 0.0;
  uint32_t maxRowLength = 0;
  for (ArithVariables::var_iterator vi = vars.var_begin(),
                                    vi_end = vars.var_end();
       vi != vi_end;
       ++vi)
  {
    ArithVar v = *vi;

    if (TraceIsOn("approx-debug"))
    {
      Trace("approx-debug") << v << " ";
      vars.printModel(v, Trace("approx-debug"));
    }

    bool isFreeOrFixed = (vars.hasUpperBound(v) && vars.hasLowerBound(v)
                          && vars.boundsAreEqual(v))
                         || (!vars.hasUpperBound(v) && !vars.hasLowerBound(v));

    if (!isFreeOrFixed)
    {
      if (vars.isAuxiliary(v))
      {
        Polynomial p = Polynomial::parsePolynomial(vars.asNode(v));
        uint32_t len = p.size();
        d_rowCandidates.set(v, len);
        sumRowLength += len;
        maxRowLength = std::max(maxRowLength, len);
      }
      else if (!vars.isInteger(v))
      {
        d_colCandidates.set(v, BoundCounts());
      }
    }
  }

  uint32_t maxCount = 0;
  for (const ArithVar v : rowToArithVar)
  {
    bool lbCap = vars.hasLowerBound(v) && !vars.hasUpperBound(v);
    bool ubCap = !vars.hasLowerBound(v) && vars.hasUpperBound(v);

    if (lbCap || ubCap)
    {
      ConstraintP b = lbCap ? vars.getLowerBoundConstraint(v)
                            : vars.getUpperBoundConstraint(v);

      if (!b->getValue().noninfinitesimalIsZero()) continue;

      Polynomial poly = Polynomial::parsePolynomial(vars.asNode(v));
      if (poly.size() != 2) continue;

      Polynomial::iterator j = poly.begin();
      Monomial first = *j;
      ++j;
      Monomial second = *j;

      const bool firstIsPos = first.constantIsPositive();
      const bool secondIsPos = second.constantIsPositive();

      if (firstIsPos == secondIsPos) continue;

      Monomial pos = firstIsPos == lbCap ? first : second;
      Monomial neg = firstIsPos != lbCap ? first : second;
      // pos >= neg
      VarList p = pos.getVarList();
      VarList n = neg.getVarList();
      if (vars.hasArithVar(p.getNode()))
      {
        ArithVar ap = vars.asArithVar(p.getNode());
        if (d_colCandidates.isKey(ap))
        {
          BoundCounts bc = d_colCandidates.get(ap);
          bc = BoundCounts(bc.lowerBoundCount(), bc.upperBoundCount() + 1);
          maxCount = std::max(maxCount, bc.upperBoundCount());
          d_colCandidates.set(ap, bc);
        }
      }
      if (vars.hasArithVar(n.getNode()))
      {
        ArithVar an = vars.asArithVar(n.getNode());
        if (d_colCandidates.isKey(an))
        {
          BoundCounts bc = d_colCandidates.get(an);
          bc = BoundCounts(bc.lowerBoundCount() + 1, bc.upperBoundCount());
          maxCount = std::max(maxCount, bc.lowerBoundCount());
          d_colCandidates.set(an, bc);
        }
      }
    }
  }

  // Attempt row
  double avgRowLength =
      d_rowCandidates.empty() ? 0.0 : (sumRowLength / d_rowCandidates.size());

  // There is a large row among the candidates
  const double rowLengthReq = (maxRowLength * .9);
  if (maxRowLength >= 10.0 * avgRowLength)
  {
    for (ArithVar r : d_rowCandidates)
    {
      uint32_t len = d_rowCandidates[r];

      int dir = guessDir(vars, r);
      if (len >= rowLengthReq)
      {
        if (TraceIsOn("approx-debug"))
        {
          Trace("approx-debug") << "high row " << r << " " << len << " "
                                << avgRowLength << " " << dir << std::endl;
          vars.printModel(r, Trace("approx-debug"));
        }
        ret.emplace_back(r, Rational(dir));
      }
    }
  }

  // Attempt columns (guessAColCandidate)
  if (maxCount >= 4)
  {
    for (ArithVar c : d_colCandidates)
    {
      BoundCounts bc = d_colCandidates[c];

      int dir = guessDir(vars, c);
      double ubScore = static_cast<double>(bc.upperBoundCount()) / maxCount;
      double lbScore = static_cast<double>(bc.lowerBoundCount()) / maxCount;
      if (ubScore >= .9 || lbScore >= .9)
      {
        if (TraceIsOn("approx-debug"))
        {
          Trace("approx-debug")
              << "high col " << c << " " << bc << " " << ubScore << " "
              << lbScore << " " << dir << std::endl;
          vars.printModel(c, Trace("approx-debug"));
        }
        ret.emplace_back(c, Rational(c));
      }
    }
  }

  return ret;
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