/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew V. Teylu, Gereon Kremer
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
#include <math.h>

#include <cfloat>
#include <cmath>
#include <unordered_map>
#include <unordered_set>

#include "base/cvc5config.h"
#include "base/output.h"
#include "proof/eager_proof_generator.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/cut_log.h"
#include "theory/arith/linear/exact_simplex.h"
#include "theory/arith/linear/matrix.h"
#include "theory/arith/linear/normal_form.h"
#include "util/statistics_registry.h"

#ifdef CVC5_USE_SOPLEX
#include <soplex.h>

#include "theory/arith/linear/partial_model.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

using soplex::SoPlex;

class ExactSoplex2 : public ExactSimplex
{
 public:
  ExactSoplex2(const ArithVariables& v, TreeLog& l, external::SimplexStatistics& s);

  external::LinResult solveRelaxation() override;
  external::Solution extractRelaxation() override
  {
    return extractSolution(false);
  }

  ArithRatPairVec heuristicOptCoeffs() const override;

  external::MipResult solveMIP(bool al) override;
  external::Solution extractMIP() override { return extractSolution(true); }
  void setOptCoeffs(const ArithRatPairVec& ref) override;
  std::vector<const CutInfo*> getValidCuts(const NodeLog& nodes) override;
  ArithVar getBranchVar(const NodeLog& con) const override;

  static void printSoplexStatus(int status, std::ostream& out);

  virtual void setPivotLimit(int pl) override;

  virtual void setBranchingDepth(int bd) override;

  virtual void setBranchOnVariableLimit(int bl) override;

  virtual std::optional<Rational> estimateWithCFE(double d) const override;
  virtual std::optional<Rational> estimateWithCFE(
      double d, const Integer& D) const override;

 private:
  void extractVarValue(ArithVar v,
                       soplex::SPxSolverBase<double>::VarStatus varStatus,
                       mpq_class&& value,
                       external::Solution& sol) const;
  void printSolution(const external::Solution& sol) const;

  soplex::Rational varToLb(ArithVar v) const;
  soplex::Rational varToUb(ArithVar v) const;
  bool hasStrictBound(ArithVar v) const;
  bool hasStrictLb(ArithVar v) const;
  bool hasStrictUB(ArithVar v) const;

  external::Solution extractSolution(bool mip);
  int guessDir(ArithVar v) const;

  // get this stuff out of here
  void tryCut(int nid, CutInfo& cut) override;

  ArithVar _getArithVar(int nid, int M, int ind) const;
  ArithVar getArithVarFromRow(int nid, int ind) const
  {
    if (ind >= 0)
    {
      const NodeLog& nl = d_log.getNode(nid);
      return nl.lookupRowId(ind);
    }
    return ARITHVAR_SENTINEL;
  }

  // virtual void mapRowId(int nid, int ind, ArithVar v){
  //   NodeLog& nl = d_log.getNode(nid);
  //   nl.mapRowId(ind, v);
  // }
  // virtual void applyRowsDeleted(int nid, const RowsDeleted& rd){
  //   NodeLog& nl = d_log.getNode(nid);
  //   nl.applyRowsDeleted(rd);
  // }

  ArithVar getArithVarFromStructural(int ind) const
  {
    if (ind >= 0)
    {
      unsigned u = (unsigned)ind;
      if (u < d_colToArithVar.size())
      {
        return d_colToArithVar[u];
      }
    }
    return ARITHVAR_SENTINEL;
  }

  double sumInfeasibilities(/* glp_prob */ soplex::SoPlex& prob,
                            bool mip) const;

  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static constexpr double SMALL_FIXED_DELTA =
      std::numeric_limits<double>::epsilon();

 private:
  const ArithVariables& d_vars;
  TreeLog& d_log;

  /* the maximum pivots allowed in a query. */
  int d_pivotLimit;

  /* maximum branches allowed on a variable */
  int d_branchLimit;

  /* maxmimum branching depth allowed.*/
  int d_maxDepth;

  /* Default denominator for diophatine approximation, 2^{26} .*/
  static constexpr uint64_t s_defaultMaxDenom = (1 << 26);

  // glp_prob* d_inputProb; /* a copy of the input prob */
  // glp_prob* d_realProb;  /* a copy of the real relaxation output */
  // glp_prob* d_mipProb;   /* a copy of the integer prob */
  SoPlex d_spx;
  std::unordered_map<int, bool> d_strict_rows;

  DenseMap<std::size_t> d_colIndices;

  // NodeLog::RowIdMap d_rootRowIds;
  std::vector<ArithVar> d_rowToArithVar;
  // DenseMap<ArithVar> d_rowToArithVar;
  std::vector<ArithVar> d_colToArithVar;

  bool d_solvedRelaxation;
  bool d_solvedMIP;
};

void ExactSoplex2::setPivotLimit(int pl)
{
  Assert(pl >= 0);
  d_pivotLimit = pl;
}

void ExactSoplex2::setBranchingDepth(int bd)
{
  Assert(bd >= 0);
  d_maxDepth = bd;
}

void ExactSoplex2::setBranchOnVariableLimit(int bl)
{
  Assert(bl >= 0);
  d_branchLimit = bl;
}

ExactSoplex2::ExactSoplex2(const ArithVariables& var,
                           TreeLog& l,
                           external::SimplexStatistics& s)
    : ExactSimplex(s),
      d_vars(var),
      d_log(l),
      d_pivotLimit(std::numeric_limits<int>::max()),
      d_branchLimit(std::numeric_limits<int>::max()),
      d_maxDepth(std::numeric_limits<int>::max()),
      d_solvedRelaxation(false),
      d_solvedMIP(false)
{
  d_spx.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);
  d_spx.setIntParam(SoPlex::SIMPLIFIER, SoPlex::SIMPLIFIER_OFF);
  d_spx.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_PRIMAL);
  d_spx.setIntParam(SoPlex::VERBOSITY, SoPlex::VERBOSITY_ERROR);
  d_spx.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
  d_spx.setIntParam(SoPlex::PRICER, SoPlex::PRICER_AUTO);
  // d_spx.setIntParam(SoPlex::RATIOTESTER, SoPlex::RATIOTESTER_BOUNDFLIPPING);
  d_spx.setIntParam(SoPlex::ITERLIMIT, d_pivotLimit);

  d_spx.setRealParam(SoPlex::FEASTOL, 0.0);
  d_spx.setRealParam(SoPlex::OPTTOL, 0.0);

  if (TraceIsOn("approx-debug"))
  {
    d_spx.setIntParam(SoPlex::VERBOSITY, SoPlex::VERBOSITY_DEBUG);
  }

  // d_spx.clearLPRational();
  d_rowToArithVar.reserve(d_vars.getNumberOfVariables() / 2);
  d_colToArithVar.reserve(d_vars.getNumberOfVariables() / 2);

  // Assign each variable to a row and column variable as it appears in the
  // input
  for (auto vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end;
       ++vi)
  {
    const ArithVar v = *vi;
    if (d_vars.isAuxiliary(v))
    {
      d_rowToArithVar.emplace_back(v);
      Trace("approx") << "Row vars: " << v << "<->"
                      << d_rowToArithVar.size() - 1 << std::endl;
    }
    else
    {
      d_colToArithVar.emplace_back(v);
      d_colIndices.set(v, d_colIndices.size());
      Trace("approx") << "Col vars: " << v << "<->" << d_colIndices.size() - 1
                      << std::endl;
    }
  }
  Assert(!d_rowToArithVar.empty());
  Assert(!d_colToArithVar.empty());

  // The number of cols must accommodate for the non-aux variables as well as
  // the additional strict variable t
  // Todo: better estimation of the number of rows
  soplex::LPRowSetRational rows(static_cast<int>(d_rowToArithVar.size()));
  soplex::LPColSetRational cols(static_cast<int>(d_colToArithVar.size()));

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (ArithVar v : d_rowToArithVar)
  {
    assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    // std::cout << d_vars.asNode(v).getName() << "\n\n";

    soplex::DSVectorRational vec(static_cast<int>(p.size()) + 1);

    for (Polynomial::iterator j = p.begin(), end = p.end(); j != end; ++j)
    {
      const Monomial& mono = *j;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      int colIndex = static_cast<int>(d_colIndices[av]);
      // std::cout << d_vars.asNode(av).getName() << " => " << colIndex << "\n";

      vec.add(colIndex, constant.getValue().getValue().get_mpq_t());
    }

    soplex::Rational lb = -soplex::infinity;
    soplex::Rational ub = soplex::infinity;
    if (d_vars.hasLowerBound(v))
    {
      lb = hasStrictLb(v) ? varToLb(v) + SMALL_FIXED_DELTA : varToLb(v);
    }
    if (d_vars.hasUpperBound(v))
    {
      ub = hasStrictUB(v) ? varToUb(v) - SMALL_FIXED_DELTA : varToUb(v);
    }
    rows.add({lb, vec, ub});
  }

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  for (ArithVar v : d_colToArithVar)
  {
    assert(!d_vars.isAuxiliary(v));

    if (TraceIsOn("approx-debug"))
    {
      Trace("approx-debug") << v << " ";
      d_vars.printModel(v, Trace("approx-debug"));
    }

    soplex::Rational lb = -soplex::infinity;
    soplex::Rational ub = soplex::infinity;
    if (d_vars.hasLowerBound(v))
    {
      lb = hasStrictLb(v) ? varToLb(v) + SMALL_FIXED_DELTA : varToLb(v);
    }
    if (d_vars.hasUpperBound(v))
    {
      ub = hasStrictUB(v) ? varToUb(v) - SMALL_FIXED_DELTA : varToUb(v);
    }
    cols.add({1.0, soplex::DSVectorRational(), ub, lb});
  }

  // Add both columns and rows to the LP
  d_spx.addColsRational(cols);
  d_spx.addRowsRational(rows);

  d_spx.writeFileRational(
      "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file.lp");
}

soplex::Rational ExactSoplex2::varToLb(const ArithVar v) const
{
  if (d_vars.hasLowerBound(v))
  {
    return d_vars.getLowerBound(v)
        .getNoninfinitesimalPart()
        .getValue()
        .get_mpq_t();
  }
  return -soplex::infinity;
}

soplex::Rational ExactSoplex2::varToUb(const ArithVar v) const
{
  if (d_vars.hasUpperBound(v))
  {
    return d_vars.getUpperBound(v)
        .getNoninfinitesimalPart()
        .getValue()
        .get_mpq_t();
  }
  return soplex::infinity;
}

bool ExactSoplex2::hasStrictBound(const ArithVar v) const
{
  return hasStrictLb(v) || hasStrictUB(v);
}

bool ExactSoplex2::hasStrictUB(const ArithVar v) const
{
  return d_vars.hasUpperBound(v)
         && !d_vars.getUpperBound(v).getInfinitesimalPart().isZero();
}

bool ExactSoplex2::hasStrictLb(ArithVar v) const
{
  return d_vars.hasLowerBound(v)
         && !d_vars.getLowerBound(v).getInfinitesimalPart().isZero();
}

int ExactSoplex2::guessDir(const ArithVar v) const
{
  if (d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)) return -1;
  if (!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)) return 1;
  if (!d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)) return 0;

  const int ubSgn = d_vars.getUpperBound(v).sgn();
  const int lbSgn = d_vars.getLowerBound(v).sgn();

  if (ubSgn != 0 && lbSgn == 0) return -1;
  if (ubSgn == 0 && lbSgn != 0) return 1;

  return 1;
}

ArithRatPairVec ExactSoplex2::heuristicOptCoeffs() const
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
  for (auto vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end;
       ++vi)
  {
    ArithVar v = *vi;

    if (TraceIsOn("approx-debug"))
    {
      Trace("approx-debug") << v << " ";
      d_vars.printModel(v, Trace("approx-debug"));
    }

    const bool hasLb = d_vars.hasLowerBound(v);
    const bool hasUb = d_vars.hasUpperBound(v);
    // Variable is not fixed nor free
    if ((hasLb || hasUb) && (!hasLb || !hasUb || !d_vars.boundsAreEqual(v)))
    {
      if (d_vars.isAuxiliary(v))
      {
        Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
        uint32_t len = p.size();
        d_rowCandidates.set(v, len);
        sumRowLength += len;
        maxRowLength = std::max(maxRowLength, len);
      }
      else if (!d_vars.isInteger(v))
      {
        d_colCandidates.set(v, BoundCounts());
      }
    }
  }

  uint32_t maxCount = 0;
  for (const ArithVar v : d_rowToArithVar)
  {
    bool lbCap = d_vars.hasLowerBound(v) && !d_vars.hasUpperBound(v);
    bool ubCap = !d_vars.hasLowerBound(v) && d_vars.hasUpperBound(v);

    if (lbCap || ubCap)
    {
      ConstraintP b = lbCap ? d_vars.getLowerBoundConstraint(v)
                            : d_vars.getUpperBoundConstraint(v);

      if (!(b->getValue()).noninfinitesimalIsZero()) continue;

      Polynomial poly = Polynomial::parsePolynomial(d_vars.asNode(v));
      if (poly.size() != 2) continue;

      Polynomial::iterator j = poly.begin();
      Monomial first = *j;
      ++j;
      Monomial second = *j;

      bool firstIsPos = first.constantIsPositive();
      bool secondIsPos = second.constantIsPositive();

      if (firstIsPos == secondIsPos) continue;

      Monomial pos = firstIsPos == lbCap ? first : second;
      Monomial neg = firstIsPos != lbCap ? first : second;
      // pos >= neg
      VarList p = pos.getVarList();
      VarList n = neg.getVarList();
      if (d_vars.hasArithVar(p.getNode()))
      {
        ArithVar ap = d_vars.asArithVar(p.getNode());
        if (d_colCandidates.isKey(ap))
        {
          BoundCounts bc = d_colCandidates.get(ap);
          bc = BoundCounts(bc.lowerBoundCount(), bc.upperBoundCount() + 1);
          maxCount = std::max(maxCount, bc.upperBoundCount());
          d_colCandidates.set(ap, bc);
        }
      }
      if (d_vars.hasArithVar(n.getNode()))
      {
        ArithVar an = d_vars.asArithVar(n.getNode());
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
  double avgRowLength = d_rowCandidates.size() >= 1
                            ? (sumRowLength / d_rowCandidates.size())
                            : 0.0;

  // There is a large row among the candidates
  bool guessARowCandidate = maxRowLength >= (10.0 * avgRowLength);

  double rowLengthReq = (maxRowLength * .9);

  if (guessARowCandidate)
  {
    for (ArithVar r : d_rowCandidates)
    {
      uint32_t len = d_rowCandidates[r];

      int dir = guessDir(r);
      if (len >= rowLengthReq)
      {
        if (TraceIsOn("approx-debug"))
        {
          Trace("approx-debug") << "high row " << r << " " << len << " "
                                << avgRowLength << " " << dir << std::endl;
          d_vars.printModel(r, Trace("approx-debug"));
        }
        ret.push_back(ArithRatPair(r, Rational(dir)));
      }
    }
  }

  // Attempt columns
  bool guessAColCandidate = maxCount >= 4;
  if (guessAColCandidate)
  {
    for (ArithVar c : d_colCandidates)
    {
      BoundCounts bc = d_colCandidates[c];

      int dir = guessDir(c);
      double ubScore = double(bc.upperBoundCount()) / maxCount;
      double lbScore = double(bc.lowerBoundCount()) / maxCount;
      if (ubScore >= .9 || lbScore >= .9)
      {
        if (TraceIsOn("approx-debug"))
        {
          Trace("approx-debug")
              << "high col " << c << " " << bc << " " << ubScore << " "
              << lbScore << " " << dir << std::endl;
          d_vars.printModel(c, Trace("approx-debug"));
        }
        ret.push_back(ArithRatPair(c, Rational(c)));
      }
    }
  }

  return ret;
}

void ExactSoplex2::setOptCoeffs(const ArithRatPairVec& ref)
{
  DenseMap<mpq_class> nbCoeffs;

  for (auto i = ref.begin(), iend = ref.end(); i != iend; ++i)
  {
    ArithVar v = (*i).first;
    const Rational& q = (*i).second;

    if (d_vars.isAuxiliary(v))
    {
      // replace the variable by its definition and multiply by q
      Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
      Polynomial pq = p * q;

      for (Polynomial::iterator j = pq.begin(), jend = pq.end(); j != jend; ++j)
      {
        const Monomial& mono = *j;
        const Constant& constant = mono.getConstant();
        const VarList& variable = mono.getVarList();

        Node n = variable.getNode();

        Assert(d_vars.hasArithVar(n));
        ArithVar av = d_vars.asArithVar(n);
        int colIndex = d_colIndices[av];
        mpq_class coeff = constant.getValue().getValue();
        if (!nbCoeffs.isKey(colIndex))
        {
          nbCoeffs.set(colIndex, 0.0);
        }
        nbCoeffs.set(colIndex, nbCoeffs[colIndex] + coeff);
      }
    }
    else
    {
      int colIndex = d_colIndices[v];
      double coeff = q.getDouble();
      if (!nbCoeffs.isKey(colIndex))
      {
        nbCoeffs.set(colIndex, 0.0);
      }
      nbCoeffs.set(colIndex, nbCoeffs[colIndex] + coeff);
    }
  }
  for (auto ci = nbCoeffs.begin(), ciend = nbCoeffs.end(); ci != ciend; ++ci)
  {
    Index colIndex = *ci;
    mpq_class coeff = nbCoeffs[colIndex];
    d_spx.changeObjRational(colIndex, soplex::Rational{coeff.get_mpq_t()});
  }
}

/*
 * rough strategy:
 *  real relaxation
 *   try approximate real optimization of error function
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 *  check integer solution
 *   try approximate mixed integer problem
 *   stop at the first feasible point
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 */

void ExactSoplex2::printSoplexStatus(int status, std::ostream& out)
{
  using SpxStatus = soplex::SPxSolverBase<double>::Status;
  switch (status)
  {
    case SpxStatus::OPTIMAL: out << "SOPLEX_OPT" << std::endl; break;
    case SpxStatus::OPTIMAL_UNSCALED_VIOLATIONS:
      out << "SOPLEX_OPT_VIOLATIONS" << std::endl;
      break;
    case SpxStatus::INFEASIBLE: out << "SOPLEX_INFEAS" << std::endl; break;
    case SpxStatus::SINGULAR: out << "SOPLEX_SINGULAR" << std::endl; break;
    case SpxStatus::UNBOUNDED: out << "SOPLEX_UNBND" << std::endl; break;
    case SpxStatus::UNKNOWN: out << "SOPLEX_UNKNOWN" << std::endl; break;
    case SpxStatus::ERROR: out << "SOPLEX_ERROR" << std::endl; break;
    case SpxStatus::ABORT_TIME: out << "SOPLEX_ABORT_TIME" << std::endl; break;
    case SpxStatus::ABORT_CYCLING:
      out << "SOPLEX_ABORT_CYCLING" << std::endl;
      break;
    case SpxStatus::ABORT_ITER: out << "SOPLEX_ABORT_ITER" << std::endl; break;
    case SpxStatus::ABORT_VALUE:
      out << "SOPLEX_ABORT_VALUE" << std::endl;
      break;
    default: out << "Status unknown" << std::endl; break;
  }
}

void ExactSoplex2::extractVarValue(
    const ArithVar v,
    const soplex::SPxSolverBase<double>::VarStatus varStatus,
    mpq_class&& value,
    external::Solution& sol) const
{
  using VarStatus = soplex::SPxSolverBase<double>::VarStatus;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

  switch (varStatus)
  {
    case VarStatus::BASIC:
      newBasis.add(v);
      if (d_vars.hasLowerBound(v)
          && d_vars.getLowerBound(v).getNoninfinitesimalPart() >= value)
      {
        newValues.set(v, d_vars.getLowerBound(v));
      }
      else if (d_vars.hasUpperBound(v)
               && d_vars.getUpperBound(v).getNoninfinitesimalPart() <= value)
      {
        newValues.set(v, d_vars.getUpperBound(v));
      }
      else
      {
        newValues.set(v, DeltaRational(value));
      }
      Assert(!d_vars.hasLowerBound(v)
             || d_vars.getLowerBound(v) <= newValues.get(v));
      Assert(!d_vars.hasUpperBound(v)
             || d_vars.getUpperBound(v) >= newValues.get(v));
      break;
    case VarStatus::ON_LOWER:
    case VarStatus::FIXED:  // No need to handle the fixed case differently
      Trace("approx-debug") << "non-basic lb" << std::endl;
      newValues.set(v, d_vars.getLowerBound(v));
      break;
    case VarStatus::ON_UPPER:
      Trace("approx-debug") << "non-basic ub" << std::endl;
      newValues.set(v, d_vars.getUpperBound(v));
      break;
    case VarStatus::ZERO:
      Trace("approx-debug") << "non-basic zero" << std::endl;
      newValues.set(v, DeltaRational(0));
      break;
    default: newValues.set(v, DeltaRational(value));
  }
}

std::ostream& operator<<(std::ostream& out, const soplex::VectorRational& v)
{
  out << "[\n";
  for (int i = 0; i < v.dim(); i++)
  {
    if (!v[i].is_zero()) out << i << " =>" << v[i] << "\n";
  }
  return out << "\n]";
}

#if 0  // For debug
void dumpProblem(soplex::SoPlex& d_spx)
{
  if (d_spx.hasSol())
  {
    soplex::VectorRational primal(d_spx.numCols());
    d_spx.getPrimalRational(primal);
    std::cout << "primal: " << primal << std::endl;
  }
  if (d_spx.hasSol())
  {
    soplex::VectorRational dual(d_spx.numRows());
    d_spx.getDualRational(dual);
    std::cout << "dual: " << dual << std::endl;
  }
  if (d_spx.hasDualFarkas())
  {
    soplex::VectorRational dualRay(d_spx.numRows());
    d_spx.getDualFarkasRational(dualRay);
    std::cout << "dual ray: " << dualRay << std::endl;
  }
  if (d_spx.hasPrimalRay())
  {
    soplex::VectorRational primalRay(d_spx.numCols());
    d_spx.getPrimalRayRational(primalRay);
    std::cout << "primal ray: " << primalRay << std::endl;
  }
  try
  {
    soplex::Rational colValue;
    d_spx.getColActivityRational(0, colValue);
    std::cout << "col 0: " << colValue << std::endl;
  }
  catch (const std::exception&)
  {
  }
  try
  {
    soplex::Rational rowValue;
    d_spx.getRowActivityRational(0, rowValue);
    std::cout << "row 0: " << rowValue << std::endl;
  }
  catch (const std::exception&)
  {
  }
}
#endif

external::Solution ExactSoplex2::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);

  external::Solution sol;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

#if 0  // For debug
  static int id = 0;

  d_spx.writeFile(("/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file"
                   + std::to_string(id) + ".lp")
                      .c_str());
  d_spx.writeFile(("/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file"
                   + std::to_string(id) + ".mps")
                      .c_str());
  id++;

  // std::cout << "Basis status: " << d_spx.basisStatus() << std::endl;
#endif

  // TODO: reimplement this for mip
  // glp_prob* prob = mip ? d_mipProb : d_realProb;

  if (d_spx.status() == soplex::SPxSolverBase<double>::Status::OPTIMAL
      || d_spx.status() == soplex::SPxSolverBase<double>::Status::UNBOUNDED)
  {
    Assert(d_spx.hasSol());
    // Feasible solution
    soplex::VectorRational primal(d_spx.numCols());
    const bool getPrimalSuccess = d_spx.getPrimalRational(primal);
    Assert(getPrimalSuccess);

    // Get the primal solution for the cols
    for (int colIdx = 0; colIdx < d_spx.numCols(); colIdx++)
    {
      const ArithVar v = d_colToArithVar.at(colIdx);
      extractVarValue(v,
                      d_spx.basisColStatus(colIdx),
                      mpq_class{primal[colIdx].backend().data()},
                      sol);
    }

    // Get the row activity for the rows
    soplex::Rational rowValue;
    for (int rowIdx = 0; rowIdx < d_spx.numRows(); rowIdx++)
    {
      const ArithVar v = d_rowToArithVar.at(rowIdx);
      d_spx.getRowActivityRational(rowIdx, rowValue);
      extractVarValue(v,
                      d_spx.basisRowStatus(rowIdx),
                      mpq_class{rowValue.backend().data()},
                      sol);
    }
  }
  else if (d_spx.status() == soplex::SPxSolverBase<double>::Status::INFEASIBLE)
  {
    // Infeasible solution
    Assert(d_spx.hasDualFarkas());
    soplex::VectorRational dualRay(d_spx.numRows());
    const bool getDualRaySuccess = d_spx.getDualFarkasRational(dualRay);
    Assert(getDualRaySuccess);

    // Get the last dual solution for the rows
    for (int rowIdx = 0; rowIdx < d_spx.numRows(); rowIdx++)
    {
      const ArithVar v = d_rowToArithVar.at(rowIdx);
      extractVarValue(v,
                      d_spx.basisRowStatus(rowIdx),
                      mpq_class{dualRay[rowIdx].backend().data()},
                      sol);
    }
    // Get the col activity for each column
    soplex::Rational colValue;
    for (int colIdx = 0; colIdx < d_spx.numCols(); colIdx++)
    {
      const ArithVar v = d_colToArithVar.at(colIdx);
      d_spx.getColActivityRational(colIdx, colValue);
      extractVarValue(v,
                      d_spx.basisColStatus(colIdx),
                      mpq_class{colValue.backend().data()},
                      sol);
    }
  }
  else
  {
    Unimplemented();
  }

#if 0  // For debug
  for (int colIdx = 0; colIdx < d_spx.numCols(); colIdx++)
  {
    soplex::LPColRational col(d_spx.numCols());
    d_spx.getColRational(colIdx, col);
    mpq_class val = sol.newValues[d_colToArithVar[colIdx]]
                        .getNoninfinitesimalPart()
                        .getValue();
    if (val < mpq_class{col.lower().backend().data()}
        || val > mpq_class{col.upper().backend().data()})
    {
      printf(
          "Column %d (var %d) has value %g which is outside bounds [%g, %g]\n",
          colIdx,
          d_colToArithVar.at(colIdx),
          val.get_d(),
          col.lower().convert_to<double>(),
          col.upper().convert_to<double>());
    }
  }
  for (int rowIdx = 0; rowIdx < d_spx.numRows(); rowIdx++)
  {
    soplex::LPRowRational row(d_spx.numRows());
    d_spx.getRowRational(rowIdx, row);
    mpq_class val = sol.newValues[d_rowToArithVar[rowIdx]]
                        .getNoninfinitesimalPart()
                        .getValue();
    if (val < mpq_class{row.lhs().backend().data()}
        || val > mpq_class{row.rhs().backend().data()})
    {
      printf("Row %d (var %d) has value %g which is outside bounds [%g, %g]\n",
             rowIdx,
             d_rowToArithVar.at(rowIdx),
             val.get_d(),
             row.lhs().convert_to<double>(),
             row.rhs().convert_to<double>());
    }
  }
  // printSolution(sol);
#endif
  return sol;
}

void ExactSoplex2::printSolution(const external::Solution& sol) const
{
  std::cout << "{  ";
  for (const auto v : sol.newBasis)
  {
    if (d_vars.isAuxiliary(v))
      d_vars.printModel(v, std::cout);
    else
      std::cout << d_vars.asNode(v).getName() << "\n";
  }
  std::cout << "}\n";
  for (const auto v : sol.newValues)
  {
    if (sol.newValues[0].isZero()) continue;
    std::cout << d_vars.asNode(v).getName() << " = " << sol.newValues[v]
              << "\n";
  }
}

std::optional<Rational> ExactSoplex2::estimateWithCFE(double d) const
{
  return estimateWithCFE(d, Integer(s_defaultMaxDenom));
}

std::optional<Rational> ExactSoplex2::estimateWithCFE(double d,
                                                      const Integer& D) const
{
  if (std::optional<Rational> from_double = Rational::fromDouble(d))
  {
    return {};
  }
  return std::optional<Rational>();
}

void ExactSoplex2::tryCut(int, CutInfo&) { Unimplemented(); }

external::MipResult ExactSoplex2::solveMIP(bool al)
{
  return external::MipResult::MipUnknown;
}

double ExactSoplex2::sumInfeasibilities(SoPlex& prob, bool mip) const
{
  /* compute the sum of dual infeasibilities */
  double infeas = 0.0;

  soplex::Rational maxBoundViolation, sumBoundViolation;
  soplex::Rational maxRowViolation, sumRowViolation;
  soplex::Rational maxDualViolation, sumDualViolation;
  prob.getBoundViolationRational(maxBoundViolation, sumBoundViolation);
  prob.getRowViolationRational(maxRowViolation, sumRowViolation);
  prob.getDualViolationRational(maxDualViolation, sumDualViolation);

  std::cout << "Infeas: " << infeas << std::endl;
  std::cout << "Max bound violation: " << maxBoundViolation << std::endl;
  std::cout << "Sum bound violation: " << sumBoundViolation << std::endl;
  std::cout << "Max row violation: " << maxRowViolation << std::endl;
  std::cout << "Sum row violation: " << sumRowViolation << std::endl;
  std::cout << "Max dual violation: " << maxDualViolation << std::endl;
  std::cout << "Sum dual violation: " << sumDualViolation << std::endl;
  std::cout << "The total infeas is "
            << static_cast<double>(sumRowViolation + sumBoundViolation)
            << std::endl;

  return static_cast<double>(sumRowViolation + sumBoundViolation);
}

external::LinResult ExactSoplex2::solveRelaxation()
{
  Assert(!d_solvedRelaxation);

  // glp_erase_prob(d_realProb);
  // glp_copy_prob(d_realProb, d_inputProb, GLP_OFF);

  using SpxStatus = soplex::SPxSolverBase<double>::Status;
  soplex::VectorRational x(d_spx.numCols());

  // d_spx.clearBasis();
  // std::cout << "OBJ:" << d_spx.objValueReal() << std::endl;
  switch (d_spx.optimize())
  {
    case SpxStatus::OPTIMAL:
    case SpxStatus::UNBOUNDED:
      // std::cout << "OBJ" << d_spx.objValueReal() << std::endl;
      Assert(d_spx.hasSol());
      d_spx.getPrimalRational(x);
      d_solvedRelaxation = true;
      // Check the value of the last column (strict variable)
      return external::LinResult::LinFeasible;
    case SpxStatus::INFEASIBLE:
      d_solvedRelaxation = true;
      return external::LinResult::LinInfeasible;
    case SpxStatus::ABORT_ITER:
    case SpxStatus::ABORT_TIME:
    case SpxStatus::ABORT_CYCLING: return external::LinResult::LinExhausted;
    default: return external::LinResult::LinUnknown;
  }
}
#if 0

static void loadCut(glp_tree* tree, CutInfo* cut)
{
  int ord, cut_len, cut_klass;
  int N, M;
  int* cut_inds;
  double* cut_coeffs;
  int glpk_cut_type;
  double cut_rhs;
  glp_prob* lp;

  lp = glp_ios_get_prob(tree);
  ord = cut->poolOrdinal();

  N = glp_get_num_cols(lp);
  M = glp_get_num_rows(lp);

  cut->setDimensions(N, M);

  // Get the cut
  cut_len = glp_ios_get_cut(tree, ord, NULL, NULL, &cut_klass, NULL, NULL);
  Assert(fromGlpkClass(cut_klass) == cut->getKlass());

  PrimitiveVec& cut_vec = cut->getCutVector();
  cut_vec.setup(cut_len);
  cut_inds = cut_vec.inds;
  cut_coeffs = cut_vec.coeffs;

  cut_vec.len = glp_ios_get_cut(
      tree, ord, cut_inds, cut_coeffs, &cut_klass, &glpk_cut_type, &cut_rhs);
  Assert(fromGlpkClass(cut_klass) == cut->getKlass());
  Assert(cut_vec.len == cut_len);

  cut->setRhs(cut_rhs);

  cut->setKind(glpk_type_to_kind(glpk_cut_type));
}

static MirInfo* mirCut(glp_tree* tree, int exec_ord, int cut_ord)
{
  Trace("approx::mirCut") << "mirCut()" << exec_ord << std::endl;

  MirInfo* mir;
  mir = new MirInfo(exec_ord, cut_ord);
  loadCut(tree, mir);
  mir->initSet();

  int nrows = glp_ios_cut_get_aux_nrows(tree, cut_ord);

  PrimitiveVec& row_sum = mir->row_sum;
  row_sum.setup(nrows);
  glp_ios_cut_get_aux_rows(tree, cut_ord, row_sum.inds, row_sum.coeffs);

  glp_ios_cut_get_mir_cset(tree, cut_ord, mir->cset);
  mir->delta = glp_ios_cut_get_mir_delta(tree, cut_ord);
  glp_ios_cut_get_mir_subst(tree, cut_ord, mir->subst);
  glp_ios_cut_get_mir_virtual_rows(tree, cut_ord, mir->vlbRows, mir->vubRows);

  if (TraceIsOn("approx::mirCut"))
  {
    Trace("approx::mirCut") << "mir_id: " << exec_ord << std::endl;
    row_sum.print(Trace("approx::mirCut"));
  }

  return mir;
}

static GmiInfo* gmiCut(glp_tree* tree, int exec_ord, int cut_ord)
{
  Trace("approx::gmiCut") << "gmiCut()" << exec_ord << std::endl;

  int gmi_var;
  int write_pos;
  int read_pos;
  int stat;
  int ind;
  int i;

  GmiInfo* gmi;
  glp_prob* lp;

  gmi = new GmiInfo(exec_ord, cut_ord);
  loadCut(tree, gmi);

  lp = glp_ios_get_prob(tree);

  int N = gmi->getN();
  int M = gmi->getMAtCreation();

  // Get the tableau row
  int nrows CVC5_UNUSED = glp_ios_cut_get_aux_nrows(tree, gmi->poolOrdinal());
  Assert(nrows == 1);
  int rows[1 + 1];
  glp_ios_cut_get_aux_rows(tree, gmi->poolOrdinal(), rows, NULL);
  gmi_var = rows[1];

  gmi->init_tab(N);
  gmi->basic = M + gmi_var;

  Trace("approx::gmiCut") << gmi << " " << gmi->basic << " " << cut_ord << " "
                          << M << " " << gmi_var << std::endl;

  PrimitiveVec& tab_row = gmi->tab_row;
  Trace("approx::gmiCut") << "Is N sufficient here?" << std::endl;
  tab_row.len = glp_eval_tab_row(lp, gmi->basic, tab_row.inds, tab_row.coeffs);

  Trace("approx::gmiCut") << "gmi_var " << gmi_var << std::endl;

  Trace("approx::gmiCut") << "tab_pos " << tab_row.len << std::endl;
  write_pos = 1;
  for (read_pos = 1; read_pos <= tab_row.len; ++read_pos)
  {
    if (fabs(tab_row.coeffs[read_pos]) < 1e-10)
    {
    }
    else
    {
      tab_row.coeffs[write_pos] = tab_row.coeffs[read_pos];
      tab_row.inds[write_pos] = tab_row.inds[read_pos];
      ++write_pos;
    }
  }
  tab_row.len = write_pos - 1;
  Trace("approx::gmiCut") << "write_pos " << write_pos << std::endl;
  Assert(tab_row.len > 0);

  for (i = 1; i <= tab_row.len; ++i)
  {
    ind = tab_row.inds[i];
    Trace("approx::gmiCut") << "ind " << i << " " << ind << std::endl;
    stat =
        (ind <= M) ? glp_get_row_stat(lp, ind) : glp_get_col_stat(lp, ind - M);

    Trace("approx::gmiCut")
        << "ind " << i << " " << ind << " stat " << stat << std::endl;
    switch (stat)
    {
      case GLP_NL:
      case GLP_NU:
      case GLP_NS: gmi->tab_statuses[i] = stat; break;
      case GLP_NF:
      default: Unreachable();
    }
  }

  if (TraceIsOn("approx::gmiCut"))
  {
    gmi->print(Trace("approx::gmiCut"));
  }
  return gmi;
}

static BranchCutInfo* branchCut(
    glp_tree* tree, int exec_ord, int br_var, double br_val, bool down_bad)
{
  //(tree, br_var, br_val, dn < 0);
  double rhs;
  Kind k;
  if (down_bad)
  {
    // down branch is infeasible
    // x <= floor(v) is infeasible
    // - so x >= ceiling(v) is implied
    k = Kind::GEQ;
    rhs = std::ceil(br_val);
  }
  else
  {
    // up branch is infeasible
    // x >= ceiling(v) is infeasible
    // - so x <= floor(v) is implied
    k = Kind::LEQ;
    rhs = std::floor(br_val);
  }
  BranchCutInfo* br_cut = new BranchCutInfo(exec_ord, br_var, k, rhs);
  return br_cut;
}

static void glpkCallback(glp_tree* tree, void* info)
{
  AuxInfo* aux = (AuxInfo*)(info);
  TreeLog& tl = *(aux->tl);

  int exec = tl.getExecutionOrd();
  int glpk_node_p = -1;
  int node_ord = -1;

  if (tl.isActivelyLogging())
  {
    switch (glp_ios_reason(tree))
    {
      case GLP_LI_DELROW:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);

        int nrows = glp_ios_rows_deleted(tree, NULL);
        int* num = new int[1 + nrows];
        glp_ios_rows_deleted(tree, num);

        NodeLog& node = tl.getNode(node_ord);

        RowsDeleted* rd = new RowsDeleted(exec, nrows, num);

        node.addCut(rd);
        delete[] num;
      }
      break;
      case GLP_ICUTADDED:
      {
        int cut_ord = glp_ios_pool_size(tree);
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        Assert(cut_ord > 0);
        Trace("approx") << "curr node " << glpk_node_p << " cut ordinal "
                        << cut_ord << " node depth "
                        << glp_ios_node_level(tree, glpk_node_p) << std::endl;
        int klass;
        glp_ios_get_cut(tree, cut_ord, NULL, NULL, &klass, NULL, NULL);

        NodeLog& node = tl.getNode(node_ord);
        switch (klass)
        {
          case GLP_RF_GMI:
          {
            GmiInfo* gmi = gmiCut(tree, exec, cut_ord);
            node.addCut(gmi);
          }
          break;
          case GLP_RF_MIR:
          {
            MirInfo* mir = mirCut(tree, exec, cut_ord);
            node.addCut(mir);
          }
          break;
          case GLP_RF_COV: Trace("approx") << "GLP_RF_COV" << std::endl; break;
          case GLP_RF_CLQ: Trace("approx") << "GLP_RF_CLQ" << std::endl; break;
          default: break;
        }
      }
      break;
      case GLP_ICUTSELECT:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        int cuts = glp_ios_pool_size(tree);
        int* ords = new int[1 + cuts];
        int* rows = new int[1 + cuts];
        int N = glp_ios_selected_cuts(tree, ords, rows);

        NodeLog& nl = tl.getNode(node_ord);
        Trace("approx") << glpk_node_p << " " << node_ord << " " << cuts << " "
                        << N << std::endl;
        for (int i = 1; i <= N; ++i)
        {
          Trace("approx") << "adding to " << node_ord << " @ i= " << i
                          << " ords[i] = " << ords[i]
                          << " rows[i] = " << rows[i] << std::endl;
          nl.addSelected(ords[i], rows[i]);
        }
        delete[] ords;
        delete[] rows;
        nl.applySelected();
      }
      break;
      case GLP_LI_BRANCH:
      {
        // a branch was just made
        int br_var;
        int p, dn, up;
        int p_ord, dn_ord, up_ord;
        double br_val;
        br_var = glp_ios_branch_log(tree, &br_val, &p, &dn, &up);
        p_ord = glp_ios_node_ord(tree, p);

        dn_ord = (dn >= 0) ? glp_ios_node_ord(tree, dn) : -1;
        up_ord = (up >= 0) ? glp_ios_node_ord(tree, up) : -1;

        Trace("approx::") << "branch: " << br_var << " " << br_val << " tree "
                          << p << " " << dn << " " << up << std::endl;
        Trace("approx::") << "\t " << p_ord << " " << dn_ord << " " << up_ord
                          << std::endl;
        if (dn < 0 && up < 0)
        {
          Trace("approx::") << "branch close " << exec << std::endl;
          NodeLog& node = tl.getNode(p_ord);
          BranchCutInfo* cut_br = branchCut(tree, exec, br_var, br_val, dn < 0);
          node.addCut(cut_br);
          tl.close(p_ord);
        }
        else if (dn < 0 || up < 0)
        {
          Trace("approx::") << "branch cut" << exec << std::endl;
          NodeLog& node = tl.getNode(p_ord);
          BranchCutInfo* cut_br = branchCut(tree, exec, br_var, br_val, dn < 0);
          node.addCut(cut_br);
        }
        else
        {
          Trace("approx::") << "normal branch" << std::endl;
          tl.branch(p_ord, br_var, br_val, dn_ord, up_ord);
        }
      }
      break;
      case GLP_LI_CLOSE:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        Trace("approx::") << "close " << glpk_node_p << std::endl;
        tl.close(node_ord);
      }
      break;
      default: break;
    }
  }

  switch (glp_ios_reason(tree))
  {
    case GLP_IBINGO:
      Trace("approx::") << "bingo" << std::endl;
      aux->term = MipBingo;
      glp_ios_terminate(tree);
      break;
    case GLP_ICUTADDED:
    {
      tl.addCut();
    }
    break;
    case GLP_LI_BRANCH:
    {
      int p, dn, up;
      int br_var = glp_ios_branch_log(tree, NULL, &p, &dn, &up);

      if (br_var >= 0)
      {
        unsigned v = br_var;
        tl.logBranch(v);
        int depth = glp_ios_node_level(tree, p);
        unsigned ubl =
            (aux->branchLimit) >= 0 ? ((unsigned)(aux->branchLimit)) : 0u;
        if (tl.numBranches(v) >= ubl || depth >= (aux->branchDepth))
        {
          aux->term = BranchesExhausted;
          glp_ios_terminate(tree);
        }
      }
    }
    break;
    case GLP_LI_CLOSE: break;
    default:
    {
      glp_prob* prob = glp_ios_get_prob(tree);
      int iterationcount = glp_get_it_cnt(prob);
      if (exec > (aux->pivotLimit))
      {
        aux->term = ExecExhausted;
        glp_ios_terminate(tree);
      }
      else if (iterationcount > (aux->pivotLimit))
      {
        aux->term = PivotsExhauasted;
        glp_ios_terminate(tree);
      }
    }
    break;
  }
}
#endif

std::vector<const CutInfo*> ExactSoplex2::getValidCuts(const NodeLog& con)
{
  std::vector<const CutInfo*> proven;
  int nid = con.getNodeId();
  for (NodeLog::const_iterator j = con.begin(), jend = con.end(); j != jend;
       ++j)
  {
    CutInfo* cut = *j;

    if (cut->getKlass() != RowsDeletedKlass)
    {
      if (!cut->reconstructed())
      {
        Assert(!cut->reconstructed());
        tryCut(nid, *cut);
      }
    }

    if (cut->proven())
    {
      proven.push_back(cut);
    }
  }
  return proven;
}

ArithVar ExactSoplex2::getBranchVar(const NodeLog& con) const
{
  int br_var = con.branchVariable();
  return getArithVarFromStructural(br_var);
}

inline DeltaRational sumConstraints(const DenseMap<Rational>& xs,
                                    const DenseMap<ConstraintP>& cs,
                                    bool* anyinf)
{
  if (anyinf != NULL)
  {
    *anyinf = false;
  }

  DeltaRational beta(0);
  DenseMap<Rational>::const_iterator iter, end;
  iter = xs.begin();
  end = xs.end();

  Trace("approx::sumConstraints") << "sumConstraints";
  for (; iter != end; ++iter)
  {
    ArithVar x = *iter;
    const Rational& psi = xs[x];
    ConstraintP c = cs[x];
    Assert(c != NullConstraint);

    const DeltaRational& bound = c->getValue();
    beta += bound * psi;
    Trace("approx::sumConstraints") << " +(" << bound << "*" << psi << ")";
    if (anyinf != NULL)
    {
      *anyinf = *anyinf || !bound.infinitesimalIsZero();
    }
  }
  Trace("approx::sumConstraints") << "= " << beta << std::endl;

  return beta;
}

// remove fixed variables from the vector
inline void removeFixed(const ArithVariables& vars,
                        DenseVector& dv,
                        std::set<ConstraintP>& exp)
{
  DenseMap<Rational>& vec = dv.lhs;
  Rational& removed = dv.rhs;
  std::vector<ArithVar> equal;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for (; vec_iter != vec_end; ++vec_iter)
  {
    ArithVar x = *vec_iter;
    if (vars.boundsAreEqual(x))
    {
      equal.push_back(x);
    }
  }
  std::vector<ArithVar>::const_iterator equal_iter, equal_end;
  equal_iter = equal.begin(), equal_end = equal.end();
  for (; equal_iter != equal_end; ++equal_iter)
  {
    ArithVar x = *equal_iter;
    Assert(vars.boundsAreEqual(x));
    const DeltaRational& lb = vars.getLowerBound(x);
    Assert(lb.infinitesimalIsZero());
    removed -= (vec[x]) * lb.getNoninfinitesimalPart();

    vec.remove(x);

    std::pair<ConstraintP, ConstraintP> p = vars.explainEqualBounds(x);
    exp.insert(p.first);
    Trace("removeFixed") << "remove fixed " << p.first << std::endl;
    if (p.second != NullConstraint)
    {
      exp.insert(p.second);
      Trace("removeFixed") << "remove fixed " << p.second << std::endl;
    }
  }
}
inline void removeZeroes(DenseMap<Rational>& v)
{
  // Remove Slack variables
  std::vector<ArithVar> zeroes;
  DenseMap<Rational>::const_iterator i, iend;
  for (i = v.begin(), iend = v.end(); i != iend; ++i)
  {
    ArithVar x = *i;
    if (v[x].isZero())
    {
      zeroes.push_back(x);
    }
  }

  std::vector<ArithVar>::const_iterator j, jend;
  for (j = zeroes.begin(), jend = zeroes.end(); j != jend; ++j)
  {
    ArithVar x = *j;
    v.remove(x);
  }
}

inline void removeZeroes(DenseVector& v) { removeZeroes(v.lhs); }

inline void removeAuxillaryVariables(const ArithVariables& vars,
                                     DenseMap<Rational>& vec)
{
  // Remove auxillary variables
  std::vector<ArithVar> aux;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for (; vec_iter != vec_end; ++vec_iter)
  {
    ArithVar x = *vec_iter;
    if (vars.isAuxiliary(x))
    {
      aux.push_back(x);
    }
  }

  std::vector<ArithVar>::const_iterator aux_iter, aux_end;
  aux_iter = aux.begin(), aux_end = aux.end();
  for (; aux_iter != aux_end; ++aux_iter)
  {
    ArithVar s = *aux_iter;
    Rational& s_coeff = vec.get(s);
    Assert(vars.isAuxiliary(s));
    Assert(vars.hasNode(s));
    Node sAsNode = vars.asNode(s);
    Polynomial p = Polynomial::parsePolynomial(sAsNode);
    for (Polynomial::iterator j = p.begin(), p_end = p.end(); j != p_end; ++j)
    {
      Monomial m = *j;
      const Rational& ns_coeff = m.getConstant().getValue();
      Node vl = m.getVarList().getNode();
      ArithVar ns = vars.asArithVar(vl);
      Rational prod = s_coeff * ns_coeff;
      if (vec.isKey(ns))
      {
        vec.get(ns) += prod;
      }
      else
      {
        vec.set(ns, prod);
      }
    }
    s_coeff = Rational(0);  // subtract s_coeff * s from vec
  }
  removeZeroes(vec);
}

ArithVar ExactSoplex2::_getArithVar(int nid, int M, int ind) const
{
  if (ind <= 0)
  {
    return ARITHVAR_SENTINEL;
  }
  else if (ind <= M)
  {
    return getArithVarFromRow(nid, ind);
  }
  else
  {
    return getArithVarFromStructural(ind - M);
  }
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex implementation. */
#endif /*#ifdef CVC5_USE_SOPLEX */

/* Begin soplex/No soplpex Glue code. */
namespace cvc5::internal {
namespace theory {
namespace arith::linear {

external::ExternalSimplex* ExactSimplex::mkExactSimplexSolver2(
    CVC5_UNUSED const ArithVariables& vars,
    CVC5_UNUSED TreeLog& l,
    CVC5_UNUSED external::SimplexStatistics& s)
{
#ifdef CVC5_USE_SOPLEX
  return new ExactSoplex2(vars, l, s);
#else
  Unimplemented() << "Exact simplex solver requires SoPlex";
#endif
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex/No soplex Glue code. */
