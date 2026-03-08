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

#include "base/cvc5config.h"
#include "base/output.h"
#include "options/arith_options.h"
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
using VarStatus = soplex::SPxSolverBase<double>::VarStatus;
using SolverStatus = soplex::SPxSolverBase<double>::Status;

DeltaRational toDeltaRational(const soplex::Rational& value)
{
  return {mpq_class{value.backend().data()}};
}

mpq_class toMpq(const soplex::Rational& value)
{
  return mpq_class{value.backend().data()};
}

class ExactSoplex : public ExactSimplex
{
 public:
  ExactSoplex(const ArithVariables& v,
              TreeLog& l,
              external::SimplexStatistics& s);

  external::LinResult solveRelaxation() override;
  external::Solution extractRelaxation() override
  {
    return extractSolution(false);
  }

  ArithRatPairVec heuristicOptCoeffs() const override;

  external::MipResult solveMIP(bool al) override;
  external::Solution extractMIP() override { return extractSolution(true); }
  std::vector<const CutInfo*> getValidCuts(const NodeLog& nodes) override;
  ArithVar getBranchVar(const NodeLog& con) const override;

  static void printSoplexStatus(int status, std::ostream& out);

  std::optional<Rational> estimateWithCFE(double d) const override
  {
    Unimplemented();
  }
  std::optional<Rational> estimateWithCFE(double d,
                                          const Integer& D) const override
  {
    Unimplemented();
  }

 protected:
  void printSolution(const external::Solution& sol) const;

  soplex::Rational varToLb(ArithVar v) const;
  soplex::Rational varToUb(ArithVar v) const;
  bool hasStrictBound(ArithVar v) const;
  bool hasStrictLb(ArithVar v) const;
  bool hasStrictUB(ArithVar v) const;

  virtual external::Solution extractSolution(bool mip) = 0;
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

  ArithVar getArithVarFromStructural(int ind) const
  {
    if (ind >= 0)
    {
      unsigned u = static_cast<unsigned>(ind);
      if (u < d_colToArithVar.size())
      {
        return d_colToArithVar[u];
      }
    }
    return ARITHVAR_SENTINEL;
  }

  double sumInfeasibilities(SoPlex& prob, bool mip) const;

  const ArithVariables& d_vars;
  TreeLog& d_log;

  const static mpq_class s_zero_mpq;
  const static soplex::Rational s_zero_rational;

  SoPlex d_spx;

  DenseMap<std::size_t> d_colIndices;

  std::vector<ArithVar> d_rowToArithVar;
  std::vector<ArithVar> d_colToArithVar;

 public:
  enum class VariableType
  {
    ROW,
    COL,
  };
  enum class FeasibilityType
  {
    FEASIBLE,
    INFEASIBLE,
  };
  enum class BoundViolationType
  {
    LOWER,
    UPPER,
  };

 protected:
  template <VariableType VarType>
  void extractVarValue(int idx,
                       external::Solution& sol,
                       const soplex::VectorRational* values = nullptr);

  virtual bool isStrictVarZero() = 0;

  bool d_solvedRelaxation;
  bool d_solvedMIP;
};

ExactSoplex::BoundViolationType operator!(ExactSoplex::BoundViolationType v)
{
  return v == ExactSoplex::BoundViolationType::LOWER
             ? ExactSoplex::BoundViolationType::UPPER
             : ExactSoplex::BoundViolationType::LOWER;
}

std::ostream& operator<<(std::ostream& out,
                         const ExactSoplex::BoundViolationType v)
{
  switch (v)
  {
    case ExactSoplex::BoundViolationType::LOWER: return out << "LOWER";
    case ExactSoplex::BoundViolationType::UPPER: return out << "UPPPER";
    default: return out << "UNKNOWN";
  }
}

class ExactSoplexEpsilon : public ExactSoplex
{
 public:
  ExactSoplexEpsilon(const ArithVariables& v,
                     TreeLog& l,
                     external::SimplexStatistics& s);

  void setOptCoeffs(const ArithRatPairVec& ref) override;

 private:
  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static constexpr double SMALL_FIXED_DELTA =
      std::numeric_limits<double>::epsilon();

  bool isStrictVarZero() override { return false; }

  external::Solution extractSolution(bool mip) override;
};

class ExactSoplexStrict : public ExactSoplex
{
 public:
  ExactSoplexStrict(const ArithVariables& v,
                    TreeLog& l,
                    external::SimplexStatistics& s);

  void setOptCoeffs(const ArithRatPairVec& ref) override;

 private:
  external::Solution extractSolution(bool mip) override;

  void adjustValue(int rowIdx,
                   soplex::Rational& value,
                   const soplex::Rational& strictValue) const;

  bool isStrictVarZero() override
  {
    if (d_spx.hasPrimal())
    {
      soplex::VectorRational primal(d_spx.numColsRational());
      d_spx.getPrimalRational(primal);
      return primal[d_spx.numColsRational() - 1].is_zero();
    }
    return false;
  }

  DeltaRational getRowActivity(int rowIdx) const;
};

const mpq_class ExactSoplex::s_zero_mpq{0};
const soplex::Rational ExactSoplex::s_zero_rational{0};

ExactSoplex::ExactSoplex(const ArithVariables& var,
                         TreeLog& l,
                         external::SimplexStatistics& s)
    : ExactSimplex(s),
      d_vars(var),
      d_log(l),
      d_solvedRelaxation(false),
      d_solvedMIP(false)
{
  d_stats.d_externalSimplexType.set(
      static_cast<std::underlying_type_t<options::ExternalLPSolver>>(
          options::ExternalLPSolver::SOPLEX));

  d_spx.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);
  d_spx.setIntParam(SoPlex::SIMPLIFIER, SoPlex::SIMPLIFIER_OFF);
  d_spx.setIntParam(SoPlex::ALGORITHM, SoPlex::ALGORITHM_PRIMAL);
  d_spx.setIntParam(SoPlex::VERBOSITY, SoPlex::VERBOSITY_ERROR);
  d_spx.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
  d_spx.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
  d_spx.setIntParam(SoPlex::PRICER, SoPlex::PRICER_AUTO);
  d_spx.setIntParam(SoPlex::ITERLIMIT, d_pivotLimit);
  d_spx.setRealParam(SoPlex::FEASTOL, 0.0);
  d_spx.setRealParam(SoPlex::OPTTOL, 0.0);

  if (TraceIsOn("approx-debug"))
  {
    d_spx.setIntParam(SoPlex::VERBOSITY, SoPlex::VERBOSITY_DEBUG);
  }

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
}

ExactSoplexEpsilon::ExactSoplexEpsilon(const ArithVariables& var,
                                       TreeLog& l,
                                       external::SimplexStatistics& s)
    : ExactSoplex(var, l, s)
{
  // The number of cols must accommodate for the non-aux variables as well as
  // the additional strict variable t
  soplex::LPRowSetRational rows(static_cast<int>(d_rowToArithVar.size()));
  soplex::LPColSetRational cols(static_cast<int>(d_colToArithVar.size()));

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (ArithVar v : d_rowToArithVar)
  {
    Assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    // std::cout << d_vars.asNode(v).getName() << "\n\n";

    soplex::DSVectorRational vec(static_cast<int>(p.size()));

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
}

ExactSoplexStrict::ExactSoplexStrict(const ArithVariables& var,
                                     TreeLog& l,
                                     external::SimplexStatistics& s)
    : ExactSoplex(var, l, s)
{
  // std::ofstream out(
  //     "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/report.txt");

  // The number of cols must accommodate for the non-aux variables as well
  // as the additional strict variable t Todo: better estimation of the
  // number of rows
  soplex::LPRowSetRational rows(static_cast<int>(d_rowToArithVar.size()));
  soplex::LPColSetRational cols(static_cast<int>(d_colToArithVar.size()) + 1);
  const int strictVarIdx = static_cast<int>(d_colToArithVar.size());
  // std::cout << "int numColsRational = " << strictVarIdx + 1 << ";\n";

  std::vector<ArithVar> rowToArithVarStrict;
  rowToArithVarStrict.reserve(d_rowToArithVar.size() * 2);

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (ArithVar v : d_rowToArithVar)
  {
    assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    soplex::DSVectorRational vec(static_cast<int>(p.size()) + 1);
    // out << "{\nsoplex::DSVectorRational vec(numColsRational);\n";

    for (auto j = p.begin(), end = p.end(); j != end; ++j)
    {
      const Monomial& mono = *j;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      int colIndex = static_cast<int>(d_colIndices[av]);
      vec.add(colIndex, constant.getValue().getValue().get_mpq_t());
      // out << "vec.add(" << colIndex << ", " << constant.getValue().getValue()
      //     << ");\n";
    }

    // If we are dealing with a row with a strict bound (< or >), then we
    // split it in two rows.
    // lhs + t <= lb   and   lhs - t >= ub
    // Minimizing (-t) will produce three possible outputs:
    // - problem is infeasible => assigment is unsat
    // - t = 0 => assigment violates the strict bounds, unsat
    // - t > 0 => assigment is sat
    if (hasStrictBound(v))
    {
      if (d_vars.hasLowerBound(v))
      {
        // If strict, add t, and in any case add the split row
        if (hasStrictLb(v))
        {
          vec.add(strictVarIdx, -1);
          // out << "vec.add(" << strictVarIdx << ", 1);\n";
        }
        rowToArithVarStrict.emplace_back(v);
        rows.add({varToLb(v), vec, soplex::infinity});
        // out << "rows.add(" << varToLb(v) << ", vec, soplex::infinity);\n";
      }
      if (d_vars.hasUpperBound(v))
      {
        // Ensure that the strict variable is present only once and with the
        // correct coefficient in the row vector
        if (const int idx = vec.pos(strictVarIdx); idx > -1) vec.remove(idx);
        // out << "const int idx = vec.pos(" << strictVarIdx
        //     << "); if ( idx > -1) vec.remove(idx);\n";

        // If strict, add -t, and in any case add the split row
        if (hasStrictUB(v))
        {
          vec.add(strictVarIdx, 1);
          // out << "vec.add(" << strictVarIdx << ", -1);\n";
        }
        rowToArithVarStrict.emplace_back(v);
        rows.add({-soplex::infinity, vec, varToUb(v)});
        // out << "rows.add(-soplex::infinity, vec, " << varToUb(v) << ");\n";
      }
    }
    else
    {
      rowToArithVarStrict.emplace_back(v);
      rows.add({varToLb(v), vec, varToUb(v)});
      // out << "rows.add(" << varToLb(v) << ", vec, " << varToUb(v) << ");\n";
    }
    // out << "}\n";
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

    bool isLbStrict = hasStrictLb(v);
    bool isUbStrict = hasStrictUB(v);
    if (isLbStrict)
    {
      soplex::DSVectorRational vec(2);
      vec.add(static_cast<int>(d_colIndices[v]), 1);
      vec.add(strictVarIdx, -1);
      // out << "{\nsoplex::DSVectorRational vec(2);\n";
      // out << "vec.add(" << static_cast<int>(d_colIndices[v]) << ", 1);\n";
      // out << "vec.add(" << strictVarIdx << ", 1);\n";
      rows.add({varToLb(v), vec, soplex::infinity});
      // out << "rows.add(" << varToLb(v) << ", vec, soplex::infinity);\n}\n";
      rowToArithVarStrict.emplace_back(v);
    }
    if (isUbStrict)
    {
      soplex::DSVectorRational vec(2);
      vec.add(static_cast<int>(d_colIndices[v]), 1);
      vec.add(strictVarIdx, 1);
      // out << "{\nsoplex::DSVectorRational vec(2);\n";
      // out << "vec.add(" << static_cast<int>(d_colIndices[v]) << ", 1);\n";
      // out << "vec.add(" << strictVarIdx << ", -1);\n";
      rows.add({-soplex::infinity, vec, varToUb(v)});
      // out << "rows.add(-soplex::infinity, vec, " << varToUb(v) << ");\n}\n";
      rowToArithVarStrict.emplace_back(v);
    }

    cols.add({0.0,
              soplex::DSVectorRational(),
              isUbStrict ? soplex::infinity : varToUb(v),
              isLbStrict ? -soplex::infinity : varToLb(v)});
  }

  // Add the strict variable t
  cols.add({-1, soplex::DSVectorRational(), 1, 0});
  // out << "cols.add({-1, soplex::DSVectorRational(), soplex::infinity,
  // 0});\n";

  // Add both columns and rows to the LP
  d_spx.addColsRational(cols);
  d_spx.addRowsRational(rows);

  d_rowToArithVar = std::move(rowToArithVarStrict);

  // out.close();
}

soplex::Rational ExactSoplex::varToLb(const ArithVar v) const
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

soplex::Rational ExactSoplex::varToUb(const ArithVar v) const
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

bool ExactSoplex::hasStrictBound(const ArithVar v) const
{
  return hasStrictLb(v) || hasStrictUB(v);
}

bool ExactSoplex::hasStrictUB(const ArithVar v) const
{
  return d_vars.hasUpperBound(v)
         && !d_vars.getUpperBound(v).getInfinitesimalPart().isZero();
}

bool ExactSoplex::hasStrictLb(ArithVar v) const
{
  return d_vars.hasLowerBound(v)
         && !d_vars.getLowerBound(v).getInfinitesimalPart().isZero();
}

int ExactSoplex::guessDir(const ArithVar v) const
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

ArithRatPairVec ExactSoplex::heuristicOptCoeffs() const
{
  ArithRatPairVec ret;
  return ret;

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

void ExactSoplexEpsilon::setOptCoeffs(const ArithRatPairVec& ref)
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
        const int colIndex = d_colIndices[av];
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
      const int colIndex = d_colIndices[v];
      const double coeff = q.getDouble();
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

void ExactSoplexStrict::setOptCoeffs(const ArithRatPairVec& ref) {}

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

void ExactSoplex::printSoplexStatus(int status, std::ostream& out)
{
  using SpxStatus = SolverStatus;
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

template <ExactSoplex::VariableType VarType>
void ExactSoplex::extractVarValue(const int idx,
                                  external::Solution& sol,
                                  const soplex::VectorRational* const values)
{
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;
  ArithVar v = ARITHVAR_SENTINEL;
  VarStatus varStatus = VarStatus::UNDEFINED;

  if constexpr (VarType == VariableType::COL)
  {
    v = d_colToArithVar.at(idx);
    varStatus = d_spx.basisColStatus(idx);
  }
  if constexpr (VarType == VariableType::ROW)
  {
    v = d_rowToArithVar.at(idx);
    varStatus = d_spx.basisRowStatus(idx);
  }
  Assert(v != ARITHVAR_SENTINEL);

  mpq_class value;
  switch (varStatus)
  {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
    case VarStatus::BASIC:
      if (!newBasis.isMember(v)) newBasis.add(v);
      CVC5_FALLTHROUGH;
    case VarStatus::UNDEFINED:
      if (values != nullptr)
      {
        value = toMpq((*values)[idx]);
      }
      else if (VarType == VariableType::ROW)
      {
        soplex::Rational valRational;
        d_spx.getRowActivityRational(idx, valRational);
        value = toMpq(valRational);
      }
      else if (VarType == VariableType::COL)
      {
        soplex::Rational valRational;
        d_spx.getColActivityRational(idx, valRational);
        value = toMpq(valRational);
      }
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
    // For non-basic variables we know the value is at a bound
    // and we can use the d_vars/proper LP bounds directly
    case VarStatus::FIXED:
      Trace("approx-debug") << "non-basic lb" << std::endl;
      Assert(d_vars.hasLowerBound(v));
      newValues.set(v, d_vars.getLowerBound(v));
      break;
    case VarStatus::ON_LOWER:
      Assert(d_vars.hasLowerBound(v));
      Trace("approx-debug") << "non-basic lb" << std::endl;
      newValues.set(v, d_vars.getLowerBound(v));
      break;
    case VarStatus::ON_UPPER:
      Trace("approx-debug") << "non-basic ub" << std::endl;
      Assert(d_vars.hasUpperBound(v));
      newValues.set(v, d_vars.getUpperBound(v));
      break;
    case VarStatus::ZERO:
      Trace("approx-debug") << "non-basic zero" << std::endl;
      newValues.set(v, DeltaRational(0));
      break;
    default: Unreachable();
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
    soplex::VectorRational primal(d_spx.numColsRational());
    d_spx.getPrimalRational(primal);
    std::cout << "primal: " << primal << std::endl;
  }
  if (d_spx.hasSol())
  {
    soplex::VectorRational dual(d_spx.numRowsRational());
    d_spx.getDualRational(dual);
    std::cout << "dual: " << dual << std::endl;
  }
  if (d_spx.hasDualFarkas())
  {
    soplex::VectorRational dualRay(d_spx.numRowsRational());
    d_spx.getDualFarkasRational(dualRay);
    std::cout << "dual ray: " << dualRay << std::endl;
  }
  if (d_spx.hasPrimalRay())
  {
    soplex::VectorRational primalRay(d_spx.numColsRational());
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

external::Solution ExactSoplexEpsilon::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);
  external::Solution sol;

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

  if (d_spx.status() == SolverStatus::OPTIMAL
      || d_spx.status() == SolverStatus::UNBOUNDED)
  {
    Assert(d_spx.hasSol());
    // Feasible solution
    soplex::VectorRational primal(d_spx.numColsRational());
    const bool getPrimalSuccess = d_spx.getPrimalRational(primal);
    Assert(getPrimalSuccess);

    // Get the primal solution for the cols
    for (int colIdx = 0; colIdx < d_spx.numColsRational(); colIdx++)
    {
      ExactSoplex::extractVarValue<VariableType::COL>(colIdx, sol, &primal);
    }

    // Get the row activity for the rows
    soplex::Rational rowValue;
    for (int rowIdx = 0; rowIdx < d_spx.numRowsRational(); rowIdx++)
    {
      ExactSoplex::extractVarValue<VariableType::ROW>(rowIdx, sol);
    }
  }
  else if (d_spx.status() == SolverStatus::INFEASIBLE)
  {
    // Infeasible solution
    Assert(d_spx.hasDualFarkas());
    soplex::VectorRational dualRay(d_spx.numRowsRational());
    const bool getDualRaySuccess = d_spx.getDualFarkasRational(dualRay);
    Assert(getDualRaySuccess);

    // Get the last dual solution for the rows
    for (int rowIdx = 0; rowIdx < d_spx.numRowsRational(); rowIdx++)
    {
      ExactSoplex::extractVarValue<VariableType::ROW>(rowIdx, sol, &dualRay);
    }
    // Get the col activity for each column
    soplex::Rational colValue;
    for (int colIdx = 0; colIdx < d_spx.numColsRational(); colIdx++)
    {
      ExactSoplex::extractVarValue<VariableType::COL>(colIdx, sol);
    }
  }
  else
  {
    Unimplemented();
  }

#if 0  // For debug
  for (int colIdx = 0; colIdx < d_spx.numColsRational(); colIdx++)
  {
    soplex::LPColRational col(d_spx.numColsRational());
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
  for (int rowIdx = 0; rowIdx < d_spx.numRowsRational(); rowIdx++)
  {
    soplex::LPRowRational row(d_spx.numRowsRational());
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

external::Solution ExactSoplexStrict::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);

  external::Solution sol;
  DenseSet nonBasicVars;

  // No need to forcefully convert a basic variable at bound to non-basic
  bool isStrictBasic =
      d_spx.basisColStatus(d_spx.numColsRational() - 1) == VarStatus::BASIC;

  // TODO: reimplement this for mip
  // glp_prob* prob = mip ? d_mipProb : d_realProb;

  if (d_spx.status() == SolverStatus::OPTIMAL)
  {
    Assert(d_spx.hasSol());
    // Feasible solution
    soplex::VectorRational primal(d_spx.numColsRational());
    bool getPrimalSuccess = d_spx.getPrimalRational(primal);
    Assert(getPrimalSuccess);
    // std::cout << "Initial solution: " << primal << std::endl;

    const soplex::Rational& strictValue = primal[d_spx.numColsRational() - 1];
    if (!strictValue.is_zero())
    {
      d_spx.changeBoundsRational(
          d_spx.numColsRational() - 1, s_zero_rational, s_zero_rational);
      const SolverStatus res = d_spx.optimize();
      Assert(res == SolverStatus::OPTIMAL);
      isStrictBasic =
          d_spx.basisColStatus(d_spx.numColsRational() - 1) == VarStatus::BASIC;
      getPrimalSuccess = d_spx.getPrimalRational(primal);
      Assert(getPrimalSuccess);
      // std::cout << "Updated solution: " << primal << std::endl;
    }

    // Get the primal solution for the cols, except for the strict variable
    for (int colIdx = 0; colIdx < d_spx.numColsRational() - 1; colIdx++)
    {
      const ArithVar v = d_colToArithVar.at(colIdx);
      const VarStatus varStatus = d_spx.basisColStatus(colIdx);
      // We now know that this variable is non-basic
      if (varStatus != VarStatus::BASIC) nonBasicVars.add(v);
      ExactSoplex::extractVarValue<VariableType::COL>(colIdx, sol, &primal);
    }

    // Get the row activity for the rows
    for (int rowIdx = 0; rowIdx < d_spx.numRowsRational(); rowIdx++)
    {
      const ArithVar v = d_rowToArithVar.at(rowIdx);
      // We already know this row's value from some other side,
      // no need to recompute it
      if (nonBasicVars.isMember(v) > 0) continue;

      const VarStatus varStatus = d_spx.basisRowStatus(rowIdx);
      // We now know that this variable is non-basic
      if (varStatus != VarStatus::BASIC) nonBasicVars.add(v);
      ExactSoplex::extractVarValue<VariableType::ROW>(rowIdx, sol);
    }
  }
  else if (d_spx.status() == SolverStatus::INFEASIBLE)
  {
    soplex::Rational strictValue;
    d_spx.getColActivityRational(d_spx.numColsRational() - 1, strictValue);

    if (!strictValue.is_zero())
    {
      d_spx.changeBoundsRational(
          d_spx.numColsRational() - 1, s_zero_rational, s_zero_rational);
      const SolverStatus res = d_spx.optimize();
      Assert(res == SolverStatus::INFEASIBLE);
      isStrictBasic =
          d_spx.basisColStatus(d_spx.numColsRational() - 1) == VarStatus::BASIC;
      // std::cout << "Updated solution: " << primal << std::endl;
    }

    // Infeasible solution
    Assert(d_spx.hasDualFarkas());
    soplex::VectorRational dualRay(d_spx.numRowsRational());
    const bool getDualRaySuccess = d_spx.getDualFarkasRational(dualRay);
    Assert(getDualRaySuccess);

    // Get the primal solution for the rows, except for the strict variable
    for (int rowIdx = 0; rowIdx < d_spx.numRowsRational() - 1; rowIdx++)
    {
      const ArithVar v = d_rowToArithVar.at(rowIdx);
      const VarStatus varStatus = d_spx.basisRowStatus(rowIdx);
      // We now know that this variable is non-basic
      if (varStatus != VarStatus::BASIC) nonBasicVars.add(v);
      ExactSoplex::extractVarValue<VariableType::ROW>(rowIdx, sol, &dualRay);
    }

    // Get the col activity for the cols
    for (int colIdx = 0; colIdx < d_spx.numColsRational(); colIdx++)
    {
      const ArithVar v = d_colToArithVar.at(colIdx);
      // We already know this col's value from some other side,
      // no need to recompute it
      if (nonBasicVars.isMember(v) > 0) continue;

      const VarStatus varStatus = d_spx.basisColStatus(colIdx);
      // We now know that this variable is non-basic
      if (varStatus != VarStatus::BASIC) nonBasicVars.add(v);
      ExactSoplex::extractVarValue<VariableType::COL>(colIdx, sol);
    }

#if 0

    // For efficiency in the following iterations, we make sure
    // to only iterate over the non-zero rows of the dual ray
    std::vector<int> nzRows;
    nzRows.reserve(dualRay.dim());
    for (int i = 0; i < dualRay.dim(); i++)
    {
      if (dualRay[i].is_zero()) continue;
      nzRows.emplace_back(i);
    }

    //  Multiply the Farkas ray by the row coefficients to get the column
    //  violations: ray * A If the result is non-zero, the sign indicates the
    //  bound that caused the violation.
    std::unordered_map<int, soplex::Rational> colViolations;
    for (const int r : nzRows)
    {
      const soplex::SVectorRational& rowVec = d_spx.rowVectorRational(r);
      for (int cnz = 0; cnz < rowVec.size(); cnz++)
      {
        const int c = rowVec.index(cnz);
        if (c == d_spx.numColsRational() - 1) continue;
        colViolations[c] += dualRay[r] * rowVec.value(cnz);
      }
    }
    for (const auto& [c, violation] : colViolations)
    {
      const ArithVar v = d_colToArithVar.at(c);
      if (violation > 0 && d_vars.hasUpperBound(v))
      {
        sol.newNonBasis.add(v);
        sol.newValues.set(v, d_vars.getUpperBound(v));
      }
      else if (violation < 0 && d_vars.hasLowerBound(v))
      {
        sol.newNonBasis.add(v);
        sol.newValues.set(v, d_vars.getLowerBound(v));
      }
      else if (!violation.is_zero())
      {
        sol.newBasis.add(v);
      }
    }

    // For each conflict rows, check whether it belongs to the basic
    // (its value is completely determined by other conflict vars)
    // or non-basic (it is at a bound and contributes to the conflict)
    for (const int r : nzRows)
    {
      const soplex::SVectorRational& rowVec = d_spx.rowVectorRational(r);
      bool markNonBasic = false;
      for (int cnz = 0; cnz < rowVec.size(); cnz++)
      {
        const int c = rowVec.index(cnz);
        const ArithVar v = d_colToArithVar.at(c);
        if (!sol.newNonBasis.isMember(v))
        {
          markNonBasic = true;
          break;
        }
      }
      const ArithVar v = d_rowToArithVar.at(r);
      if (!markNonBasic)
      {
        sol.newBasis.add(v);
      }
      else
      {
        sol.newNonBasis.add(v);
        sol.newValues.set(
            v,
            dualRay[r] > 0 ? d_vars.getLowerBound(v) : d_vars.getUpperBound(v));
      }
    }

    // soplex::SoPlex newSpx;
    // newSpx.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
    // newSpx.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
    // newSpx.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
    // newSpx.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
    // for (int i = 0; i < d_spx.numColsRational(); i++)
    // {
    //   soplex::LPColRational col;
    //   d_spx.getColRational(i, col);
    //   if (colViolations.count(i) == 0 || colViolations[i] == 0)
    //   {
    //     newSpx.addColRational({0.0,
    //                            soplex::DSVectorRational(),
    //                            soplex::infinity,
    //                            -soplex::infinity});
    //   }
    //   else
    //   {
    //     bool useLower = colViolations[i] < 0;
    //     bool useUpper = colViolations[i] > 0;
    //     newSpx.addColRational({0.0,
    //                            soplex::DSVectorRational(),
    //                            useUpper ? col.upper() : soplex::infinity,
    //                            useLower ? col.lower() : -soplex::infinity});
    //   }
    // }
    // for (const int r : nzRows)
    // {
    //   soplex::LPRowRational row;
    //   d_spx.getRowRational(r, row);
    //   const bool useLhs = dualRay[r] > 0;
    //   newSpx.addRowRational({useLhs ? row.lhs() : -soplex::infinity,
    //                          row.rowVector(),
    //                          useLhs ? soplex::infinity : row.rhs()});
    // }
    // newSpx.writeFileRational(
    //     "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file.ilp");
#endif

    return sol;
  }
  else
  {
    Unimplemented();
  }

  // Forcefully remove all non-basic variables that we identified from the
  // basis
  for (const ArithVar v : nonBasicVars)
  {
    if (sol.newBasis.isMember(v)) sol.newBasis.remove(v);
  }
  // If the strict variable is basic, we need to add some other non-basic
  // variable to the basis to maintain the same number of basic variables
  if (isStrictBasic)
  {
    for (const ArithVar v : nonBasicVars)
    {
      if (!sol.newBasis.isMember(v))
      {
        sol.newBasis.add(v);
        break;
      }
    }
  }

  // Make sure to remove all strict rows that we know are non-basic
  return sol;
}

void ExactSoplexStrict::adjustValue(const int rowIdx,
                                    soplex::Rational& value,
                                    const soplex::Rational& strictValue) const
{
  Unimplemented();
}

void ExactSoplex::printSolution(const external::Solution& sol) const
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

void ExactSoplex::tryCut(int, CutInfo&) { Unimplemented(); }

external::MipResult ExactSoplex::solveMIP(bool al)
{
  return external::MipResult::MipUnknown;
}

double ExactSoplex::sumInfeasibilities(SoPlex& prob, bool mip) const
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

external::LinResult ExactSoplex::solveRelaxation()
{
  Assert(!d_solvedRelaxation);

  // glp_erase_prob(d_realProb);
  // glp_copy_prob(d_realProb, d_inputProb, GLP_OFF);

  using SpxStatus = SolverStatus;

  // d_spx.clearBasis();
  // std::cout << "OBJ:" << d_spx.objValueReal() << std::endl;

  SolverStatus res = SolverStatus::UNKNOWN;
  try
  {
    res = d_spx.optimize();
  }
  catch (const soplex::SPxException&)
  {
    return external::LinResult::LinExhausted;
  }

  // d_spx.writeFileRational(
  //     "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file.lp");
  // d_spx.writeFileRational(
  //     "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file.mps");

  d_stats.d_refinements << d_spx.numRefinements();
  std::size_t precision =
      d_spx.numPrecisionBoosts() == 0 ? sizeof(double) * 8 : 167;
  for (int i = 1; i < d_spx.numPrecisionBoosts(); i++)
  {
    precision = static_cast<std::size_t>(
        precision * d_spx.realParam(SoPlex::PRECISION_BOOSTING_FACTOR));
  }
  d_stats.d_precision << precision;

  switch (res)
  {
    case SpxStatus::OPTIMAL:
    case SpxStatus::UNBOUNDED:
      // std::cout << "OBJ" << d_spx.objValueReal() << std::endl;
      Assert(d_spx.hasSol());
      d_solvedRelaxation = true;
      // Check the value of the last column (strict variable)
      return isStrictVarZero() ? external::LinResult::LinInfeasible
                               : external::LinResult::LinFeasible;
    case SpxStatus::INFEASIBLE:
      d_solvedRelaxation = true;
      return external::LinResult::LinInfeasible;
    case SpxStatus::ABORT_ITER:
    case SpxStatus::ABORT_TIME:
    case SpxStatus::ABORT_CYCLING: return external::LinResult::LinExhausted;
    default: return external::LinResult::LinUnknown;
  }
}

std::vector<const CutInfo*> ExactSoplex::getValidCuts(const NodeLog& con)
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

ArithVar ExactSoplex::getBranchVar(const NodeLog& con) const
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

ArithVar ExactSoplex::_getArithVar(int nid, int M, int ind) const
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

external::ExternalSimplex* ExactSimplex::mkExactSimplexSolver(
    CVC5_UNUSED const ArithVariables& vars,
    CVC5_UNUSED TreeLog& l,
    CVC5_UNUSED external::SimplexStatistics& s,
    const bool useStrict)
{
#ifdef CVC5_USE_SOPLEX
  if (useStrict) return new ExactSoplexStrict(vars, l, s);
  return new ExactSoplexEpsilon(vars, l, s);
#else
  Unimplemented() << "Exact simplex solver requires SoPlex";
#endif
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex/No soplex Glue code. */

void attempt()
{
#if 0  // For debug
  for (int colIdx = 0; colIdx < d_spx.numColsRational(); colIdx++)
  {
    soplex::LPColRational col(d_spx.numColsRational());
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
  for (int rowIdx = 0; rowIdx < d_spx.numRowsRational(); rowIdx++)
  {
    soplex::LPRowRational row(d_spx.numRowsRational());
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
}