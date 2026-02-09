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
#include "theory/arith/linear/exact_simplex.h"

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

struct AuxInfo
{
  TreeLog* tl;
  int pivotLimit;
  int branchLimit;
  int branchDepth;
  external::MipResult term; /* terminatation */
};

enum SlackReplace
{
  SlackUndef = 0,
  SlackLB,
  SlackUB,
  SlackVLB,
  SlackVUB
};

struct VirtualBound
{
  // Either x <= d * y or x >= d * y
  ArithVar x;     // variable being bounded
  Kind k;         // either LEQ or GEQ
  Rational d;     // the multiple on y
  ArithVar y;     // the variable that is the upper bound
  ConstraintP c;  // the original constraint relating x and y

  VirtualBound()
      : x(ARITHVAR_SENTINEL),
        k(Kind::UNDEFINED_KIND),
        d(),
        y(ARITHVAR_SENTINEL),
        c(NullConstraint)
  {
  }
  VirtualBound(ArithVar toBound,
               Kind rel,
               const Rational& coeff,
               ArithVar bounding,
               ConstraintP orig)
      : x(toBound), k(rel), d(coeff), y(bounding), c(orig)
  {
    Assert(k == Kind::LEQ || k == Kind::GEQ);
  }
};

struct CutScratchPad
{
  bool d_failure;  // if the construction was unsuccessful

  /* GOMORY CUTS Datastructures */
  ArithVar d_basic;  // a variable that is basic in the approximate solver
  DenseVector
      d_tabRow;  // a row in the tableau not including d_basic, equal to 0
  DenseMap<ConstraintP>
      d_toBound;  // each variable in toBound maps each variable in tabRow to
                  // either an upper/lower bound

  /* MIR CUTS Datastructures */
  DenseMap<SlackReplace> d_slacks;  // The x'[i] selected for x[i]
  DenseMap<VirtualBound> d_vub;     // Virtual upper bounds.
  DenseMap<VirtualBound> d_vlb;     // Virtual lower bounds.
  DenseMap<Rational> d_compRanges;

  // a sum of rows in the tableau, with possible replacements for fixed
  // sum aggLhs[i] x[i] = aggRhs;
  DenseVector d_agg;
  // Takes agg and replaces x[i] with a slack variable x'[i]
  // Takes agg and replaces x[i] with a slack variable x'[i]
  // sum modLhs[i] x'[i] = modRhs;
  DenseVector d_mod;

  // Takes mod, and performs c-Mir on it
  // sum alpha[i] x'[i] <= beta
  DenseVector d_alpha;

  /* The constructed cut */
  // sum cut[i] x[i] <= cutRhs
  DenseVector d_cut;
  Kind d_cutKind;

  /* The constraints used throughout construction. */
  std::set<ConstraintP> d_explanation;  // use pointer equality
  CutScratchPad() { clear(); }
  void clear()
  {
    d_failure = false;
    d_basic = ARITHVAR_SENTINEL;
    d_tabRow.purge();
    d_toBound.purge();

    d_slacks.purge();
    d_vub.purge();
    d_vlb.purge();
    d_compRanges.purge();

    d_agg.purge();
    d_mod.purge();
    d_alpha.purge();

    d_cut.purge();
    d_cutKind = Kind::UNDEFINED_KIND;
    d_explanation.clear();
  }
};

struct GmiInfo;
struct MirInfo;
class BranchCutInfo;

class ExactSoplex : public ExactSimplex
{
 public:
  ExactSoplex(const ArithVariables& v, TreeLog& l, ExactStatistics& s);

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

  /**
   * Attempts to make the row vector vec on the pad.
   * If this is not in the row span of the original tableau this
   * raises the failure flag.
   */
  bool attemptConstructTableRow(int node, int M, const PrimitiveVec& vec);
  bool guessCoefficientsConstructTableRow(int node,
                                          int M,
                                          const PrimitiveVec& vec);
  bool guessCoefficientsConstructTableRow(int node,
                                          int M,
                                          const PrimitiveVec& vec,
                                          const Integer& D);
  bool gaussianElimConstructTableRow(int node, int M, const PrimitiveVec& vec);

  /* This is a guess of a vector in the row span of the tableau.
   * Attempt to cancel out all of the variables.
   * returns true if this is constructable.
   */
  bool guessIsConstructable(const DenseMap<Rational>& guess) const;

  /**
   * Loads a vector of statuses into a dense map over bounds.
   * returns true on failure.
   */
  bool loadToBound(int node,
                   int M,
                   int len,
                   int* inds,
                   int* statuses,
                   DenseMap<ConstraintP>& toBound) const;

  /** checks the cut on the pad for whether it is sufficiently similar to cut.
   */
  bool checkCutOnPad(int nid, const CutInfo& cut) const;

  /** turns the pad into a node and creates an explanation. */
  // std::pair<Node, Node> makeCutNodes(int nid, const CutInfo& cut) const;

  // true means failure!
  // BRANCH CUTS
  bool attemptBranchCut(int nid, const BranchCutInfo& br);

  // GOMORY CUTS
  bool attemptGmi(int nid, const GmiInfo& gmi);
  /** tries to turn the information on the pad into a cut. */
  bool constructGmiCut();

  // MIR CUTS
  bool attemptMir(int nid, const MirInfo& mir);
  bool applyCMIRRule(int nid, const MirInfo& mir);
  bool makeRangeForComplemented(int nid, const MirInfo& mir);
  bool loadSlacksIntoPad(int nid, const MirInfo& mir);
  bool loadVirtualBoundsIntoPad(int nid, const MirInfo& mir);
  bool loadRowSumIntoAgg(int nid, int M, const PrimitiveVec& mir);
  bool buildModifiedRow(int nid, const MirInfo& mir);
  bool constructMixedKnapsack();
  bool replaceSlacksOnCuts();
  bool loadVB(int nid, int M, int j, int ri, bool wantUb, VirtualBound& tmp);

  double sumInfeasibilities(/* glp_prob */ soplex::SoPlex& prob,
                            bool mip) const;

  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static constexpr double SMALL_FIXED_DELTA = .000000001;
  static constexpr double TOLERENCE = 1 + .000000001;

  /** Returns true if two doubles are roughly equal based on TOLERENCE and
   * SMALL_FIXED_DELTA.*/
  static bool roughlyEqual(double a, double b);

  /**
   * Converts a rational to a continued fraction expansion representation
   * using a maximum number of expansions equal to depth as long as the
   * expression is not roughlyEqual() to 0.
   */
  static std::vector<Integer> rationalToCfe(const Rational& q, int depth);

  /** Converts a continued fraction expansion representation to a rational. */
  static Rational cfeToRational(const std::vector<Integer>& exp);

  /** Estimates a rational as a continued fraction expansion.*/
  static Rational estimateWithCFE(const Rational& q, const Integer& K);

 private:
  const ArithVariables& d_vars;
  TreeLog& d_log;
  ExactStatistics& d_stats;

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

  DenseMap<std::size_t> d_colIndices;

  // NodeLog::RowIdMap d_rootRowIds;
  std::vector<ArithVar> d_auxVars;
  std::vector<ArithVar> d_rowToArithVar;
  // DenseMap<ArithVar> d_rowToArithVar;
  std::vector<ArithVar> d_colToArithVar;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

  CutScratchPad d_pad;

  std::vector<Integer> d_denomGuesses;
};

void ExactSoplex::setPivotLimit(int pl)
{
  Assert(pl >= 0);
  d_pivotLimit = pl;
}

void ExactSoplex::setBranchingDepth(int bd)
{
  Assert(bd >= 0);
  d_maxDepth = bd;
}

void ExactSoplex::setBranchOnVariableLimit(int bl)
{
  Assert(bl >= 0);
  d_branchLimit = bl;
}

bool ExactSoplex::roughlyEqual(double a, double b)
{
  if (a == 0)
  {
    return -SMALL_FIXED_DELTA <= b && b <= SMALL_FIXED_DELTA;
  }
  else if (b == 0)
  {
    return -SMALL_FIXED_DELTA <= a && a <= SMALL_FIXED_DELTA;
  }
  else
  {
    return std::abs(b / a) <= TOLERENCE && std::abs(a / b) <= TOLERENCE;
  }
}

Rational ExactSoplex::cfeToRational(const std::vector<Integer>& exp)
{
  if (exp.empty())
  {
    return Rational(0);
  }
  else
  {
    Rational result = exp.back();
    std::vector<Integer>::const_reverse_iterator exp_iter = exp.rbegin();
    std::vector<Integer>::const_reverse_iterator exp_end = exp.rend();
    ++exp_iter;
    while (exp_iter != exp_end)
    {
      result = result.inverse();
      const Integer& i = *exp_iter;
      result += i;
      ++exp_iter;
    }
    return result;
  }
}

std::vector<Integer> ExactSoplex::rationalToCfe(const Rational& q, int depth)
{
  std::vector<Integer> mods;
  if (!q.isZero())
  {
    Rational carry = q;
    for (int i = 0; i <= depth; ++i)
    {
      Assert(!carry.isZero());
      mods.push_back(Integer());
      Integer& back = mods.back();
      back = carry.floor();
      Trace("rationalToCfe") << "  cfe[" << i << "]: " << back << std::endl;
      carry -= back;
      if (carry.isZero())
      {
        break;
      }
      else if (ExactSoplex::roughlyEqual(carry.getDouble(), 0.0))
      {
        break;
      }
      else
      {
        carry = carry.inverse();
      }
    }
  }
  return mods;
}

Rational ExactSoplex::estimateWithCFE(const Rational& r, const Integer& K)
{
  Trace("estimateWithCFE") << "estimateWithCFE(" << r << ", " << K << ")"
                           << std::endl;
  // references
  // page 4:
  // http://carlossicoli.free.fr/C/Cassels_J.W.S.-An_introduction_to_diophantine_approximation-University_Press(1965).pdf
  // http://en.wikipedia.org/wiki/Continued_fraction
  Assert(K >= Integer(1));
  if (r.getDenominator() <= K)
  {
    return r;
  }

  // current numerator and denominator that has not been resolved in the cfe
  Integer num = r.getNumerator(), den = r.getDenominator();
  Integer quot, rem;

  unsigned t = 0;
  // For a sequence of candidate solutions q_t/p_t
  // we keep only 3 time steps: 0[prev], 1[current], 2[next]
  // timesteps with a fake timestep 0 (p is 0 and q is 1)
  // at timestep 1
  Integer p[3];  // h
  Integer q[3];  // k
  // load the first 3 time steps manually
  p[0] = 0;
  q[0] = 1;  // timestep -2
  p[1] = 1;
  q[1] = 0;  // timestep -1

  Integer::floorQR(quot, rem, num, den);
  num = den;
  den = rem;

  q[2] = q[0] + quot * q[1];
  p[2] = p[0] + quot * p[1];
  Trace("estimateWithCFE") << "  cfe[" << t << "]: " << p[2] << "/" << q[2]
                           << std::endl;
  while (q[2] <= K)
  {
    p[0] = p[1];
    p[1] = p[2];
    q[0] = q[1];
    q[1] = q[2];

    Integer::floorQR(quot, rem, num, den);
    num = den;
    den = rem;

    p[2] = p[0] + quot * p[1];
    q[2] = q[0] + quot * q[1];
    ++t;
    Trace("estimateWithCFE")
        << "  cfe[" << t << "]: " << p[2] << "/" << q[2] << std::endl;
  }

  Integer k = (K - q[0]).floorDivideQuotient(q[1]);
  Rational cand_prev(p[0] + k * p[1], q[0] + k * q[1]);
  Rational cand_curr(p[1], q[1]);
  Rational dist_prev = (cand_prev - r).abs();
  Rational dist_curr = (cand_curr - r).abs();
  if (dist_prev <= dist_curr)
  {
    Trace("estimateWithCFE")
        << cand_prev << " is closer than " << cand_curr << std::endl;
    return cand_prev;
  }
  else
  {
    Trace("estimateWithCFE")
        << cand_curr << " is closer than " << cand_prev << std::endl;
    return cand_curr;
  }
}

std::optional<Rational> ExactSoplex::estimateWithCFE(double d,
                                                     const Integer& D) const
{
  if (std::optional<Rational> from_double = Rational::fromDouble(d))
  {
    return estimateWithCFE(*from_double, D);
  }
  return std::optional<Rational>();
}

void ExactSoplex::printSolution(const external::Solution& sol) const
{
  std::cout << "{  ";
  for (const auto v : sol.newBasis)
  {
    std::cout << d_vars.asNode(v).getName() << "\n";
  }
  std::cout << "}\n";
  for (const auto v : sol.newValues)
  {
    std::cout << d_vars.asNode(v).getName() << " = " << sol.newValues[v]
              << "\n";
  }
}

std::optional<Rational> ExactSoplex::estimateWithCFE(double d) const
{
  return estimateWithCFE(d, Integer(s_defaultMaxDenom));
}

#if 0
Kind glpk_type_to_kind(int glpk_cut_type)
{
  switch (glpk_cut_type)
  {
    case GLP_LO: return Kind::GEQ;
    case GLP_UP: return Kind::LEQ;
    case GLP_FX: return Kind::EQUAL;
    case GLP_DB:
    case GLP_FR:
    default: return Kind::UNDEFINED_KIND;
  }
}

#ifdef CVC5_ASSERTIONS
static CutInfoKlass fromGlpkClass(int klass)
{
  switch (klass)
  {
    case GLP_RF_GMI: return GmiCutKlass;
    case GLP_RF_MIR: return MirCutKlass;
    case GLP_RF_COV:
    case GLP_RF_CLQ:
    default: return UnknownKlass;
  }
}
#endif
#endif

ExactSoplex::ExactSoplex(const ArithVariables& var,
                         TreeLog& l,
                         ExactStatistics& s)
    : d_vars(var),
      d_log(l),
      d_stats(s),
      d_pivotLimit(std::numeric_limits<int>::max()),
      d_branchLimit(std::numeric_limits<int>::max()),
      d_maxDepth(std::numeric_limits<int>::max()),
      d_solvedRelaxation(false),
      d_solvedMIP(false)
{
  d_denomGuesses.push_back(Integer(1 << 22));
  d_denomGuesses.push_back(Integer(ExactSoplex::s_defaultMaxDenom));
  d_denomGuesses.push_back(Integer(1ul << 29));
  d_denomGuesses.push_back(Integer(1ul << 31));

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

  d_auxVars.reserve(d_vars.getNumberOfVariables());
  d_colToArithVar.reserve(d_vars.getNumberOfVariables() / 2);

  // Assign each variable to a row and column variable as it appears in the
  // input
  for (auto vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end;
       ++vi)
  {
    ArithVar v = *vi;
    if (d_vars.isAuxiliary(v))
    {
      d_auxVars.emplace_back(v);
      Trace("approx") << "Row vars: " << v << "<->" << d_auxVars.size() - 1
                      << std::endl;
    }
    else
    {
      d_colToArithVar.emplace_back(v);
      d_colIndices.set(v, d_colIndices.size());
      Trace("approx") << "Col vars: " << v << "<->" << d_colIndices.size() - 1
                      << std::endl;
    }
  }
  Assert(!d_auxVars.empty());
  Assert(!d_colToArithVar.empty());

  // The number of cols must accommodate for the non-aux variables as well as
  // the additional strict variable t
  // Todo: better estimation of the number of rows
  soplex::LPRowSetRational rows(static_cast<int>(d_auxVars.size()) * 2);
  soplex::LPColSetRational cols(static_cast<int>(d_colToArithVar.size()) + 1);

  d_rowToArithVar.reserve(d_auxVars.size() * 2);

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (ArithVar v : d_auxVars)
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
        if (hasStrictLb(v)) vec.add(cols.max() - 1, 1);
        rows.add({varToLb(v), vec, soplex::infinity});
        d_rowToArithVar.emplace_back(v);
      }
      if (d_vars.hasUpperBound(v))
      {
        // If strict, add -t, and in any case add the split row
        if (hasStrictUB(v)) vec.add(cols.max() - 1, -1);
        rows.add({-soplex::infinity, vec, varToUb(v)});
        d_rowToArithVar.emplace_back(v);
      }
    }
    else
    {
      rows.add({varToLb(v), vec, varToUb(v)});
      d_rowToArithVar.emplace_back(v);
    }
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

    cols.add({0.0, soplex::DSVectorRational(), varToUb(v), varToLb(v)});

    if (hasStrictLb(v))
    {
      soplex::DSVectorRational vec(2);
      vec.add(static_cast<int>(d_colIndices[v]), 1);
      vec.add(cols.max() - 1, 1);
      rows.add({varToLb(v), vec, soplex::infinity});
      d_rowToArithVar.emplace_back(ARITHVAR_SENTINEL);
    }
    if (hasStrictUB(v))
    {
      soplex::DSVectorRational vec(2);
      vec.add(static_cast<int>(d_colIndices[v]), 1);
      vec.add(cols.max() - 1, -1);
      rows.add({-soplex::infinity, vec, varToUb(v)});
      d_rowToArithVar.emplace_back(ARITHVAR_SENTINEL);
    }
  }

  // Add the strict variable t
  cols.add({-1, soplex::DSVectorRational(), 1, 0});

  // Add both columns and rows to the LP
  d_spx.addColsRational(cols);
  d_spx.addRowsRational(rows);

  d_spx.writeFile(
      "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/file.lp");
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

    if (!d_vars.boundsAreEqual(v)
        && (d_vars.hasLowerBound(v) || d_vars.hasUpperBound(v)))
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
  for (const ArithVar v : d_auxVars)
  {
    assert(d_vars.isAuxiliary(v));

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

void ExactSoplex::setOptCoeffs(const ArithRatPairVec& ref)
{
  // DenseMap<double> nbCoeffs;
  std::unordered_map<int, soplex::Rational> nbCoeffs;
  nbCoeffs.reserve(d_spx.numCols());

  for (auto i = ref.begin(), iend = ref.end(); i != iend; ++i)
  {
    const ArithVar v = i->first;
    const Rational& q = i->second;

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
        soplex::Rational coeff = constant.getValue().getValue().get_mpq_t();
        const auto it = nbCoeffs.find(colIndex);
        if (it != nbCoeffs.end())
        {
          it->second += coeff;
        }
        else
        {
          nbCoeffs.emplace(colIndex, coeff);
        }
      }
    }
    else
    {
      int colIndex = d_colIndices[v];
      soplex::Rational coeff = q.getValue().get_mpq_t();
      const auto it = nbCoeffs.find(colIndex);
      if (it != nbCoeffs.end())
      {
        it->second += coeff;
      }
      else
      {
        nbCoeffs.emplace(colIndex, coeff);
      }
    }
  }
  for (const auto& [colIndex, coeff] : nbCoeffs)
  {
    d_spx.changeObjRational(colIndex, coeff);
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

void ExactSoplex::printSoplexStatus(int status, std::ostream& out)
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

external::Solution ExactSoplex::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);

  external::Solution sol;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

  // TODO: reimplement this for mip
  // glp_prob* prob = mip ? d_mipProb : d_realProb;

  using VarStatus = soplex::SPxSolverBase<double>::VarStatus;

  std::vector<VarStatus> rows, cols;
  rows.resize(d_spx.numRows());
  cols.resize(d_spx.numCols());
  d_spx.getBasis(rows.data(), cols.data());

  soplex::Rational value;
  mpq_class mpq_value;
  std::size_t colIdx = 0;
  for (const VarStatus colState : cols)
  {
    // Reached the strict var, we can stop
    if (colIdx >= d_colToArithVar.size()) break;
    const ArithVar v = d_colToArithVar.at(colIdx);
    switch (colState)
    {
      case VarStatus::BASIC:
        Trace("approx") << "basic" << std::endl;
        newBasis.add(v);
        d_spx.getColActivityRational(colIdx, value);
        mpq_value = mpq_class{value.backend().data()};
        if (d_vars.hasLowerBound(v)
            && d_vars.getLowerBound(v).getNoninfinitesimalPart().getValue()
                   == mpq_value)
        {
          newValues.set(v, d_vars.getLowerBound(v));
        }
        else if (d_vars.hasUpperBound(v)
                 && d_vars.getUpperBound(v).getNoninfinitesimalPart().getValue()
                        == mpq_value)
        {
          newValues.set(v, d_vars.getUpperBound(v));
        }
        else
        {
          newValues.set(v, DeltaRational(mpq_value));
        }
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
        newValues.set(v, DeltaRational(0, 0));
        break;
      default:
        d_spx.getColActivityRational(colIdx, value);
        newValues.set(v, DeltaRational(mpq_class{value.backend().data()}));
    }
    colIdx++;
  }

  std::size_t rowIdx = 0;
  for (const VarStatus rowState : rows)
  {
    // Reached the strict var, we can stop
    const ArithVar v = d_rowToArithVar.at(rowIdx);
    if (v == ARITHVAR_SENTINEL) continue;
    switch (rowState)
    {
      case VarStatus::BASIC:
        Trace("approx") << "basic" << std::endl;
        // Multiple rows could point to the same variable, need to chek
        if (!newBasis.isMember(v)) newBasis.add(v);
        d_spx.getRowActivityRational(rowIdx, value);
        mpq_value = mpq_class{value.backend().data()};
        if (d_vars.hasLowerBound(v)
            && d_vars.getLowerBound(v).getNoninfinitesimalPart().getValue()
                   == mpq_value)
        {
          newValues.set(v, d_vars.getLowerBound(v));
        }
        else if (d_vars.hasUpperBound(v)
                 && d_vars.getUpperBound(v).getNoninfinitesimalPart().getValue()
                        == mpq_value)
        {
          newValues.set(v, d_vars.getUpperBound(v));
        }
        else
        {
          newValues.set(v, DeltaRational(mpq_value));
        }
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
        newValues.set(v, DeltaRational(0, 0));
        break;
      default:
        d_spx.getRowActivityRational(rowIdx, value);
        newValues.set(v, DeltaRational(mpq_class{value.backend().data()}));
    }
    rowIdx++;
  }

  printSolution(sol);
  return sol;
}

double ExactSoplex::sumInfeasibilities(SoPlex& prob, bool mip) const
{
  /* compute the sum of dual infeasibilities */
  double infeas = 0.0;

  // for (ArithVariables::var_iterator i = d_vars.var_begin(),
  //                                   i_end = d_vars.var_end();
  //      i != i_end;
  //      ++i)
  // {
  //   ArithVar vi = *i;
  //   bool isAux = d_vars.isAuxiliary(vi);
  //   int glpk_index = isAux ? d_rowIndices[vi] : d_colIndices[vi];
  //
  //   double newAssign;
  //   if (mip)
  //   {
  //     Unimplemented() << "MPI is not implemented for exact solver";
  //     // newAssign = (isAux ? glp_mip_row_val(prob, glpk_index)
  //     //                    : glp_mip_col_val(prob, glpk_index));
  //   }
  //   else
  //   {
  //     newAssign = (isAux ? glp_get_row_prim(prob, glpk_index)
  //                        : glp_get_col_prim(prob, glpk_index));
  //   }
  //
  //   double ub = isAux ? prob.getViolation glp_get_row_ub(prob, glpk_index)
  //                     : glp_get_col_ub(prob, glpk_index);
  //
  //   double lb = isAux ? glp_get_row_lb(prob, glpk_index)
  //                     : glp_get_col_lb(prob, glpk_index);
  //
  //   if (ub != +DBL_MAX)
  //   {
  //     if (newAssign > ub)
  //     {
  //       double ubinf = newAssign - ub;
  //       infeas += ubinf;
  //       Trace("approx::soi")
  //           << "ub inf" << vi << " " << ubinf << " " << infeas << std::endl;
  //     }
  //   }
  //   if (lb != -DBL_MAX)
  //   {
  //     if (newAssign < lb)
  //     {
  //       double lbinf = lb - newAssign;
  //       infeas += lbinf;
  //
  //       Trace("approx::soi")
  //           << "lb inf" << vi << " " << lbinf << " " << infeas << std::endl;
  //     }
  //   }
  // }

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

  using SpxStatus = soplex::SPxSolverBase<double>::Status;
  soplex::VectorRational x(d_colToArithVar.size() + 1);

  const SpxStatus res = d_spx.optimize();
  switch (res)
  {
    case SpxStatus::OPTIMAL:
      d_spx.getPrimalRational(x);
      d_solvedRelaxation = true;
      return x[d_colToArithVar.size()].is_zero()
                 ? external::LinResult::LinInfeasible
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

struct MirInfo : public CutInfo
{
  /** a sum of input rows. */
  PrimitiveVec row_sum;

  /* the delta used */
  double delta;

  /* all of these are length vars == N+M*/
  int nvars;
  char* cset;
  char* subst;
  int* vlbRows;
  int* vubRows;
  MirInfo(int execOrd, int ord)
      : CutInfo(MirCutKlass, execOrd, ord),
        nvars(0),
        cset(NULL),
        subst(NULL),
        vlbRows(NULL),
        vubRows(NULL)
  {
  }

  ~MirInfo() { clearSets(); }
  void clearSets()
  {
    if (cset != NULL)
    {
      delete[] cset;
      delete[] subst;
      delete[] vlbRows;
      delete[] vubRows;
      cset = NULL;
      nvars = 0;
    }
  }
  void initSet()
  {
    Assert(d_N >= 0);
    Assert(d_mAtCreation >= 0);
    clearSets();

    int vars = 1 + d_N + d_mAtCreation;

    cset = new char[1 + vars];
    subst = new char[1 + vars];
    vlbRows = new int[1 + vars];
    vubRows = new int[1 + vars];
  }
};

struct GmiInfo : public CutInfo
{
  int basic;
  PrimitiveVec tab_row;
  int* tab_statuses;
  /* has the length tab_row.length */

  GmiInfo(int execOrd, int ord)
      : CutInfo(GmiCutKlass, execOrd, ord),
        basic(-1),
        tab_row(),
        tab_statuses(NULL)
  {
    Assert(!initialized_tab());
  }

  ~GmiInfo()
  {
    if (initialized_tab())
    {
      clear_tab();
    }
  }

  bool initialized_tab() const { return tab_statuses != NULL; }

  void init_tab(int N)
  {
    if (initialized_tab())
    {
      clear_tab();
    }
    tab_row.setup(N);
    tab_statuses = new int[1 + N];
  }

  void clear_tab()
  {
    delete[] tab_statuses;
    tab_statuses = NULL;
    tab_row.clear();
    basic = -1;
  }
};

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

external::MipResult ExactSoplex::solveMIP(bool activelyLog)
{
  Assert(d_solvedRelaxation);
  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  AuxInfo aux;
  aux.pivotLimit = d_pivotLimit;
  aux.branchLimit = d_branchLimit;
  aux.branchDepth = d_maxDepth;
  aux.tl = &d_log;
  aux.term = external::MipResult::MipUnknown;

  // TODO: does this reset matter? or is it just logging?
  // d_log.reset(d_rootRowIds);
  if (activelyLog)
  {
    d_log.makeActive();
  }
  else
  {
    d_log.makeInactive();
  }

  // TODO: implement MIP
  Unimplemented() << "TODO";

  // glp_iocp parm;
  // glp_init_iocp(&parm);
  // parm.presolve = GLP_OFF;
  // parm.pp_tech = GLP_PP_NONE;
  // parm.fp_heur = GLP_ON;
  // parm.gmi_cuts = GLP_ON;
  // parm.mir_cuts = GLP_ON;
  // parm.cov_cuts = GLP_ON;
  // parm.cb_func = glpkCallback;
  // parm.cb_info = &aux;
  // parm.msg_lev = GLP_MSG_OFF;
  // if (TraceIsOn("approx-debug"))
  // {
  //   parm.msg_lev = GLP_MSG_ALL;
  // }
  //
  // glp_erase_prob(d_mipProb);
  // glp_copy_prob(d_mipProb, d_realProb, GLP_OFF);
  //
  // int res = glp_intopt(d_mipProb, &parm);
  //
  // Trace("approx::solveMIP")
  //     << "res " << res << " aux.term " << aux.term << std::endl;
  //
  // switch (res)
  // {
  //   case 0:
  //   case GLP_ESTOP:
  //   {
  //     int status = glp_mip_status(d_mipProb);
  //     Trace("approx::") << "status " << status << std::endl;
  //     switch (status)
  //     {
  //       case GLP_OPT:
  //       case GLP_FEAS:
  //         d_solvedMIP = true;
  //         Trace("approx::") << "bingo here!" << std::endl;
  //         return MipBingo;
  //       case GLP_NOFEAS: d_solvedMIP = true; return MipClosed;
  //       default:
  //         if (aux.term == MipBingo)
  //         {
  //           d_solvedMIP = true;
  //           Trace("approx::") << "bingo here?" << std::endl;
  //         }
  //         return aux.term;
  //     }
  //   }
  //   default: return MipUnknown;
  // }
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

bool ExactSoplex::guessIsConstructable(const DenseMap<Rational>& guess) const
{
  // basic variable
  // sum g[i] * x_i
  DenseMap<Rational> g = guess;
  removeAuxillaryVariables(d_vars, g);

  if (TraceIsOn("guessIsConstructable"))
  {
    if (!g.empty())
    {
      Trace("approx::guessIsConstructable")
          << "guessIsConstructable failed " << g.size() << std::endl;
      DenseVector::print(Trace("approx::guessIsConstructable"), g);
      Trace("approx::guessIsConstructable") << std::endl;
    }
  }
  return g.empty();
}

bool ExactSoplex::loadToBound(int nid,
                              int M,
                              int len,
                              int* inds,
                              int* statuses,
                              DenseMap<ConstraintP>& toBound) const
{
  Unimplemented() << "load to bounds";
  //
  // for (int i = 1; i <= len; ++i)
  // {
  //   int status = statuses[i];
  //   int ind = inds[i];
  //   ArithVar v = _getArithVar(nid, M, ind);
  //   ConstraintP c = NullConstraint;
  //   if (v == ARITHVAR_SENTINEL)
  //   {
  //     return true;
  //   }
  //
  //   switch (status)
  //   {
  //     case GLP_NL: c = d_vars.getLowerBoundConstraint(v); break;
  //     case GLP_NU:
  //     case GLP_NS:  // upper bound sufficies for fixed variables
  //       c = d_vars.getUpperBoundConstraint(v);
  //       break;
  //     case GLP_NF:
  //     default: return true;
  //   }
  //   if (c == NullConstraint)
  //   {
  //     Trace("approx::") << "couldn't find " << v << " @ " << nid <<
  //     std::endl; return true;
  //   }
  //   Assert(c != NullConstraint);
  //   toBound.set(v, c);
  // }
  return false;
}

bool ExactSoplex::checkCutOnPad(int nid, const CutInfo& cut) const
{
  Trace("approx::checkCutOnPad")
      << "checkCutOnPad(" << nid << ", " << cut.getId() << ")" << std::endl;

  const DenseMap<Rational>& constructedLhs = d_pad.d_cut.lhs;
  const Rational& constructedRhs = d_pad.d_cut.rhs;
  std::unordered_set<ArithVar> visited;

  if (constructedLhs.empty())
  {
    Trace("approx::checkCutOnPad") << "its empty?" << std::endl;
    return true;
  }
  if (cut.getKind() != d_pad.d_cutKind)
  {
    Trace("approx::checkCutOnPad") << "rel doesn't match" << std::endl;
    return true;
  }

  const PrimitiveVec& cv = cut.getCutVector();
  for (int i = 1; i <= cv.len; ++i)
  {
    int ind = cv.inds[i];  // this is always a structural variable
    double coeff = cv.coeffs[i];

    if (ind > d_colToArithVar.size())
    {
      return true;
    }
    ArithVar x = d_colToArithVar[ind];
    // if(x == ARITHVAR_SENTINEL){ return true; }
    visited.insert(x);

    if (!constructedLhs.isKey(x))
    {
      if (TraceIsOn("approx::checkCutOnPad"))
      {
        Trace("approx::checkCutOnPad")
            << " didn't find key for " << x << std::endl;
        cut.print(Trace("approx::checkCutOnPad"));
        Trace("approx::checkCutOnPad") << std::endl;
        d_pad.d_cut.print(Trace("approx::checkCutOnPad"));
        Trace("approx::checkCutOnPad") << std::endl;
      }
      return true;
    }

    const Rational& onConstructed = constructedLhs[x];

    Trace("approx::checkCutOnPad") << ind << " " << coeff << " " << std::endl;
    Trace("approx::checkCutOnPad")
        << " " << x << " " << onConstructed << std::endl;

    if (!roughlyEqual(coeff, onConstructed.getDouble()))
    {
      Trace("approx::checkCutOnPad") << "coeff failure" << std::endl;
      return true;
    }
  }
  if (visited.size() != constructedLhs.size())
  {
    Trace("approx::checkCutOnPad") << "size mismatch" << std::endl;
    return true;
  }

  if (!roughlyEqual(cut.getRhs(), constructedRhs.getDouble()))
  {
    Trace("approx::checkCutOnPad") << "norm rhs is off " << cut.getRhs() << " "
                                   << constructedRhs << std::endl;
    return true;
  }
  return false;
}

bool ExactSoplex::attemptBranchCut(int nid, const BranchCutInfo& br_cut)
{
  d_pad.clear();

  const PrimitiveVec& cut_vec = br_cut.getCutVector();
  int structural = cut_vec.inds[1];
  Assert(roughlyEqual(cut_vec.coeffs[1], +1.0));

  ArithVar x = getArithVarFromStructural(structural);
  d_pad.d_failure = (x == ARITHVAR_SENTINEL);
  if (d_pad.d_failure)
  {
    return true;
  }

  Kind brKind = br_cut.getKind();

  d_pad.d_failure = (brKind != Kind::LEQ && brKind != Kind::GEQ);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_cutKind = brKind;
  d_pad.d_cut.lhs.set(x, Rational(1));

  Rational& rhs = d_pad.d_cut.rhs;
  std::optional<Rational> br_cut_rhs = Rational::fromDouble(br_cut.getRhs());
  if (!br_cut_rhs)
  {
    return true;
  }

  rhs = estimateWithCFE(*br_cut_rhs, Integer(1));
  d_pad.d_failure = !rhs.isIntegral();
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = checkCutOnPad(nid, br_cut);
  if (d_pad.d_failure)
  {
    return true;
  }

  return false;
}

bool ExactSoplex::attemptGmi(int nid, const GmiInfo& gmi)
{
  d_pad.clear();

  d_pad.d_cutKind = Kind::GEQ;

  int M = gmi.getMAtCreation();
  ArithVar b = _getArithVar(nid, M, gmi.basic);
  d_pad.d_failure = (b == ARITHVAR_SENTINEL);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = !d_vars.isIntegerInput(b);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_basic = b;

  const PrimitiveVec& tab = gmi.tab_row;
  d_pad.d_failure = attemptConstructTableRow(nid, M, tab);
  if (d_pad.d_failure)
  {
    return true;
  }

  int* statuses = gmi.tab_statuses;
  DenseMap<ConstraintP>& toBound = d_pad.d_toBound;
  d_pad.d_failure = loadToBound(nid, M, tab.len, tab.inds, statuses, toBound);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = constructGmiCut();
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = checkCutOnPad(nid, gmi);
  if (d_pad.d_failure)
  {
    return true;
  }

  return false;
}

bool ExactSoplex::applyCMIRRule(int nid, const MirInfo& mir)
{
  const DenseMap<Rational>& compRanges = d_pad.d_compRanges;

  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  Rational& b = d_pad.d_alpha.rhs;

  std::optional<Rational> delta = estimateWithCFE(mir.delta);
  if (!delta)
  {
    return true;
  }

  d_pad.d_failure = (delta->sgn() <= 0);
  if (d_pad.d_failure)
  {
    return true;
  }

  Trace("approx::mir") << "applyCMIRRule() " << delta << " " << mir.delta
                       << std::endl;

  DenseMap<Rational>::const_iterator iter, iend;
  iter = alpha.begin(), iend = alpha.end();
  for (; iter != iend; ++iter)
  {
    ArithVar v = *iter;
    const Rational& curr = alpha[v];
    Rational next = curr / *delta;
    if (compRanges.isKey(v))
    {
      b -= curr * compRanges[v];
      alpha.set(v, -next);
    }
    else
    {
      alpha.set(v, next);
    }
  }
  b = b / *delta;

  Rational roundB = (b + Rational(1, 2)).floor();
  d_pad.d_failure = (b - roundB).abs() < Rational(1, 90);
  // intensionally more generous than glpk here
  if (d_pad.d_failure)
  {
    return true;
  }

  Rational one(1);
  Rational fb = b.floor_frac();
  Rational one_sub_fb = one - fb;
  Rational gamma = (one / one_sub_fb);

  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  Rational& beta = d_pad.d_cut.rhs;

  iter = alpha.begin(), iend = alpha.end();
  for (; iter != iend; ++iter)
  {
    ArithVar v = *iter;
    const Rational& a_j = alpha[v];
    if (d_vars.isIntegerInput(v))
    {
      Rational floor_aj = a_j.floor();
      Rational frac_aj = a_j.floor_frac();
      if (frac_aj <= fb)
      {
        cut.set(v, floor_aj);
      }
      else
      {
        Rational tmp = ((frac_aj - fb) / one_sub_fb);
        cut.set(v, floor_aj + tmp);
      }
    }
    else
    {
      cut.set(v, a_j * gamma);
    }
  }
  beta = b.floor();

  iter = cut.begin(), iend = cut.end();
  for (; iter != iend; ++iter)
  {
    ArithVar v = *iter;
    if (compRanges.isKey(v))
    {
      Rational neg = -cut[v];
      beta += neg * compRanges[v];
      cut.set(v, neg);
    }
  }

  return false;
}

bool ExactSoplex::attemptMir(int nid, const MirInfo& mir)
{
  d_pad.clear();

  d_pad.d_cutKind = Kind::LEQ;

  // virtual bounds must be done before slacks
  d_pad.d_failure = loadVirtualBoundsIntoPad(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = loadSlacksIntoPad(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = loadRowSumIntoAgg(nid, mir.getMAtCreation(), mir.row_sum);
  if (d_pad.d_failure)
  {
    return true;
  }

  removeFixed(d_vars, d_pad.d_agg, d_pad.d_explanation);

  d_pad.d_failure = buildModifiedRow(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = constructMixedKnapsack();
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = makeRangeForComplemented(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = applyCMIRRule(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  d_pad.d_failure = replaceSlacksOnCuts();
  if (d_pad.d_failure)
  {
    return true;
  }

  removeAuxillaryVariables(d_vars, d_pad.d_cut.lhs);

  d_pad.d_failure = checkCutOnPad(nid, mir);
  if (d_pad.d_failure)
  {
    return true;
  }

  return false;
  // return makeCutNodes(nid, mir);
}

/** Returns true on failure. */
bool ExactSoplex::loadVB(
    int nid, int M, int j, int ri, bool wantUb, VirtualBound& tmp)
{
  if (ri <= 0)
  {
    return true;
  }

  Trace("glpk::loadVB") << "loadVB() " << std::endl;

  ArithVar rowVar = _getArithVar(nid, M, ri);
  ArithVar contVar = _getArithVar(nid, M, j);
  if (rowVar == ARITHVAR_SENTINEL)
  {
    Trace("glpk::loadVB") << "loadVB() "
                          << " rowVar is ARITHVAR_SENTINEL " << rowVar
                          << std::endl;
    return true;
  }
  if (contVar == ARITHVAR_SENTINEL)
  {
    Trace("glpk::loadVB") << "loadVB() "
                          << " contVar is ARITHVAR_SENTINEL " << contVar
                          << std::endl;
    return true;
  }

  if (!d_vars.isAuxiliary(rowVar))
  {
    Trace("glpk::loadVB") << "loadVB() "
                          << " rowVar is not auxilliary " << rowVar
                          << std::endl;
    return true;
  }
  // is integer is correct here
  if (d_vars.isInteger(contVar))
  {
    Trace("glpk::loadVB") << "loadVB() contVar is integer " << contVar
                          << std::endl;
    return true;
  }

  ConstraintP lb = d_vars.getLowerBoundConstraint(rowVar);
  ConstraintP ub = d_vars.getUpperBoundConstraint(rowVar);

  if (lb != NullConstraint && ub != NullConstraint)
  {
    Trace("glpk::loadVB") << "loadVB() lb and ub are both NULL " << lb << " "
                          << ub << std::endl;
    return true;
  }

  ConstraintP rcon = lb == NullConstraint ? ub : lb;
  if (rcon == NullConstraint)
  {
    Trace("glpk::loadVB") << "loadVB() rcon is NULL " << rcon << std::endl;
    return true;
  }

  if (!rcon->getValue().isZero())
  {
    Trace("glpk::loadVB") << "loadVB() rcon value is not 0 " << rcon->getValue()
                          << std::endl;
    return true;
  }

  if (!d_vars.hasNode(rowVar))
  {
    Trace("glpk::loadVB") << "loadVB() does not have node " << rowVar
                          << std::endl;
    return true;
  }

  Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(rowVar));
  if (p.size() != 2)
  {
    Trace("glpk::loadVB") << "loadVB() polynomial is not binary: "
                          << p.getNode() << std::endl;
    return true;
  }

  Monomial first = p.getHead(), second = p.getTail().getHead();
  Rational c1 = first.getConstant().getValue();
  Rational c2 = second.getConstant().getValue();
  Node nx1 = first.getVarList().getNode();
  Node nx2 = second.getVarList().getNode();

  if (!d_vars.hasArithVar(nx1))
  {
    Trace("glpk::loadVB") << "loadVB() does not have a variable for nx1: "
                          << nx1 << std::endl;
    return true;
  }
  if (!d_vars.hasArithVar(nx2))
  {
    Trace("glpk::loadVB") << "loadVB() does not have a variable for nx2 " << nx2
                          << std::endl;
    return true;
  }
  ArithVar x1 = d_vars.asArithVar(nx1), x2 = d_vars.asArithVar(nx2);

  Assert(x1 != x2);
  Assert(!c1.isZero());
  Assert(!c2.isZero());

  Trace("glpk::loadVB") << " lb " << lb << " ub " << ub << " rcon " << rcon
                        << " x1 " << x1 << " x2 " << x2 << " c1 " << c1
                        << " c2 " << c2 << std::endl;

  ArithVar iv = (x1 == contVar) ? x2 : x1;
  Rational& cc = (x1 == contVar) ? c1 : c2;
  Rational& ic = (x1 == contVar) ? c2 : c1;

  Trace("glpk::loadVB") << " cv " << contVar << " cc " << cc << " iv " << iv
                        << " c2 " << ic << std::endl;

  if (!d_vars.isIntegerInput(iv))
  {
    Trace("glpk::loadVB") << "loadVB() iv is not an integer input variable "
                          << iv << std::endl;
    return true;
  }
  // cc * cv + ic * iv <= 0 or
  // cc * cv + ic * iv <= 0

  if (rcon == ub)
  {  // multiply by -1
    cc = -cc;
    ic = -ic;
  }
  Trace("glpk::loadVB") << " cv " << contVar << " cc " << cc << " iv " << iv
                        << " c2 " << ic << std::endl;

  // cc * cv + ic * iv >= 0
  // cc * cv >= -ic * iv
  // if cc < 0:
  //   cv <= -ic/cc * iv
  // elif cc > 0:
  //   cv >= -ic/cc * iv
  Assert(!cc.isZero());
  Rational d = -ic / cc;
  Trace("glpk::loadVB") << d << " " << cc.sgn() << std::endl;
  bool nowUb = cc.sgn() < 0;
  if (wantUb != nowUb)
  {
    Trace("glpk::loadVB") << "loadVB() wantUb is not nowUb " << wantUb << " "
                          << nowUb << std::endl;

    return true;
  }

  Kind rel = wantUb ? Kind::LEQ : Kind::GEQ;

  tmp = VirtualBound(contVar, rel, d, iv, rcon);
  Trace("glpk::loadVB") << "loadVB() was successful" << std::endl;
  return false;
}

bool ExactSoplex::loadVirtualBoundsIntoPad(int nid, const MirInfo& mir)
{
  Assert(mir.vlbRows != NULL);
  Assert(mir.vubRows != NULL);

  int N = mir.getN();
  int M = mir.getMAtCreation();

  // Load the virtual bounds first
  VirtualBound tmp;
  for (int j = 1; j <= N + M; ++j)
  {
    if (!loadVB(nid, M, j, mir.vlbRows[j], false, tmp))
    {
      if (d_pad.d_vlb.isKey(tmp.x))
      {
        return true;
      }
      d_pad.d_vlb.set(tmp.x, tmp);
    }
    else if (mir.vlbRows[j] > 0)
    {
      Trace("approx::mir") << "expected vlb to work" << std::endl;
    }
    if (!loadVB(nid, M, j, mir.vubRows[j], true, tmp))
    {
      if (d_pad.d_vub.isKey(tmp.x))
      {
        return true;
      }
      d_pad.d_vub.set(tmp.x, tmp);
    }
    else if (mir.vubRows[j] > 0)
    {
      Trace("approx::mir") << "expected vub to work" << std::endl;
    }
  }
  return false;
}

bool ExactSoplex::loadSlacksIntoPad(int nid, const MirInfo& mir)
{
  Assert(mir.vlbRows != NULL);
  Assert(mir.vubRows != NULL);

  int N = mir.getN();
  int M = mir.getMAtCreation();

  bool useVB;
  // Load the virtual bounds first
  SlackReplace rep;
  bool lb;
  ConstraintP b;
  Trace("approx::mir") << "loadSlacksIntoPad(): N=" << N << ", M=" << M
                       << std::endl;
  for (int j = 1; j <= N + M; ++j)
  {
    ArithVar v = _getArithVar(nid, M, j);
    if (v == ARITHVAR_SENTINEL)
    {
      Trace("approx::mir") << " for: " << j << " no variable" << std::endl;
      continue;
    }
    rep = SlackUndef;
    char sub = mir.subst[j];
    switch (sub)
    {
      case 'L':
      case 'U':
        lb = (sub == 'L');
        useVB = lb ? (mir.vlbRows[j] > 0) : (mir.vubRows[j] > 0);
        if (useVB)
        {
          if (lb ? d_pad.d_vlb.isKey(v) : d_pad.d_vub.isKey(v))
          {
            rep = lb ? SlackVLB : SlackVUB;
          }
        }
        else
        {
          b = lb ? d_vars.getLowerBoundConstraint(v)
                 : d_vars.getUpperBoundConstraint(v);
          if (b != NullConstraint)
          {
            if (b->getValue().infinitesimalIsZero())
            {
              rep = lb ? SlackLB : SlackUB;
            }
          }
        }

        Trace("approx::mir") << " for: " << j << ", " << v;
        Trace("approx::mir")
            << " " << ((rep != SlackUndef) ? "succ" : "fail") << " ";
        Trace("approx::mir") << sub << " " << rep << " " << mir.vlbRows[j]
                             << " " << mir.vubRows[j] << std::endl;
        if (rep != SlackUndef)
        {
          d_pad.d_slacks.set(v, rep);
        }
        break;
      case '?': continue;
      default:
        Trace("approx::mir")
            << " for: " << j << " got subst " << (int)sub << std::endl;
        continue;
    }
  }
  return false;
}

bool ExactSoplex::replaceSlacksOnCuts()
{
  std::vector<ArithVar> virtualVars;

  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  Rational& cutRhs = d_pad.d_cut.rhs;

  DenseMap<Rational>::const_iterator iter, iend;
  iter = cut.begin(), iend = cut.end();
  for (; iter != iend; ++iter)
  {
    ArithVar x = *iter;
    SlackReplace rep = d_pad.d_slacks[x];
    if (d_vars.isIntegerInput(x))
    {
      Assert(rep == SlackLB || rep == SlackUB);
      Rational& a = cut.get(x);

      const DeltaRational& bound =
          (rep == SlackLB) ? d_vars.getLowerBound(x) : d_vars.getUpperBound(x);
      Assert(bound.infinitesimalIsZero());
      Rational prod = a * bound.getNoninfinitesimalPart();
      if (rep == SlackLB)
      {
        cutRhs += prod;
      }
      else
      {
        cutRhs -= prod;
        a = -a;
      }
    }
    else if (rep == SlackVLB)
    {
      virtualVars.push_back(d_pad.d_vlb[x].y);
    }
    else if (rep == SlackVUB)
    {
      virtualVars.push_back(d_pad.d_vub[x].y);
    }
  }

  for (size_t i = 0; i < virtualVars.size(); ++i)
  {
    ArithVar x = virtualVars[i];
    if (!cut.isKey(x))
    {
      cut.set(x, Rational(0));
    }
  }

  iter = cut.begin(), iend = cut.end();
  for (; iter != iend; ++iter)
  {
    ArithVar x = *iter;
    if (!d_vars.isIntegerInput(x))
    {
      SlackReplace rep = d_pad.d_slacks[x];
      Rational& a = cut.get(x);
      switch (rep)
      {
        case SlackLB:
        {
          const DeltaRational& bound = d_vars.getLowerBound(x);
          Assert(bound.infinitesimalIsZero());
          cutRhs += a * bound.getNoninfinitesimalPart();
        }
        break;
        case SlackUB:
        {
          const DeltaRational& bound = d_vars.getUpperBound(x);
          Assert(bound.infinitesimalIsZero());
          cutRhs -= a * bound.getNoninfinitesimalPart();
          a = -a;
        }
        break;
        case SlackVLB:
        case SlackVUB:
        {
          bool lb = (rep == SlackVLB);
          const VirtualBound& vb = lb ? d_pad.d_vlb[x] : d_pad.d_vub[x];
          ArithVar y = vb.y;
          Assert(vb.x == x);
          Assert(cut.isKey(y));
          Rational& ycoeff = cut.get(y);
          if (lb)
          {
            ycoeff -= a * vb.d;
          }
          else
          {
            ycoeff += a * vb.d;
            a = -a;
          }
        }
        break;
        default: return true;
      }
    }
  }
  removeZeroes(cut);
  return false;
}

bool ExactSoplex::loadRowSumIntoAgg(int nid, int M, const PrimitiveVec& row_sum)
{
  DenseMap<Rational>& lhs = d_pad.d_agg.lhs;
  d_pad.d_agg.rhs = Rational(0);

  int len = row_sum.len;
  for (int i = 1; i <= len; ++i)
  {
    int aux_ind = row_sum.inds[i];  // auxillary index
    double coeff = row_sum.coeffs[i];
    ArithVar x = _getArithVar(nid, M, aux_ind);
    if (x == ARITHVAR_SENTINEL)
    {
      return true;
    }
    std::optional<Rational> c = estimateWithCFE(coeff);
    if (!c)
    {
      return true;
    }

    if (lhs.isKey(x))
    {
      lhs.get(x) -= *c;
    }
    else
    {
      lhs.set(x, -(*c));
    }
  }

  Trace("approx::mir") << "beg loadRowSumIntoAgg() 1" << std::endl;
  if (TraceIsOn("approx::mir"))
  {
    DenseVector::print(Trace("approx::mir"), lhs);
  }
  removeAuxillaryVariables(d_vars, lhs);
  Trace("approx::mir") << "end loadRowSumIntoAgg() 1" << std::endl;

  if (TraceIsOn("approx::mir"))
  {
    Trace("approx::mir") << "loadRowSumIntoAgg() 2" << std::endl;
    DenseVector::print(Trace("approx::mir"), lhs);
    Trace("approx::mir") << "end loadRowSumIntoAgg() 2" << std::endl;
  }

  for (int i = 1; i <= len; ++i)
  {
    int aux_ind = row_sum.inds[i];  // auxillary index
    double coeff = row_sum.coeffs[i];
    ArithVar x = _getArithVar(nid, M, aux_ind);
    Assert(x != ARITHVAR_SENTINEL);
    std::optional<Rational> c = estimateWithCFE(coeff);
    if (!c)
    {
      return true;
    }
    Assert(!lhs.isKey(x));
    lhs.set(x, *c);
  }

  if (TraceIsOn("approx::mir"))
  {
    Trace("approx::mir") << "loadRowSumIntoAgg() 2" << std::endl;
    DenseVector::print(Trace("approx::mir"), lhs);
    Trace("approx::mir") << "end loadRowSumIntoAgg() 3" << std::endl;
  }
  return false;
}

bool ExactSoplex::buildModifiedRow(int nid, const MirInfo& mir)
{
  const DenseMap<Rational>& agg = d_pad.d_agg.lhs;
  const Rational& aggRhs = d_pad.d_agg.rhs;
  DenseMap<Rational>& mod = d_pad.d_mod.lhs;
  Rational& modRhs = d_pad.d_mod.rhs;

  Trace("approx::mir") << "buildModifiedRow()"
                       << " |agg|=" << d_pad.d_agg.lhs.size()
                       << " |mod|=" << d_pad.d_mod.lhs.size()
                       << " |slacks|=" << d_pad.d_slacks.size()
                       << " |vlb|=" << d_pad.d_vub.size()
                       << " |vub|=" << d_pad.d_vlb.size() << std::endl;

  mod.addAll(agg);
  modRhs = aggRhs;
  DenseMap<Rational>::const_iterator iter, iend;
  for (iter = agg.begin(), iend = agg.end(); iter != iend; ++iter)
  {
    ArithVar x = *iter;
    const Rational& c = mod[x];
    if (!d_pad.d_slacks.isKey(x))
    {
      Trace("approx::mir") << "missed x: " << x << std::endl;
      return true;
    }
    SlackReplace rep = d_pad.d_slacks[x];
    switch (rep)
    {
      case SlackLB:  // skip for now
      case SlackUB: break;
      case SlackVLB: /* x[k] = lb[k] * x[kk] + x'[k] */
      case SlackVUB: /* x[k] = ub[k] * x[kk] - x'[k] */
      {
        Assert(!d_vars.isIntegerInput(x));
        bool ub = (rep == SlackVUB);
        const VirtualBound& vb = ub ? d_pad.d_vub[x] : d_pad.d_vlb[x];
        Assert(vb.x == x);
        ArithVar y = vb.y;
        Rational prod = c * vb.d;
        if (mod.isKey(y))
        {
          mod.get(x) += prod;
        }
        else
        {
          mod.set(y, prod);
        }
        if (ub)
        {
          mod.set(x, -c);
        }
        Assert(vb.c != NullConstraint);
        d_pad.d_explanation.insert(vb.c);
      }
      break;
      default: return true;
    }
  }
  removeZeroes(
      mod); /* if something cancelled we don't want it in the explanation */
  for (iter = mod.begin(), iend = mod.end(); iter != iend; ++iter)
  {
    ArithVar x = *iter;
    if (!d_pad.d_slacks.isKey(x))
    {
      return true;
    }

    SlackReplace rep = d_pad.d_slacks[x];
    switch (rep)
    {
      case SlackLB: /* x = lb + x' */
      case SlackUB: /* x = ub - x' */
      {
        bool ub = (rep == SlackUB);
        ConstraintP b = ub ? d_vars.getUpperBoundConstraint(x)
                           : d_vars.getLowerBoundConstraint(x);

        Assert(b != NullConstraint);
        Assert(b->getValue().infinitesimalIsZero());
        const Rational& c = mod.get(x);
        modRhs -= c * b->getValue().getNoninfinitesimalPart();
        if (ub)
        {
          mod.set(x, -c);
        }
        d_pad.d_explanation.insert(b);
      }
      break;
      case SlackVLB: /* handled earlier */
      case SlackVUB: break;
      default: return true;
    }
  }
  removeZeroes(mod);
  return false;
}

bool ExactSoplex::makeRangeForComplemented(int nid, const MirInfo& mir)
{
  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  int M = mir.getMAtCreation();
  int N = mir.getN();
  DenseMap<Rational>& compRanges = d_pad.d_compRanges;

  int complemented = 0;

  for (int j = 1; j <= M + N; ++j)
  {
    if (mir.cset[j] != 0)
    {
      complemented++;
      ArithVar x = _getArithVar(nid, M, j);
      if (!alpha.isKey(x))
      {
        return true;
      }
      if (!d_vars.isIntegerInput(x))
      {
        return true;
      }
      Assert(d_pad.d_slacks.isKey(x));
      Assert(d_pad.d_slacks[x] == SlackLB || d_pad.d_slacks[x] == SlackUB);

      ConstraintP lb = d_vars.getLowerBoundConstraint(x);
      ConstraintP ub = d_vars.getUpperBoundConstraint(x);

      if (lb == NullConstraint)
      {
        return true;
      }
      if (ub == NullConstraint)
      {
        return true;
      }

      if (!lb->getValue().infinitesimalIsZero())
      {
        return true;
      }
      if (!ub->getValue().infinitesimalIsZero())
      {
        return true;
      }

      const Rational& uval = ub->getValue().getNoninfinitesimalPart();
      const Rational& lval = lb->getValue().getNoninfinitesimalPart();

      d_pad.d_explanation.insert(lb);
      d_pad.d_explanation.insert(ub);

      Rational u = uval - lval;
      // u is the same for both rep == LP and rep == UB
      if (compRanges.isKey(x))
      {
        return true;
      }
      compRanges.set(x, u);
    }
  }

  Trace("approx::mir") << "makeRangeForComplemented()" << complemented
                       << std::endl;
  return false;
}

bool ExactSoplex::constructMixedKnapsack()
{
  const DenseMap<Rational>& mod = d_pad.d_mod.lhs;
  const Rational& modRhs = d_pad.d_mod.rhs;
  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  Rational& beta = d_pad.d_alpha.rhs;

  Assert(alpha.empty());
  beta = modRhs;

  unsigned intVars = 0;
  unsigned remain = 0;
  unsigned dropped = 0;
  DenseMap<Rational>::const_iterator iter, iend;
  for (iter = mod.begin(), iend = mod.end(); iter != iend; ++iter)
  {
    ArithVar v = *iter;
    const Rational& c = mod[v];
    Assert(!c.isZero());
    if (d_vars.isIntegerInput(v))
    {
      intVars++;
      alpha.set(v, c);
    }
    else if (c.sgn() < 0)
    {
      remain++;
      alpha.set(v, c);
    }
    else
    {
      dropped++;
    }
  }

  Trace("approx::mir") << "constructMixedKnapsack() "
                       << " dropped " << dropped << " remain " << remain
                       << " intVars " << intVars << std::endl;
  return intVars == 0;  // if this is 0 we have failed
}

bool ExactSoplex::attemptConstructTableRow(int nid,
                                           int M,
                                           const PrimitiveVec& vec)
{
  bool failed = guessCoefficientsConstructTableRow(nid, M, vec);
  if (failed)
  {
    failed = gaussianElimConstructTableRow(nid, M, vec);
  }

  return failed;
}

bool ExactSoplex::gaussianElimConstructTableRow(int nid,
                                                int M,
                                                const PrimitiveVec& vec)
{
  TimerStat::CodeTimer codeTimer(d_stats.d_gaussianElimConstructTime);
  ++d_stats.d_gaussianElimConstruct;

  ArithVar basic = d_pad.d_basic;
  DenseMap<Rational>& tab = d_pad.d_tabRow.lhs;
  tab.purge();
  d_pad.d_tabRow.rhs = Rational(0);
  Assert(basic != ARITHVAR_SENTINEL);
  Assert(tab.empty());
  Assert(d_pad.d_tabRow.rhs.isZero());

  if (d_vars.isAuxiliary(basic))
  {
    return true;
  }

  if (TraceIsOn("gaussianElimConstructTableRow"))
  {
    Trace("gaussianElimConstructTableRow")
        << "1 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
        << std::endl;
    vec.print(Trace("gaussianElimConstructTableRow"));
    Trace("gaussianElimConstructTableRow")
        << "match " << basic << "(" << d_vars.asNode(basic) << ")" << std::endl;
  }

  std::set<ArithVar> onrow;
  for (int i = 1; i <= vec.len; ++i)
  {
    int ind = vec.inds[i];
    ArithVar var = _getArithVar(nid, M, ind);
    if (var == ARITHVAR_SENTINEL)
    {
      Trace("gaussianElimConstructTableRow")
          << "couldn't find" << ind << " " << M << " " << nid << std::endl;
      return true;
    }
    onrow.insert(var);
  }

  Trace("gaussianElimConstructTableRow")
      << "2 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;

  Matrix<Rational> A;
  A.increaseSizeTo(d_vars.getNumberOfVariables());
  std::vector<std::pair<RowIndex, ArithVar> > rows;
  // load the rows for auxiliary variables into A
  for (ArithVar v : onrow)
  {
    if (d_vars.isAuxiliary(v))
    {
      Assert(d_vars.hasNode(v));

      std::vector<Rational> coeffs;
      std::vector<ArithVar> vars;

      coeffs.push_back(Rational(-1));
      vars.push_back(v);

      Node n = d_vars.asNode(v);
      Polynomial p = Polynomial::parsePolynomial(n);
      Polynomial::iterator j = p.begin(), jend = p.end();
      for (j = p.begin(), jend = p.end(); j != jend; ++j)
      {
        Monomial m = *j;
        if (m.isConstant())
        {
          return true;
        }
        VarList vl = m.getVarList();
        if (!d_vars.hasArithVar(vl.getNode()))
        {
          return true;
        }
        ArithVar x = d_vars.asArithVar(vl.getNode());
        const Rational& q = m.getConstant().getValue();
        coeffs.push_back(q);
        vars.push_back(x);
      }
      RowIndex rid = A.addRow(coeffs, vars);
      rows.push_back(std::make_pair(rid, ARITHVAR_SENTINEL));
    }
  }
  Trace("gaussianElimConstructTableRow")
      << "3 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;

  for (size_t i = 0; i < rows.size(); ++i)
  {
    RowIndex rid = rows[i].first;
    Assert(rows[i].second == ARITHVAR_SENTINEL);

    // substitute previous rows
    for (size_t j = 0; j < i; j++)
    {
      RowIndex prevRow = rows[j].first;
      ArithVar other = rows[j].second;
      Assert(other != ARITHVAR_SENTINEL);
      const Matrix<Rational>::Entry& e = A.findEntry(rid, other);
      if (!e.blank())
      {
        // r_p : 0 = -1 * other + sum a_i x_i
        // rid : 0 =  e * other + sum b_i x_i
        // rid += e * r_p
        //     : 0 = 0 * other + ...
        Assert(!e.getCoefficient().isZero());

        Rational cp = e.getCoefficient();
        Trace("gaussianElimConstructTableRow")
            << "on " << rid << " subst " << cp << "*" << prevRow << " " << other
            << std::endl;
        A.rowPlusRowTimesConstant(rid, prevRow, cp);
      }
    }
    if (TraceIsOn("gaussianElimConstructTableRow"))
    {
      A.printMatrix(Trace("gaussianElimConstructTableRow"));
    }

    // solve the row for anything other than non-basics
    bool solveForBasic = (i + 1 == rows.size());
    Rational q;
    ArithVar s = ARITHVAR_SENTINEL;
    Matrix<Rational>::RowIterator k = A.getRow(rid).begin();
    Matrix<Rational>::RowIterator k_end = A.getRow(rid).end();
    for (; k != k_end; ++k)
    {
      const Matrix<Rational>::Entry& e = *k;
      ArithVar colVar = e.getColVar();
      bool selectColVar = false;
      if (colVar == basic)
      {
        selectColVar = solveForBasic;
      }
      else if (onrow.find(colVar) == onrow.end())
      {
        selectColVar = true;
      }
      if (selectColVar)
      {
        s = colVar;
        q = e.getCoefficient();
      }
    }
    if (s == ARITHVAR_SENTINEL || q.isZero())
    {
      Trace("gaussianElimConstructTableRow")
          << "3 fail gaussianElimConstructTableRow(" << nid << ", " << basic
          << ")" << std::endl;
      return true;
    }
    else
    {
      // 0 = q * s + sum c_i * x_i
      Rational mult = -(q.inverse());
      Trace("gaussianElimConstructTableRow")
          << "selecting " << s << " : complexity " << mult.complexity() << " "
          << mult << std::endl;
      Trace("gaussianElimConstructTableRow")
          << "selecting " << rid << " " << s << std::endl;
      A.multiplyRowByConstant(rid, mult);
      rows[i].second = s;
    }
  }
  Trace("gaussianElimConstructTableRow")
      << "4 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;

  if (rows.empty())
  {
    Trace("gaussianElimConstructTableRow")
        << "4 fail 1 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << std::endl;
    return true;
  }
  RowIndex rid_last = rows.back().first;
  ArithVar rid_var = rows.back().second;
  if (rid_var != basic)
  {
    Trace("gaussianElimConstructTableRow")
        << "4 fail 2 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << std::endl;
    return true;
  }

  Assert(tab.empty());

  Matrix<Rational>::RowIterator k = A.getRow(rid_last).begin();
  Matrix<Rational>::RowIterator k_end = A.getRow(rid_last).end();
  for (; k != k_end; ++k)
  {
    const Matrix<Rational>::Entry& e = *k;
    tab.set(e.getColVar(), e.getCoefficient());
  }
  Trace("gaussianElimConstructTableRow")
      << "5 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;
  if (!tab.isKey(basic))
  {
    Trace("gaussianElimConstructTableRow")
        << "5 fail 1 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << std::endl;
    return true;
  }
  if (tab[basic] != Rational(-1))
  {
    Trace("gaussianElimConstructTableRow")
        << "5 fail 2 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << std::endl;
    return true;
  }

  tab.remove(basic);
  Trace("gaussianElimConstructTableRow")
      << "6 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;

  if (vec.len < 0)
  {
    Trace("gaussianElimConstructTableRow")
        << "6 fail 1 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << std::endl;
    return true;
  }
  if (tab.size() != ((unsigned)vec.len))
  {
    Trace("gaussianElimConstructTableRow")
        << "6 fail 2 gaussianElimConstructTableRow(" << nid << ", " << basic
        << ")" << tab.size() << " " << vec.len << std::endl;
    return true;
  }

  Trace("gaussianElimConstructTableRow")
      << "7 gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << std::endl;

  for (int i = 1; i <= vec.len; ++i)
  {
    int ind = vec.inds[i];
    double coeff = vec.coeffs[i];
    ArithVar var = _getArithVar(nid, M, ind);
    Assert(var != ARITHVAR_SENTINEL);
    if (!tab.isKey(var))
    {
      Trace("gaussianElimConstructTableRow")
          << "7 fail 1 gaussianElimConstructTableRow(" << nid << ", " << basic
          << ")" << std::endl;
      return true;
    }

    double est = tab[var].getDouble();

    if (!ExactSoplex::roughlyEqual(coeff, est))
    {
      Trace("gaussianElimConstructTableRow")
          << "7 fail 2 gaussianElimConstructTableRow(" << nid << ", " << basic
          << ")"
          << " boink on " << ind << " " << var << " " << est << std::endl;
      return true;
    }
    Trace("gaussianElimConstructTableRow")
        << var << " cfe " << coeff << std::endl;
  }

  Trace("gaussianElimConstructTableRow")
      << "gaussianElimConstructTableRow(" << nid << ", " << basic << ")"
      << " superduper" << std::endl;

  return false;
}
bool ExactSoplex::guessCoefficientsConstructTableRow(int nid,
                                                     int M,
                                                     const PrimitiveVec& vec)
{
  for (size_t i = 0; i < d_denomGuesses.size(); ++i)
  {
    const Integer& D = d_denomGuesses[i];
    if (!guessCoefficientsConstructTableRow(nid, M, vec, D))
    {
      d_stats.d_averageGuesses << i + 1;
      Trace("approx::gmi") << "guesseditat " << i << " D=" << D << std::endl;
      return false;
    }
  }
  return true;
}
bool ExactSoplex::guessCoefficientsConstructTableRow(int nid,
                                                     int M,
                                                     const PrimitiveVec& vec,
                                                     const Integer& D)
{
  ArithVar basic = d_pad.d_basic;
  DenseMap<Rational>& tab = d_pad.d_tabRow.lhs;
  tab.purge();
  d_pad.d_tabRow.rhs = Rational(0);
  Assert(basic != ARITHVAR_SENTINEL);
  Assert(tab.empty());
  Assert(d_pad.d_tabRow.rhs.isZero());

  if (TraceIsOn("guessCoefficientsConstructTableRow"))
  {
    Trace("guessCoefficientsConstructTableRow")
        << "attemptConstructTableRow(" << nid << ", " << basic << ",...," << D
        << ")" << std::endl;
    vec.print(Trace("guessCoefficientsConstructTableRow"));
    Trace("guessCoefficientsConstructTableRow")
        << "match " << basic << "(" << d_vars.asNode(basic) << ")" << std::endl;
  }

  tab.set(basic, Rational(-1));
  for (int i = 1; i <= vec.len; ++i)
  {
    int ind = vec.inds[i];
    double coeff = vec.coeffs[i];
    ArithVar var = _getArithVar(nid, M, ind);
    if (var == ARITHVAR_SENTINEL)
    {
      Trace("guessCoefficientsConstructTableRow")
          << "couldn't find" << ind << " " << M << " " << nid << std::endl;
      return true;
    }
    Trace("guessCoefficientsConstructTableRow")
        << "match " << ind << "," << var << "(" << d_vars.asNode(var) << ")"
        << std::endl;

    std::optional<Rational> cfe = estimateWithCFE(coeff, D);
    if (!cfe)
    {
      return true;
    }
    tab.set(var, *cfe);
    Trace("guessCoefficientsConstructTableRow")
        << var << " cfe " << cfe << std::endl;
  }
  if (!guessIsConstructable(tab))
  {
    Trace("guessCoefficientsConstructTableRow")
        << "failed to construct with " << D << std::endl;
    return true;
  }
  tab.remove(basic);
  return false;
}

/* Maps an ArithVar to either an upper/lower bound */
bool ExactSoplex::constructGmiCut()
{
  const DenseMap<Rational>& tabRow = d_pad.d_tabRow.lhs;
  const DenseMap<ConstraintP>& toBound = d_pad.d_toBound;
  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  std::set<ConstraintP>& explanation = d_pad.d_explanation;
  Rational& rhs = d_pad.d_cut.rhs;

  DenseMap<Rational>::const_iterator iter, end;
  Assert(cut.empty());

  // compute beta for a "fake" assignment
  bool anyInf;
  DeltaRational dbeta = sumConstraints(tabRow, toBound, &anyInf);
  const Rational& beta = dbeta.getNoninfinitesimalPart();
  Trace("approx::gmi") << dbeta << std::endl;
  if (anyInf || beta.isIntegral())
  {
    return true;
  }

  Rational one = Rational(1);
  Rational fbeta = beta.floor_frac();
  rhs = fbeta;
  Assert(fbeta.sgn() > 0);
  Assert(fbeta < one);
  Rational one_sub_fbeta = one - fbeta;
  for (iter = tabRow.begin(), end = tabRow.end(); iter != end; ++iter)
  {
    ArithVar x = *iter;
    const Rational& psi = tabRow[x];
    ConstraintP c = toBound[x];
    const Rational& bound = c->getValue().getNoninfinitesimalPart();
    if (d_vars.boundsAreEqual(x))
    {
      // do not add a coefficient
      // implictly substitute the variable w/ its constraint
      std::pair<ConstraintP, ConstraintP> exp = d_vars.explainEqualBounds(x);
      explanation.insert(exp.first);
      if (exp.second != NullConstraint)
      {
        explanation.insert(exp.second);
      }
    }
    else if (d_vars.isIntegerInput(x) && psi.isIntegral())
    {
      // do not add a coefficient
      // nothing to explain
      Trace("approx::gmi") << "skipping " << x << std::endl;
    }
    else
    {
      explanation.insert(c);
      Rational phi;
      Rational alpha = (c->isUpperBound() ? psi : -psi);

      // x - ub <= 0 and lb - x <= 0
      if (d_vars.isIntegerInput(x))
      {
        Assert(!psi.isIntegral());
        // alpha = slack_sgn * psi
        Rational falpha = alpha.floor_frac();
        Assert(falpha.sgn() > 0);
        Assert(falpha < one);
        phi = (falpha <= fbeta) ? falpha
                                : ((fbeta / one_sub_fbeta) * (one - falpha));
      }
      else
      {
        phi = (alpha >= 0) ? alpha : ((fbeta / one_sub_fbeta) * (-alpha));
      }
      Assert(phi.sgn() != 0);
      if (c->isUpperBound())
      {
        cut.set(x, -phi);
        rhs -= phi * bound;
      }
      else
      {
        cut.set(x, phi);
        rhs += phi * bound;
      }
    }
  }
  if (TraceIsOn("approx::gmi"))
  {
    Trace("approx::gmi") << "pre removeSlackVariables";
    d_pad.d_cut.print(Trace("approx::gmi"));
    Trace("approx::gmi") << std::endl;
  }
  removeAuxillaryVariables(d_vars, cut);

  if (TraceIsOn("approx::gmi"))
  {
    Trace("approx::gmi") << "post removeAuxillaryVariables";
    d_pad.d_cut.print(Trace("approx::gmi"));
    Trace("approx::gmi") << std::endl;
  }
  removeFixed(d_vars, d_pad.d_cut, explanation);

  if (TraceIsOn("approx::gmi"))
  {
    Trace("approx::gmi") << "post removeFixed";
    d_pad.d_cut.print(Trace("approx::gmi"));
    Trace("approx::gmi") << std::endl;
  }
  return false;
}

void ExactSoplex::tryCut(int nid, CutInfo& cut)
{
  Assert(!cut.reconstructed());
  Assert(cut.getKlass() != RowsDeletedKlass);
  bool failure = false;
  switch (cut.getKlass())
  {
    case GmiCutKlass:
      failure = attemptGmi(nid, static_cast<const GmiInfo&>(cut));
      break;
    case MirCutKlass:
      failure = attemptMir(nid, static_cast<const MirInfo&>(cut));
      break;
    case BranchCutKlass:
      failure = attemptBranchCut(nid, dynamic_cast<const BranchCutInfo&>(cut));
      break;
    default: break;
  }
  Assert(failure == d_pad.d_failure);

  if (!failure)
  {
    // move the pad to the cut
    cut.setReconstruction(d_pad.d_cut);

    if (cut.getKlass() != BranchCutKlass)
    {
      std::set<ConstraintP>& exp = d_pad.d_explanation;
      ConstraintCPVec asvec(exp.begin(), exp.end());
      cut.swapExplanation(asvec);
    }
  }
  else
  {
    Trace("approx") << "failure " << cut.getKlass() << std::endl;
  }
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End GPLK implementation. */
#endif /*#ifdef CVC5_USE_SOPLEX */

/* Begin GPLK/NOGLPK Glue code. */
namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ExactSimplex* ExactSimplex::mkExactSimplexSolver(
    CVC5_UNUSED const ArithVariables& vars,
    CVC5_UNUSED TreeLog& l,
    CVC5_UNUSED ExactStatistics& s)
{
#ifdef CVC5_USE_SOPLEX
  return new ExactSoplex(vars, l, s);
#else
  Unimplemented() << "Exact simplex solver requires SoPlex";
#endif
}

bool ExactSimplex::enabled()
{
#ifdef CVC5_USE_SOPLEX
  return true;
#else
  return false;
#endif
}

ExactStatistics::ExactStatistics(StatisticsRegistry& sr)
    : d_branchMaxDepth(sr.registerInt("z::approx::branchMaxDepth")),
      d_branchesMaxOnAVar(sr.registerInt("z::approx::branchesMaxOnAVar")),
      d_gaussianElimConstructTime(
          sr.registerTimer("z::approx::gaussianElimConstruct::time")),
      d_gaussianElimConstruct(
          sr.registerInt("z::approx::gaussianElimConstruct::calls")),
      d_averageGuesses(sr.registerAverage("z::approx::averageGuesses"))
{
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End GPLK/NOGLPK Glue code. */
