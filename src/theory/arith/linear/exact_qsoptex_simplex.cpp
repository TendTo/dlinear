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
#include "options/arith_options.h"
#include "proof/eager_proof_generator.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/cut_log.h"
#include "theory/arith/linear/exact_simplex.h"
#include "theory/arith/linear/matrix.h"
#include "theory/arith/linear/normal_form.h"
#include "util/statistics_registry.h"

#ifdef CVC5_USE_QSOPTEX
#include <gmpxx.h>

extern "C" {
#include <qsopt_ex/QSopt_ex.h>  // IWYU pragma: export
}

#include <string>

// These #defines from <qsopt_ex/QSopt_ex.h> cause problems for us
// because they mess with SoPlex's enums.
#undef OPTIMAL
#undef DUAL_INFEASIBLE

#include "theory/arith/linear/partial_model.h"

using VarStatus = char;
using SolverStatus = int;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

/**
 * Cast a mpq_class to a mpq_t.
 * Important definitions from <gmpxx.h> and <gmp.h> (fair use):
 *
 *   mpq_srcptr mpq_class::get_mpq_t() const { return mp; }
 *   mpq_ptr mpq_class::get_mpq_t() { return mp; }
 *
 *   typedef const __mpq_struct *mpq_srcptr;
 *   typedef __mpq_struct *mpq_ptr;
 *   typedef __mpq_struct mpq_t[1];
 *
 * We can cast mpq_ptr to mpq_t * (or mpq_srcptr to const mpq_t *).
 * This is the same as casting (__mpq_struct *) to (__mpq_struct (*)[1]).
 * It's okay because it converts a pointer to a struct, to a pointer to an
 * array of that struct (which is always okay).
 *
 * We can then dereference the (mpq_t *) to obtain a mpq_t.
 * Because mpq_t is an array type, it is still effectively treated as a pointer
 * in certain contexts (such as when returning it from / passing it into a
 * function).
 * This pointer has the same value as the (mpq_t *).
 *
 * We can then take a reference to the mpq_t.
 * The address of this reference also has the same value as the (mpq_t *).
 * @param cla mpq_class to cast
 * @return mpq_t reference
 */
inline const mpq_t& toMpq(const mpq_class& cla)
{
  return *reinterpret_cast<const mpq_t*>(cla.get_mpq_t());
}

inline mpq_t& toMpq(mpq_class& cla)
{
  return *reinterpret_cast<mpq_t*>(cla.get_mpq_t());
}

/**
 * Cast a mpq_t to a mpq_class.
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline const mpq_class& toMpqClass(const mpq_t& mpq)
{
  return reinterpret_cast<const mpq_class&>(mpq);
}

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline mpq_class& toMpqClass(mpq_t& mpq)
{
  return reinterpret_cast<mpq_class&>(mpq);
}

namespace qsopt_ex {

/**
 * Convert a string to a mpq_class.
 * @param str string representation of a rational number
 * @return pointer to a dynamically allocated mpq_class. Must be freed with
 * delete.
 * @warning The caller is responsible for freeing the returned pointer.
 */
mpq_class* StringToMpqPtr(const std::string& str);
/**
 * Convert a string to a mpq_class.
 * @param str string representation of a rational number
 * @return mpq_class object
 */
mpq_class StringToMpq(const std::string& str);
/**
 * Convert a C-string to a mpq_class.
 * @param str C-string representation of a rational number
 * @return pointer to a dynamically allocated mpq_class. Must be freed with
 * delete.
 * @warning The caller is responsible for freeing the returned pointer.
 */
mpq_class* CStringToMpqPtr(const char str[]);
/**
 * Convert a string to a mpq_class.
 * @param str C-string representation of a rational number
 * @return mpq_class object
 */
mpq_class CStringToMpq(const char str[]);

/**
 * A wrapper around an array of mpq_t elements.
 *
 * It is used to pass around arrays of mpq_t, ensuring they are cleaned up after
 * use. The array is allocated by AllocateMpqArray() and freed by
 * FreeMpqArray().
 */
class MpqArray
{
 public:
  /**
   * Construct a new MpqArray object, allocating the array with @p n_elements
   * elements.
   * @param n_elements The number of elements in the array.
   */
  explicit MpqArray(size_t n_elements);
  MpqArray(const MpqArray&) = delete;
  MpqArray(MpqArray&&) = delete;
  MpqArray& operator=(const MpqArray&) = delete;
  MpqArray& operator=(MpqArray&&) = delete;
  /** Destroy the MpqArray object, freeing the array */
  ~MpqArray();
  /**
   * Obtain a constant pointer to the internal @ref array_.
   * @return internal mpq_t array as a constant pointer
   */
  explicit operator const mpq_t*() const { return array_; }

  /**
   * Obtain a pointer to the internal array.
   * @return internal mpq_t array
   */
  explicit operator mpq_t*() { return array_; }

  mpq_t& operator[](const int idx) { return array_[idx]; }

  const mpq_t& operator[](const int idx) const { return array_[idx]; }

  /** @getter{size, array} */
  [[nodiscard]] size_t size() const
  {
    return array_ ? reinterpret_cast<size_t*>(array_)[-1] : 0;
  }

  /**
   * Resize the array to have @p nElements elements.
   *
   * All the previous elements are lost.
   * @param nElements new  number of elements in the array
   */
  void Resize(size_t nElements);

 private:
  mpq_t* array_;  ///< array of mpq_t. It is allocated by AllocateMpqArray() and
                  ///< freed by FreeMpqArray().

  /**
   * Allocate the array with @p n_elements elements.
   *
   * The array has a peculiar structure, where the element at index -1 is the
   * size of the array. All the other @p n_elements elements are mpq_t.
   * @param n_elements The number of elements in the array.
   */
  void AllocateMpqArray(size_t n_elements);

  /** Free the array of mpq_t */
  void FreeMpqArray();
};

void QSXStart();
void QSXFinish();

mpq_class inf_mpq{0, 0};
mpq_class ninf_mpq{0, 0};

void QSXStart()
{
  static bool started = false;
  if (started) return;
  started = true;
  QSexactStart();
  inf_mpq = mpq_class(mpq_INFTY);
  ninf_mpq = mpq_class(mpq_NINFTY);
}

void QSXFinish() { QSexactClear(); }

mpq_class* StringToMpqPtr(const std::string& str)
{
  return CStringToMpqPtr(str.c_str());
}
mpq_class StringToMpq(const std::string& str)
{
  return CStringToMpq(str.c_str());
}
mpq_class* CStringToMpqPtr(const char str[])
{
  mpq_t val;
  mpq_init(val);
  mpq_EGlpNumReadStr(val, str);
  auto result = new mpq_class(val);
  mpq_clear(val);
  return result;
}
mpq_class CStringToMpq(const char str[])
{
  mpq_t val;
  mpq_init(val);
  mpq_EGlpNumReadStr(val, str);
  mpq_class result(val);
  mpq_clear(val);
  return result;
}

void MpqArray::AllocateMpqArray(size_t n_elements)
{
  auto const memSize =
      static_cast<size_t>(sizeof(mpq_t) * n_elements + sizeof(size_t));
  void* newArray = nullptr;
  if (memSize)
  {
    newArray = calloc(1, memSize);
    if (!newArray)
    {
      fprintf(stderr,
              "EXIT: Not enough memory while allocating %zd bytes",
              memSize);
      exit(1);
    }
  }
  size_t* sizeArray = n_elements ? static_cast<size_t*>(newArray) : nullptr;
  if (n_elements) sizeArray[0] = n_elements;

  array_ = reinterpret_cast<mpq_t*>(n_elements ? (sizeArray + 1) : nullptr);
  for (size_t i = 0; i < n_elements; ++i) mpq_init(array_[i]);
}

void MpqArray::FreeMpqArray()
{
  auto* sizeArray = reinterpret_cast<size_t*>(array_);
  if (sizeArray) sizeArray--;
  size_t nElements = sizeArray ? sizeArray[0] : 0;

  for (size_t i = 0; i < nElements; ++i) mpq_clear(array_[i]);
  free(sizeArray);
  array_ = nullptr;
}

MpqArray::MpqArray(size_t n_elements) : array_{nullptr}
{
  AllocateMpqArray(n_elements);
}

MpqArray::~MpqArray() { FreeMpqArray(); }

void MpqArray::Resize(size_t nElements)
{
  {
    FreeMpqArray();
    AllocateMpqArray(nElements);
  }
}

}  // namespace qsopt_ex

class ExactQsoptex : public ExactSimplex
{
 public:
  ExactQsoptex(const ArithVariables& v,
               TreeLog& l,
               external::SimplexStatistics& s);
  virtual ~ExactQsoptex();

  external::LinResult solveRelaxation() override;
  external::Solution extractRelaxation() override
  {
    return extractSolution(false);
  }

  ArithRatPairVec heuristicOptCoeffs() const override;

  external::MipResult solveMIP(bool al) override;
  external::Solution extractMIP() override { return extractSolution(true); }
  void setOptCoeffs(const ArithRatPairVec& ref) override;
  std::vector<const CutInfo*> getValidCuts(const NodeLog& nodes) override
  {
    return {};
  }
  ArithVar getBranchVar(const NodeLog& con) const override;

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
  void freeBasis();

  int numCols() const { return mpq_QSget_colcount(d_qsx); }
  int numRows() const { return mpq_QSget_rowcount(d_qsx); }
  const mpq_class& varToLb(ArithVar v) const;
  const mpq_class& varToUb(ArithVar v) const;
  bool hasStrictBound(ArithVar v) const;
  bool hasStrictLb(ArithVar v) const;
  bool hasStrictUB(ArithVar v) const;

  const mpq_class& getY(const int rowIdx) const
  {
    Assert(d_qsx && d_qsx->lp && d_qsx->lp->pIpiz);
    return toMpqClass(d_qsx->lp->pIpiz[rowIdx]);
  }
  virtual external::Solution extractSolution(bool mip) = 0;
  int guessDir(ArithVar v) const;

  // get this stuff out of here
  void tryCut(int nid, CutInfo& cut) override { Unimplemented(); }

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

  const ArithVariables& d_vars;
  TreeLog& d_log;

  // glp_prob* d_inputProb; /* a copy of the input prob */
  // glp_prob* d_realProb;  /* a copy of the real relaxation output */
  // glp_prob* d_mipProb;   /* a copy of the integer prob */
  mpq_QSprob d_qsx;

  DenseMap<std::size_t> d_colIndices;

  std::vector<ArithVar> d_rowToArithVar;
  std::vector<ArithVar> d_colToArithVar;

  SolverStatus d_status;
  std::vector<mpq_class> d_rhs;
  std::vector<char> d_sense;
  qsopt_ex::MpqArray d_x;
  QSbasis d_basis;

 public:
  enum class VariableType
  {
    ROW,
    COL,
  };

 protected:
  template <VariableType VarType>
  void extractVarValue(int idx, external::Solution& sol);

  virtual bool isStrictVarZero() = 0;

  bool d_solvedRelaxation;
  bool d_solvedMIP;
};

class ExactQsoptexEpsilon : public ExactQsoptex
{
 public:
  ExactQsoptexEpsilon(const ArithVariables& vars,
                      TreeLog& l,
                      external::SimplexStatistics& s);

  external::Solution extractSolution(bool mip) override;

 private:
  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static constexpr double SMALL_FIXED_DELTA =
      std::numeric_limits<double>::epsilon();

  bool isStrictVarZero() override { return false; }
};

class ExactQsoptexStrict : public ExactQsoptex
{
 public:
  ExactQsoptexStrict(const ArithVariables& v,
                     TreeLog& l,
                     external::SimplexStatistics& s);

  void setOptCoeffs(const ArithRatPairVec& ref) override {}

  external::Solution extractSolution(bool mip) override;

 private:
  std::vector<ArithVar> d_strictVars;

  bool isStrictVarZero() override
  {
    if (d_x.size() > 0) return mpq_sgn(d_x[numCols() - 1]) == 0;
    return false;
  }
};

void ExactQsoptex::printSolution(const external::Solution& sol) const
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

ExactQsoptex::ExactQsoptex(const ArithVariables& var,
                           TreeLog& l,
                           external::SimplexStatistics& s)
    : ExactSimplex(s),
      d_vars(var),
      d_log(l),
      d_status(-1),
      d_x(0),
      d_basis{.nstruct = 0, .nrows = 0, .cstat = nullptr, .rstat = nullptr},
      d_solvedRelaxation(false),
      d_solvedMIP(false)
{
  d_stats.d_externalSimplexType.set(
      static_cast<std::underlying_type_t<options::ExternalLPSolver>>(
          options::ExternalLPSolver::QSOPTEX));

  qsopt_ex::QSXStart();
  d_qsx = mpq_QScreate_prob(nullptr, QS_MIN);

  mpq_QSset_param(d_qsx, QS_PARAM_SIMPLEX_MAX_ITERATIONS, d_pivotLimit);

  if (TraceIsOn("approx-debug"))
  {
    mpq_QSset_param(d_qsx, QS_PARAM_SIMPLEX_DISPLAY, 2);
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

ExactQsoptexEpsilon::ExactQsoptexEpsilon(const ArithVariables& vars,
                                         TreeLog& l,
                                         external::SimplexStatistics& s)
    : ExactQsoptex(vars, l, s)
{
  d_stats.d_strict.set(0);

  // Assign each variable to a row and column variable as it appears in the
  // input
  std::vector<int> numNonZeroPerRow;
  std::vector<int> beginRowIdx;
  std::vector<int> colIdxs;
  std::vector<mpq_class> values;

  d_rhs.reserve(d_rowToArithVar.size() * 2);
  numNonZeroPerRow.reserve(d_rowToArithVar.size() * 2);
  beginRowIdx.reserve(d_rowToArithVar.size() * 2);
  colIdxs.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  values.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  d_sense.reserve(d_rowToArithVar.size() * 2);

  std::vector<ArithVar> rowToArithVarSplit;
  rowToArithVarSplit.reserve(d_rowToArithVar.size() * 2);

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (const ArithVar v : d_rowToArithVar)
  {
    Assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    // std::cout << d_vars.asNode(v).getName() << "\n\n";

    numNonZeroPerRow.emplace_back(p.size());
    beginRowIdx.emplace_back(colIdxs.size());
    for (Polynomial::iterator j = p.begin(), end = p.end(); j != end; ++j)
    {
      const Monomial& mono = *j;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      const int colIdx = static_cast<int>(d_colIndices[av]);

      colIdxs.emplace_back(colIdx);
      // TODO: maybe we can just borrow the reference?
      values.emplace_back(constant.getValue().getValue());
    }

    // Case I: we are dealing with a free row. Just add it to capture its
    // behaviour, but set it to -inf
    if (!d_vars.hasEitherBound(v))
    {
      d_rhs.emplace_back(mpq_NINFTY);
      d_sense.emplace_back('G');
      rowToArithVarSplit.emplace_back(v);
      continue;
    }

    // Case II: we are dealing with a row with at least one bound. If both
    // bounds are set, we add the row twice, once for the lower bound and once
    // for the upper bound.
    const bool hasBothBounds =
        d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v);
    if (hasBothBounds)
    {
      beginRowIdx.emplace_back(colIdxs.size());
      colIdxs.insert(colIdxs.end(),
                     colIdxs.end() - numNonZeroPerRow.back(),
                     colIdxs.end());
      values.insert(
          values.end(), values.end() - numNonZeroPerRow.back(), values.end());
      numNonZeroPerRow.emplace_back(numNonZeroPerRow.back());
    }
    if (d_vars.hasLowerBound(v))
    {
      d_rhs.emplace_back(hasStrictLb(v) ? varToLb(v) + SMALL_FIXED_DELTA
                                        : varToLb(v));
      d_sense.emplace_back('G');
      rowToArithVarSplit.emplace_back(v);
    }
    if (d_vars.hasUpperBound(v))
    {
      d_rhs.emplace_back(hasStrictUB(v) ? varToUb(v) - SMALL_FIXED_DELTA
                                        : varToUb(v));
      d_sense.emplace_back('L');
      rowToArithVarSplit.emplace_back(v);
    }
  }

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  for (ArithVar v : d_colToArithVar)
  {
    Assert(!d_vars.isAuxiliary(v));

    if (TraceIsOn("approx-debug"))
    {
      Trace("approx-debug") << v << " ";
      d_vars.printModel(v, Trace("approx-debug"));
    }

    mpq_QSnew_col(
        d_qsx,
        mpq_oneLpNum,
        hasStrictLb(v) ? mpq_class(varToLb(v) + SMALL_FIXED_DELTA).get_mpq_t()
                       : varToLb(v).get_mpq_t(),
        hasStrictUB(v) ? mpq_class(varToUb(v) - SMALL_FIXED_DELTA).get_mpq_t()
                       : varToUb(v).get_mpq_t(),
        nullptr);
  }

  static_assert(sizeof(mpq_class) == sizeof(mpq_t),
                "mpq_class layout assumption broken");
  mpq_QSadd_rows(d_qsx,
                 static_cast<int>(numNonZeroPerRow.size()),
                 numNonZeroPerRow.data(),
                 beginRowIdx.data(),
                 colIdxs.data(),
                 reinterpret_cast<const mpq_t*>(values.data()),
                 reinterpret_cast<const mpq_t*>(d_rhs.data()),
                 d_sense.data(),
                 nullptr);

  d_rowToArithVar = std::move(rowToArithVarSplit);
}

ExactQsoptexStrict::ExactQsoptexStrict(const ArithVariables& vars,
                                       TreeLog& l,
                                       external::SimplexStatistics& s)
    : ExactQsoptex(vars, l, s)
{
  d_stats.d_strict.set(1);

  // Assign each variable to a row and column variable as it appears in the
  // input
  std::vector<int> numNonZeroPerRow;
  std::vector<int> beginRowIdx;
  std::vector<int> colIdxs;
  std::vector<mpq_class> values;

  d_rhs.reserve(d_rowToArithVar.size() * 2);
  numNonZeroPerRow.reserve(d_rowToArithVar.size() * 2);
  beginRowIdx.reserve(d_rowToArithVar.size() * 2);
  colIdxs.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  values.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  d_sense.reserve(d_rowToArithVar.size() * 2);

  std::vector<ArithVar> rowToArithVarSplit;
  rowToArithVarSplit.reserve(d_rowToArithVar.size() * 2);
  d_strictVars.reserve(d_rowToArithVar.size() / 2);

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (const ArithVar v : d_rowToArithVar)
  {
    Assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));

    numNonZeroPerRow.emplace_back(p.size());
    beginRowIdx.emplace_back(colIdxs.size());

    for (Polynomial::iterator j = p.begin(), end = p.end(); j != end; ++j)
    {
      const Monomial& mono = *j;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      const int colIdx = static_cast<int>(d_colIndices[av]);

      colIdxs.emplace_back(colIdx);
      values.emplace_back(constant.getValue().getValue());
    }

    // Case I: we are dealing with a free row. Just add it to capture its
    // behaviour, but set it to -inf
    if (!d_vars.hasEitherBound(v))
    {
      d_rhs.emplace_back(mpq_NINFTY);
      d_sense.emplace_back('G');
      rowToArithVarSplit.emplace_back(v);
      continue;
    }

    const bool isLbStrict = hasStrictLb(v);

    if (d_vars.hasLowerBound(v))
    {
      if (isLbStrict)
      {
        numNonZeroPerRow.back()++;
        colIdxs.emplace_back(d_colToArithVar.size());
        values.emplace_back(-1);
        d_strictVars.emplace_back(v);
      }
      d_rhs.emplace_back(varToLb(v));
      d_sense.emplace_back('G');
      rowToArithVarSplit.emplace_back(v);
    }

    // Case II: we are dealing with a row with at least one bound. If both
    // bounds are set, we add the row twice, once for the lower bound and once
    // for the upper bound.
    const bool hasBothBounds =
        d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v);
    if (hasBothBounds)
    {
      // Insert all cols (except strict col, if present)
      beginRowIdx.emplace_back(colIdxs.size());
      colIdxs.insert(colIdxs.end(),
                     colIdxs.end() - numNonZeroPerRow.back(),
                     isLbStrict ? colIdxs.end() - 1 : colIdxs.end());
      // Insert all values (except strict col, if present)
      values.insert(values.end(),
                    values.end() - numNonZeroPerRow.back(),
                    isLbStrict ? values.end() - 1 : values.end());
      numNonZeroPerRow.emplace_back(isLbStrict ? numNonZeroPerRow.back() - 1
                                               : numNonZeroPerRow.back());
    }

    if (d_vars.hasUpperBound(v))
    {
      if (hasStrictUB(v))
      {
        numNonZeroPerRow.back()++;
        colIdxs.emplace_back(d_colToArithVar.size());
        values.emplace_back(1);
        d_strictVars.emplace_back(v);
      }
      d_rhs.emplace_back(varToUb(v));
      d_sense.emplace_back('L');
      rowToArithVarSplit.emplace_back(v);
    }
  }

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  for (ArithVar v : d_colToArithVar)
  {
    Assert(!d_vars.isAuxiliary(v));

    if (TraceIsOn("approx-debug"))
    {
      Trace("approx-debug") << v << " ";
      d_vars.printModel(v, Trace("approx-debug"));
    }

    const bool isLbStrict = hasStrictLb(v);
    const bool isUbStrict = hasStrictUB(v);

    if (isLbStrict)
    {
      numNonZeroPerRow.emplace_back(2);
      beginRowIdx.emplace_back(colIdxs.size());
      colIdxs.emplace_back(d_colIndices[v]);
      colIdxs.emplace_back(d_colToArithVar.size());
      values.emplace_back(1);
      values.emplace_back(-1);
      d_sense.emplace_back('G');
      d_rhs.emplace_back(varToLb(v));
      rowToArithVarSplit.emplace_back(v);
      d_strictVars.emplace_back(v);
    }

    if (isUbStrict)
    {
      numNonZeroPerRow.emplace_back(2);
      beginRowIdx.emplace_back(colIdxs.size());
      colIdxs.emplace_back(d_colIndices[v]);
      colIdxs.emplace_back(d_colToArithVar.size());
      values.emplace_back(1);
      values.emplace_back(1);
      d_sense.emplace_back('L');
      d_rhs.emplace_back(varToUb(v));
      rowToArithVarSplit.emplace_back(v);
      d_strictVars.emplace_back(v);
    }

    mpq_QSnew_col(d_qsx,
                  mpq_zeroLpNum,
                  isLbStrict ? mpq_NINFTY : varToLb(v).get_mpq_t(),
                  isUbStrict ? mpq_INFTY : varToUb(v).get_mpq_t(),
                  nullptr);
  }

  mpq_QSnew_col(
      d_qsx, mpq_class{-1}.get_mpq_t(), mpq_zeroLpNum, mpq_oneLpNum, nullptr);

  static_assert(sizeof(mpq_class) == sizeof(mpq_t),
                "mpq_class layout assumption broken");
  mpq_QSadd_rows(d_qsx,
                 static_cast<int>(numNonZeroPerRow.size()),
                 numNonZeroPerRow.data(),
                 beginRowIdx.data(),
                 colIdxs.data(),
                 reinterpret_cast<const mpq_t*>(values.data()),
                 reinterpret_cast<const mpq_t*>(d_rhs.data()),
                 d_sense.data(),
                 nullptr);

  d_rowToArithVar = std::move(rowToArithVarSplit);
}

ExactQsoptex::~ExactQsoptex()
{
  mpq_QSfree_prob(d_qsx);
  freeBasis();
}

void ExactQsoptex::freeBasis()
{
  if (d_basis.cstat != nullptr) free(d_basis.cstat);
  if (d_basis.rstat != nullptr) free(d_basis.rstat);
  d_basis.cstat = nullptr;
  d_basis.rstat = nullptr;
  d_basis.nstruct = 0;
  d_basis.nrows = 0;
}

const mpq_class& ExactQsoptex::varToLb(const ArithVar v) const
{
  return d_vars.hasLowerBound(v)
             ? d_vars.getLowerBound(v).getNoninfinitesimalPart().getValue()
             : qsopt_ex::ninf_mpq;
}

const mpq_class& ExactQsoptex::varToUb(const ArithVar v) const
{
  return d_vars.hasUpperBound(v)
             ? d_vars.getUpperBound(v).getNoninfinitesimalPart().getValue()
             : qsopt_ex::inf_mpq;
}

bool ExactQsoptex::hasStrictBound(const ArithVar v) const
{
  return hasStrictLb(v) || hasStrictUB(v);
}

bool ExactQsoptex::hasStrictUB(const ArithVar v) const
{
  return d_vars.hasUpperBound(v)
         && !d_vars.getUpperBound(v).getInfinitesimalPart().isZero();
}

bool ExactQsoptex::hasStrictLb(ArithVar v) const
{
  return d_vars.hasLowerBound(v)
         && !d_vars.getLowerBound(v).getInfinitesimalPart().isZero();
}

int ExactQsoptex::guessDir(const ArithVar v) const
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

ArithRatPairVec ExactQsoptex::heuristicOptCoeffs() const
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
  for (const ArithVar v : d_rowToArithVar)
  {
    Assert(d_vars.isAuxiliary(v));

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

void ExactQsoptex::setOptCoeffs(const ArithRatPairVec& ref)
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
    mpq_QSchange_objcoef(d_qsx, colIndex, coeff.get_mpq_t());
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
template <ExactQsoptex::VariableType VarType>
void ExactQsoptex::extractVarValue(const int idx, external::Solution& sol)
{
  DenseSet& newBasis = sol.newBasis;
  DenseSet& newNonBasis = sol.newNonBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;
  ArithVar v = ARITHVAR_SENTINEL;
  VarStatus varStatus = 'x';

  if constexpr (VarType == VariableType::COL)
  {
    v = d_colToArithVar.at(idx);
    varStatus = d_basis.cstat[idx];
  }
  if constexpr (VarType == VariableType::ROW)
  {
    v = d_rowToArithVar.at(idx);
    varStatus = d_basis.rstat[idx];
  }
  Assert(v != ARITHVAR_SENTINEL);
  Assert(varStatus != 'x');

  if (varStatus == QS_COL_BSTAT_BASIC && !newBasis.isMember(v))
    newBasis.add(v);
  else if (varStatus != QS_COL_BSTAT_BASIC && !newNonBasis.isMember(v))
    newNonBasis.add(v);

  const mpq_t* value = nullptr;
  mpq_class rhs;
  switch (varStatus)
  {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
    case QS_COL_BSTAT_BASIC:
    case QS_COL_BSTAT_FREE:  // Shared with basic
      if (VarType == VariableType::ROW)
      {
        rhs = d_rhs[idx] + (d_sense[idx] == 'G' ? getY(idx) : -getY(idx));
        value = &toMpq(rhs);
      }
      else if (VarType == VariableType::COL)
      {
        value = &d_x[idx];
      }
      Assert(value != nullptr);
      if (d_vars.hasLowerBound(v)
          && d_vars.getLowerBound(v).getNoninfinitesimalPart()
                 >= toMpqClass(*value))
      {
        newValues.set(v, d_vars.getLowerBound(v));
      }
      else if (d_vars.hasUpperBound(v)
               && d_vars.getUpperBound(v).getNoninfinitesimalPart()
                      <= toMpqClass(*value))
      {
        newValues.set(v, d_vars.getUpperBound(v));
      }
      else
      {
        newValues.set(v, DeltaRational(toMpqClass(*value)));
      }
      Assert(!d_vars.hasLowerBound(v)
             || d_vars.getLowerBound(v) <= newValues.get(v));
      Assert(!d_vars.hasUpperBound(v)
             || d_vars.getUpperBound(v) >= newValues.get(v));
      break;
    // For non-basic variables we know the value is at a bound
    // and we can use the d_vars/proper LP bounds directly
    case QS_COL_BSTAT_LOWER:
      Trace("approx-debug") << "non-basic lb" << std::endl;
      // Free rows are set to lower bound, handle them accordingly
      if (!d_vars.hasEitherBound(v))
      {
        if (VarType == VariableType::ROW)
        {
          rhs = d_rhs[idx] + (d_sense[idx] == 'G' ? getY(idx) : -getY(idx));
          value = &toMpq(rhs);
        }
        else if (VarType == VariableType::COL)
        {
          value = &d_x[idx];
        }
        Assert(value != nullptr);
        newValues.set(v, DeltaRational(toMpqClass(*value)));
      }
      else if (VarType == VariableType::ROW)
      {
        if (d_sense[idx] == 'G')
        {
          Assert(d_vars.hasLowerBound(v));
          newValues.set(v, d_vars.getLowerBound(v));
        }
        else if (d_sense[idx] == 'L')
        {
          Assert(d_vars.hasUpperBound(v));
          newValues.set(v, d_vars.getUpperBound(v));
        }
        else
        {
          Unreachable();
        }
      }
      else if (VarType == VariableType::COL)
      {
        Assert(d_vars.hasLowerBound(v));
        newValues.set(v, d_vars.getLowerBound(v));
      }
      else
      {
        Unreachable();
      }
      break;
    case QS_COL_BSTAT_UPPER:
      Trace("approx-debug") << "non-basic ub" << std::endl;
      Assert(d_vars.hasUpperBound(v));
      newValues.set(v, d_vars.getUpperBound(v));
      break;
    default: Unreachable();
  }
}

external::Solution ExactQsoptexEpsilon::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);
  external::Solution sol;

  // TODO: reimplement this for mip
  // glp_prob* prob = mip ? d_mipProb : d_realProb;

  if (d_status == QS_LP_OPTIMAL || d_status == QS_LP_DELTA_OPTIMAL
      || d_status == QS_LP_FEASIBLE || d_status == QS_LP_DELTA_FEASIBLE
      || d_status == QS_LP_UNBOUNDED || d_status == QS_LP_INFEASIBLE)
  {
    for (int colIdx = 0; colIdx < numCols(); colIdx++)
    {
      extractVarValue<VariableType::COL>(colIdx, sol);
    }

    for (int rowIdx = 0; rowIdx < numRows(); rowIdx++)
    {
      const ArithVar v = d_rowToArithVar[rowIdx];
      // We already encountered the nonbasic version of this row, we can skip it
      if (sol.newNonBasis.isMember(v)) continue;
      extractVarValue<VariableType::ROW>(rowIdx, sol);
    }
  }
  else
  {
    // Infeasible solution.
    Unimplemented();
  }

  // Since we have to split range rows, we have to remove those that we
  // erroneously marked as basic and then discovered to be nonbasic
  for (const ArithVar v : sol.newNonBasis)
  {
    if (sol.newBasis.isMember(v)) sol.newBasis.remove(v);
  }

  return sol;
}

external::Solution ExactQsoptexStrict::extractSolution(bool mip)
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);
  external::Solution sol;

  // TODO: reimplement this for mip
  // glp_prob* prob = mip ? d_mipProb : d_realProb;
  bool isStrictBasic = d_basis.cstat[numCols() - 1] == QS_COL_BSTAT_BASIC;

#ifndef NDEBUG
  std::cout << "Strict var value: " << d_x[numCols() - 1] << std::endl;
#endif

  if (isStrictBasic && toMpqClass(d_x[numCols() - 1]) > 0)
  {
    int res = mpq_QSchange_bound(d_qsx, numCols() - 1, 'U', mpq_zeroLpNum);
    Assert(res == 0);
    mpq_class delta = 0;
    res = QSdelta_solver(d_qsx,
                         delta.get_mpq_t(),
                         static_cast<mpq_t*>(d_x),
                         nullptr,
                         &d_basis,
                         nullptr,
                         PRIMAL_SIMPLEX,
                         &d_status,
                         nullptr,
                         nullptr);
    Assert(res == 0);
    Assert(d_status == QS_LP_OPTIMAL || d_status == QS_LP_DELTA_OPTIMAL
           || d_status == QS_LP_FEASIBLE || d_status == QS_LP_DELTA_FEASIBLE);
    isStrictBasic = d_basis.cstat[numCols() - 1] == QS_COL_BSTAT_BASIC;
  }

  // By this point, either the strict variable is basic and at 0,
  // or it is non-basic and we don't care about its value
  Assert(!isStrictBasic || toMpqClass(d_x[numCols() - 1]) == 0);

  // TODO: for now, disable this. Maybe it could be work activating
  // if (d_status == QS_LP_INFEASIBLE)
  // {
  //   freeBasis();
  //   int res = mpq_QSdelete_col(d_qsx, numCols() - 1);
  //   Assert(res == 0);
  //   mpq_class delta = 0;
  //   res = QSdelta_solver(d_qsx,
  //                        delta.get_mpq_t(),
  //                        static_cast<mpq_t*>(d_x),
  //                        nullptr,
  //                        &d_basis,
  //                        nullptr,
  //                        PRIMAL_SIMPLEX,
  //                        &d_status,
  //                        nullptr,
  //                        nullptr);
  //   Assert(res == 0);
  //   Assert(d_status == QS_LP_INFEASIBLE);
  //   isStrictBasic = false;
  // }

  if (d_status == QS_LP_OPTIMAL || d_status == QS_LP_DELTA_OPTIMAL
      || d_status == QS_LP_FEASIBLE || d_status == QS_LP_DELTA_FEASIBLE
      || d_status == QS_LP_UNBOUNDED || d_status == QS_LP_INFEASIBLE)
  {
    for (int colIdx = 0; colIdx < static_cast<int>(d_colToArithVar.size());
         colIdx++)
    {
      extractVarValue<VariableType::COL>(colIdx, sol);
    }

    for (int rowIdx = 0; rowIdx < numRows(); rowIdx++)
    {
      const ArithVar v = d_rowToArithVar[rowIdx];
      // We already encountered the nonbasic version of this row, we can skip it
      if (sol.newNonBasis.isMember(v)) continue;
      extractVarValue<VariableType::ROW>(rowIdx, sol);
    }
  }
  else
  {
    // Infeasible solution.
    Unimplemented();
  }

  // Since we have to split range rows, we have to remove those that we
  // erroneously marked as basic and then discovered to be nonbasic
  for (const ArithVar v : sol.newNonBasis)
  {
    if (sol.newBasis.isMember(v)) sol.newBasis.remove(v);
  }
  // If the strict variable is basic, we need to add some other non-basic
  // variable to the basis to maintain the same number of basic variables
  if (isStrictBasic)
  {
    bool added = false;
    for (const ArithVar v : d_strictVars)
    {
      if (!sol.newBasis.isMember(v)
          && (d_vars.cmpToLowerBound(v, sol.newValues.get(v)) == 0
              || d_vars.cmpToUpperBound(v, sol.newValues.get(v)) == 0))
      {
        added = true;
        sol.newBasis.add(v);
        break;
      }
    }
    Assert(added);
  }

  return sol;
}

external::LinResult ExactQsoptex::solveRelaxation()
{
  Assert(!d_solvedRelaxation);

#ifndef NDEBUG
  mpq_QSwrite_prob(
      d_qsx,
      "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/qsfile.lp",
      "LP");
#endif

  // Should have room for the (rowcount) "logical" variables, which come after
  // the (colcount) "structural" variables.
  d_x.Resize(static_cast<size_t>(numCols()));
  unsigned int precision = 0;
  mpq_class delta = 0;
  const int res = QSdelta_solver(d_qsx,
                                 delta.get_mpq_t(),
                                 static_cast<mpq_t*>(d_x),
                                 nullptr,
                                 &d_basis,
                                 &precision,
                                 PRIMAL_SIMPLEX,
                                 &d_status,
                                 nullptr,
                                 nullptr);
  Assert(res == 0);

  d_stats.d_precision << precision;

  switch (d_status)
  {
    case QS_LP_OPTIMAL:
    case QS_LP_FEASIBLE:
    case QS_LP_DELTA_OPTIMAL:
    case QS_LP_DELTA_FEASIBLE:
      d_solvedRelaxation = true;
      // Check the value of the last column (strict variable)
      return isStrictVarZero() ? external::LinResult::LinInfeasible
                               : external::LinResult::LinFeasible;
    case QS_LP_INFEASIBLE:
      d_solvedRelaxation = true;
      return external::LinResult::LinInfeasible;
    case QS_LP_ITER_LIMIT:
    case QS_LP_TIME_LIMIT: return external::LinResult::LinExhausted;
    default: return external::LinResult::LinUnknown;
  }
}

ArithVar ExactQsoptex::getBranchVar(const NodeLog& con) const
{
  int br_var = con.branchVariable();
  return getArithVarFromStructural(br_var);
}

external::MipResult ExactQsoptex::solveMIP(bool al)
{
  return external::MipResult::MipUnknown;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex implementation. */
#endif /*#ifdef CVC5_USE_QSOPTEX */

/* Begin soplex/No soplpex Glue code. */
namespace cvc5::internal {
namespace theory {
namespace arith::linear {

external::ExternalSimplex* ExactSimplex::mkExactQsoptexSolver(
    CVC5_UNUSED const ArithVariables& vars,
    CVC5_UNUSED TreeLog& l,
    CVC5_UNUSED external::SimplexStatistics& s,
    CVC5_UNUSED const Options& o)
{
#ifdef CVC5_USE_QSOPTEX
  if (o.arith.lpStrictVar) return new ExactQsoptexStrict(vars, l, s);
  return new ExactQsoptexEpsilon(vars, l, s);
#else
  Unimplemented() << "Exact simplex solver requires SoPlex";
#endif
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex/No soplex Glue code. */
