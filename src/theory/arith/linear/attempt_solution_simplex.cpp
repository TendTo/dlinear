/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Gereon Kremer
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
#include "theory/arith/linear/attempt_solution_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/error_set.h"
#include "theory/arith/linear/linear_equality.h"
#include "theory/arith/linear/tableau.h"
#include "util/statistics_registry.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

void debugSol(const ArithVariables& vars, const external::Solution& sol){
  const auto& newValues = sol.newValues;
  for (auto i = newValues.begin(), i_end = newValues.end(); i != i_end; ++i){
    ArithVar v = *i;
    cout << "Variable " << v << " (" << (sol.newBasis.isMember(v) ? "B" : "NB") <<  ") => ";
    if (vars.isAuxiliary(v))
      vars.printModel(v);
    else
      cout << vars.asNode(v).getName();
    cout << " should be " << newValues[v] << endl;
  }
}

void debugNonBasic(const ArithVariables& vars, const external::Solution& sol, const Tableau& tableau){
  const auto& newValues = sol.newValues;
  for (auto i = newValues.begin(), i_end = newValues.end(); i != i_end; ++i){
    ArithVar v = *i;
    if (tableau.isBasic(v)) continue;
    cout << "Variable " << v << " (NB) => ";
    if (vars.isAuxiliary(v))
      vars.printModel(v);
    else
      cout << vars.asNode(v).getName();
    cout << "\n\t" << (vars.hasLowerBound(v) ? vars.getLowerBound(v).toString() : "-inf") << " <= " << newValues[v].toString() << " <= "
         << (vars.hasUpperBound(v) ? vars.getUpperBound(v).toString() : "+inf") << endl;
  }
}

AttemptSolutionSDP::AttemptSolutionSDP(Env& env,
                                       LinearEqualityModule& linEq,
                                       ErrorSet& errors,
                                       RaiseConflict conflictChannel,
                                       TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_statistics(statisticsRegistry())
{ }

AttemptSolutionSDP::Statistics::Statistics(StatisticsRegistry& sr)
    : d_searchTime(sr.registerTimer("theory::arith::attempt::searchTime")),
      d_queueTime(sr.registerTimer("theory::arith::attempt::queueTime")),
      d_conflicts(sr.registerInt("theory::arith::attempt::conflicts")),
      d_extendedSearch(sr.registerInt("theory::arith::attempt::extendedSearch"))
{
}

bool AttemptSolutionSDP::matchesNewValue(const DenseMap<DeltaRational>& nv, ArithVar v) const{
  return nv[v] == d_variables.getAssignment(v);
}

Result::Status AttemptSolutionSDP::attempt(const external::Solution& sol)
{
  TimerStat::CodeTimer timer{d_statistics.d_searchTime};

  if (options().arith.externalLPSolver == options::ExternalLPSolver::SOPLEX
    && sol.linResult == external::LinResult::LinInfeasible)
  {
    return attemptPivotFirst(sol);
  }
  return attemptOptimistic(sol);
}

Result::Status AttemptSolutionSDP::attemptOptimistic(
    const external::Solution& sol)
{
    const DenseSet& newBasis = sol.newBasis;
    const DenseMap<DeltaRational>& newValues = sol.newValues;

#if 0 // For debug
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(d_tableau.isBasic(b)){
      std::cout << "Variable " << b << " => ";
      if (d_variables.isAuxiliary(b))
        std::cout << d_variables.asNode(b).getName();
      else
        d_variables.printModel(b, std::cout);
      std::cout << " is basic" << std::endl;
    }
  }
#endif

  DenseSet needsToBeAdded;
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(!d_tableau.isBasic(b)){
      needsToBeAdded.add(b);
    }
  }
  DenseMap<DeltaRational>::const_iterator nvi = newValues.begin(), nvi_end = newValues.end();
  for(; nvi != nvi_end; ++nvi){
    ArithVar currentlyNb = *nvi;
    if(!d_tableau.isBasic(currentlyNb)){
      if(!matchesNewValue(newValues, currentlyNb)){
        const DeltaRational& newValue = newValues[currentlyNb];
        Trace("arith::updateMany")
          << "updateMany:" << currentlyNb << " "
          << d_variables.getAssignment(currentlyNb) << " to "<< newValue << endl;
        d_linEq.update(currentlyNb, newValue);
        Assert(d_variables.assignmentIsConsistent(currentlyNb));
      }
    }
  }
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if(processSignals()){
    Trace("arith::findModel") << "attemptSolution() early conflict" << endl;
    d_conflictVariables.purge();
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Trace("arith::findModel") << "attemptSolution() fixed itself" << endl;
    return Result::SAT;
  }

  // The simple assignment was not enough, extended search is needed
  ++d_statistics.d_extendedSearch;

  while(!needsToBeAdded.empty() && !d_errorSet.errorEmpty()){
    ArithVar toRemove = ARITHVAR_SENTINEL;
    ArithVar toAdd = ARITHVAR_SENTINEL;
    DenseSet::const_iterator i = needsToBeAdded.begin(), i_end = needsToBeAdded.end();
    for(; toAdd == ARITHVAR_SENTINEL && i != i_end; ++i){
      ArithVar v = *i;

      Tableau::ColIterator colIter = d_tableau.colIterator(v);
      for(; !colIter.atEnd(); ++colIter){
        const Tableau::Entry& entry = *colIter;
        Assert(entry.getColVar() == v);
        ArithVar b = d_tableau.rowIndexToBasic(entry.getRowIndex());
        if(!newBasis.isMember(b)){
          toAdd = v;

          bool favorBOverToRemove =
            (toRemove == ARITHVAR_SENTINEL) ||
            (matchesNewValue(newValues, toRemove) && !matchesNewValue(newValues, b)) ||
            (d_tableau.basicRowLength(toRemove) > d_tableau.basicRowLength(b));

          if(favorBOverToRemove){
            toRemove = b;
          }
        }
      }
    }
    Assert(toRemove != ARITHVAR_SENTINEL);
    Assert(toAdd != ARITHVAR_SENTINEL);

    Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;

    d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);

    Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" << endl;
    needsToBeAdded.remove(toAdd);

    bool conflict = processSignals();
    if(conflict){
      d_errorSet.reduceToSignals();
      d_conflictVariables.purge();

      return Result::UNSAT;
    }
  }
  Assert(d_conflictVariables.empty());

  if(d_errorSet.errorEmpty()){
    return Result::SAT;
  }else{
    d_errorSet.reduceToSignals();
    return Result::UNKNOWN;
  }
}

Result::Status AttemptSolutionSDP::attemptPivotFirst(
    const external::Solution& sol)
{
  const DenseSet& newBasis = sol.newBasis;
  const DenseSet& newNonBasis = sol.newNonBasis;
  const DenseMap<DeltaRational>& newValues = sol.newValues;

  DenseMap<DeltaRational>::const_iterator nvi = newValues.begin(), nvi_end = newValues.end();
  for(; nvi != nvi_end; ++nvi){
    ArithVar currentlyNb = *nvi;
    if(!d_tableau.isBasic(currentlyNb) && newNonBasis.isMember(currentlyNb) && !matchesNewValue(newValues, currentlyNb)){
      const DeltaRational& newValue = newValues[currentlyNb];
      Trace("arith::updateMany")
        << "updateMany:" << currentlyNb << " "
        << d_variables.getAssignment(currentlyNb) << " to "<< newValue << endl;
      d_linEq.update(currentlyNb, newValue);
      Assert(d_variables.assignmentIsConsistent(currentlyNb));
      Assert(
      !d_variables.hasEitherBound(currentlyNb) ||
      (d_variables.atBoundCounts(currentlyNb).upperBoundCount() > 0
        || d_variables.atBoundCounts(currentlyNb).lowerBoundCount() > 0));
    }
  }
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if(processSignals()){
    Trace("arith::findModel") << "attemptSolution() early conflict" << endl;
    d_conflictVariables.purge();
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Trace("arith::findModel") << "attemptSolution() fixed itself" << endl;
    return Result::SAT;
  }

  // The simple assignment was not enough, extended search is needed
  ++d_statistics.d_extendedSearch;

  DenseSet needsToBeAdded;
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(!d_tableau.isBasic(b)){
      needsToBeAdded.add(b);
    }
  }
  while(!needsToBeAdded.empty() && !d_errorSet.errorEmpty()){
    ArithVar toRemove = ARITHVAR_SENTINEL;
    ArithVar toAdd = ARITHVAR_SENTINEL;
    DenseSet::const_iterator i = needsToBeAdded.begin(), i_end = needsToBeAdded.end();
    for(; toAdd == ARITHVAR_SENTINEL && i != i_end; ++i){
      ArithVar v = *i;

      Tableau::ColIterator colIter = d_tableau.colIterator(v);
      for(; !colIter.atEnd(); ++colIter){
        const Tableau::Entry& entry = *colIter;
        Assert(entry.getColVar() == v);
        ArithVar b = d_tableau.rowIndexToBasic(entry.getRowIndex());
        if(!newBasis.isMember(b)){
          toAdd = v;

          bool favorBOverToRemove =
            (toRemove == ARITHVAR_SENTINEL) ||
            (newValues.isKey(b) && !newValues.isKey(toRemove)) ||
            (d_tableau.basicRowLength(toRemove) > d_tableau.basicRowLength(b));

          if(favorBOverToRemove){
            toRemove = b;
          }
        }
      }
    }
    Assert(toRemove != ARITHVAR_SENTINEL);
    Assert(toAdd != ARITHVAR_SENTINEL);

    Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;

    if (newValues.isKey(toRemove))
    {
      d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);
    } else
    {
      d_linEq.pivotAndUpdate(toRemove,
                       toAdd,
                       d_variables.hasLowerBound(toRemove)
                           ? d_variables.getLowerBound(toRemove)
                       : d_variables.hasUpperBound(toRemove)
                           ? d_variables.getUpperBound(toRemove)
                           : d_variables.getAssignment(toRemove));
    }

    Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" << endl;
    needsToBeAdded.remove(toAdd);

    if(processSignals()){
      d_errorSet.reduceToSignals();
      d_conflictVariables.purge();

      return Result::UNSAT;
    }
  }
  Assert(d_conflictVariables.empty());

  DenseSet needsToBeRemoved;
  for(DenseSet::const_iterator i = newNonBasis.begin(), i_end = newNonBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(d_tableau.isBasic(b)){
      needsToBeRemoved.add(b);
    }
  }
  auto it = d_variables.var_begin(), vi_end = d_variables.var_end();
  for (auto i = needsToBeRemoved.begin(), i_end = needsToBeRemoved.end(); i != i_end; ++i){
    ArithVar toRemove = *i;
    for (; it != vi_end; ++it){
      ArithVar toAdd = *it;
      if (toAdd == toRemove) continue;
      if (d_tableau.isBasic(toAdd)) continue;
      if (needsToBeRemoved.isMember(toAdd)) continue;
      const DeltaRational& newValue = newValues[toAdd];
      Trace("arith::updateMany")
        << "updateMany:" << toAdd << " "
        << d_variables.getAssignment(toAdd) << " to "<< newValue << endl;
      Assert(toAdd != ARITHVAR_SENTINEL);
      Assert(toRemove != ARITHVAR_SENTINEL);
      Trace("arith::forceNewBasis") << toAdd << " " << toRemove << endl;


      d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);
      Assert(
        !d_variables.hasEitherBound(toRemove) ||
        (d_variables.atBoundCounts(toRemove).upperBoundCount() > 0
          || d_variables.atBoundCounts(toRemove).lowerBoundCount() > 0));

      if(processSignals()){
        d_errorSet.reduceToSignals();
        d_conflictVariables.purge();

        return Result::UNSAT;
      }

      break;
    }
  }

  Assert(d_conflictVariables.empty());

  if(d_errorSet.errorEmpty()){
    return Result::SAT;
  }else{
    d_errorSet.reduceToSignals();
    return Result::UNKNOWN;
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
