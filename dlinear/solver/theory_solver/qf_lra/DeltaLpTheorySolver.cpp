//
// Created by c3054737 on 08/11/24.
//

#include "DeltaLpTheorySolver.h"

namespace dlinear {
void DeltaLpTheorySolver::AddVariable(const Variable& var) { LpTheorySolver::AddVariable(var); }
void DeltaLpTheorySolver::AddLiterals() { LpTheorySolver::AddLiterals(); }
void DeltaLpTheorySolver::Consolidate(const Box& box) { LpTheorySolver::Consolidate(box); }
void DeltaLpTheorySolver::Backtrack() { LpTheorySolver::Backtrack(); }
void DeltaLpTheorySolver::UpdateModelSolution() { LpTheorySolver::UpdateModelSolution(); }
void DeltaLpTheorySolver::EnableSpxVarBound() { LpTheorySolver::EnableSpxVarBound(); }
void DeltaLpTheorySolver::EnableSpxRow(int spx_row, bool truth) {}
}  // namespace dlinear