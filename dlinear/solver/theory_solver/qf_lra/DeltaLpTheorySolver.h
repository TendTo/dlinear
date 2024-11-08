#pragma once

#include "dlinear/solver/theory_solver/qf_lra/LpTheorySolver.h"
#include "third_party/com_github_robotlocomotion_drake/dlinear/symbolic/symbolic_variable.h"

namespace dlinear {

class DeltaLpTheorySolver : public LpTheorySolver {
 public:
  explicit DeltaLpTheorySolver(const PredicateAbstractor& predicate_abstractor,
                               const std::string& class_name = "DeltaLpTheorySolver");

  void AddVariable(const Variable& var) override;
  void AddLiterals() override;
  void Consolidate(const Box& box) override;
  void Backtrack() override;

 protected:
  void UpdateModelSolution() override;
  void EnableSpxVarBound() override;
  void EnableSpxRow(int spx_row, bool truth) override;
};

}  // namespace dlinear
