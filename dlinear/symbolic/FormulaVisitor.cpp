/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "FormulaVisitor.h"

#include "dlinear/util/exception.h"

namespace dlinear {

Formula FormulaVisitor::Visit(const Formula &f) {
  switch (f.get_kind()) {
    case FormulaKind::False:
      return VisitFalse(f);
    case FormulaKind::True:
      return VisitTrue(f);
    case FormulaKind::Var:
      return VisitVariable(f);
    case FormulaKind::Eq:
      return VisitEqualTo(f);
    case FormulaKind::Neq:
      return VisitNotEqualTo(f);
    case FormulaKind::Gt:
      return VisitGreaterThan(f);
    case FormulaKind::Geq:
      return VisitGreaterThanOrEqualTo(f);
    case FormulaKind::Lt:
      return VisitLessThan(f);
    case FormulaKind::Leq:
      return VisitLessThanOrEqualTo(f);
    case FormulaKind::And:
      return VisitConjunction(f);
    case FormulaKind::Or:
      return VisitDisjunction(f);
    case FormulaKind::Not:
      return VisitNegation(f);
    case FormulaKind::Forall:
      return VisitForall(f);
  }
  DLINEAR_UNREACHABLE();
}

}  // namespace dlinear
