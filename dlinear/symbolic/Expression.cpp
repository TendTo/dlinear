#include "Expression.h"

#include "dlinear/util/exception.h"

namespace dlinear::symbolic {

Expression::Expression(ExpressionCell* c) : cell_{c} {
  DLINEAR_ASSERT(c != nullptr, "Expression cell must not be null");
}

}  // namespace dlinear::symbolic