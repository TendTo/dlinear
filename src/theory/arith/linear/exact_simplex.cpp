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

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

bool ExactSimplex::soplexEnabled()
{
#ifdef CVC5_USE_SOPLEX
  return true;
#else
  return false;
#endif
}

bool ExactSimplex::qsoptexEnabled()
{
#ifdef CVC5_USE_QSOPTEX
  return true;
#else
  return false;
#endif
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
/* End soplex/No soplex Glue code. */
