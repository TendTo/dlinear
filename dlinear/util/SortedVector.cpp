/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SortedVector.hpp"

#include "dlinear/solver/Bound.h"

namespace dlinear {

template class SortedVector<Bound>;
template class SortedVector<int>;
template class SortedVector<double>;

}  // namespace dlinear
