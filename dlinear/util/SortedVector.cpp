#include "SortedVector.hpp"

#include "dlinear/solver/Bound.h"

namespace dlinear {

template class SortedVector<Bound>;
template class SortedVector<int>;
template class SortedVector<double>;

}  // namespace dlinear
