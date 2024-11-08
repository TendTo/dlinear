/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "QfLraTheorySolver.h"

namespace dlinear {

QfLraTheorySolver::QfLraTheorySolver(const PredicateAbstractor& predicate_abstractor, const std::string& class_name)
    : TheorySolver{predicate_abstractor, class_name} {}

}  // namespace dlinear