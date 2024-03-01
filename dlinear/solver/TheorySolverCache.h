#pragma once

#include <map>
#include <optional>

#include "dlinear/symbolic/literal.h"

namespace dlinear {

/**
 * TheorySolverCache class.
 *
 * It is used to cache the explanations obtained from the theory solver over a set of literals.
 * This is useful to avoid recomputing of the same LP problem over and over again when only some boolean variables
 * change.
 */
class TheorySolverCache {
 public:
  /**
   * Get the cached explanation for the given literals.
   *
   * If the explanation is not found, std::nullopt is returned.
   * @param literals set of literals to get the explanation for
   * @return literal set with the explanation if it is found (cache hit)
   * @return std::nullopt if the explanation is not found (cache miss)
   */
  [[nodiscard]] std::optional<const LiteralSet *const> GetTheoryExplanation(const std::vector<Literal> &literals) const;
  /**
   * Cache the explanation for the given literal set.
   *
   * @param literals set of literals to cache the explanation for
   * @param explanation explanation to cache
   */
  void CacheTheoryExplanation(const std::vector<Literal> &literals, const LiteralSet &explanation);

  /**
   * Clear the cache.
   */
  void Clear();

 private:
  std::map<LiteralSet, LiteralSet, LiteralSetComparator> cache_;  ///< Cache of the explanations
};

}  // namespace dlinear
