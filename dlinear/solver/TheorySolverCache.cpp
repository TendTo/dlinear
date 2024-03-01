#include "TheorySolverCache.h"

#include "dlinear/util/logging.h"

namespace dlinear {

std::optional<const LiteralSet *const> TheorySolverCache::GetTheoryExplanation(
    const std::vector<Literal> &literals) const {
  auto it = cache_.find({literals.cbegin(), literals.cend()});
  if (it != cache_.end()) {
    DLINEAR_TRACE("TheorySolverCache::GetTheoryExplanation(): cache hit");
    return std::optional<const LiteralSet *const>{&it->second};
  }
  DLINEAR_TRACE("TheorySolverCache::GetTheoryExplanation(): cache miss");
  return {};
}

void TheorySolverCache::CacheTheoryExplanation(const std::vector<Literal> &literals, const LiteralSet &explanation) {
  DLINEAR_TRACE("TheorySolverCache::CacheTheoryExplanation(): caching explanation");
  cache_[{literals.cbegin(), literals.cend()}] = explanation;
}

void TheorySolverCache::Clear() {
  DLINEAR_TRACE("TheorySolverCache::Clear()");
  cache_.clear();
}

}  // namespace dlinear