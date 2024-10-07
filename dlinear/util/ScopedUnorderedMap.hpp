/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Backtrackable scoped unordered_map.
 *
 * This is a unordered_map that supports backtracking. It is used to store
 * intermediate results.
 */
#pragma once

#include <functional>
#include <iostream>
#include <memory>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace dlinear {

template <class Key, class T, class Hash = std::hash<Key>, class KeyEqual = std::equal_to<Key>,
          class Allocator = std::allocator<std::pair<const Key, T>>>

class ScopedUnorderedMap {
 public:
  // Aliases.
  using UnorderedMapType = std::unordered_map<Key, T, Hash, KeyEqual, Allocator>;
  using value_type = typename UnorderedMapType::value_type;
  using size_type = typename UnorderedMapType::size_type;
  using const_iterator = typename UnorderedMapType::const_iterator;

  /**
   * Action to perform on the scoped unordered map.
   */
  enum class ActionKind {
    INSERT,  ///< Insert(k, v) means that (k, v) is inserted.
    UPDATE,  ///< Update(k, v) means that (k, v) was replaced by a new value.
  };
  using Action = std::tuple<ActionKind, Key, T>;

  ScopedUnorderedMap() = default;
  ScopedUnorderedMap(const ScopedUnorderedMap &) = default;
  ScopedUnorderedMap(ScopedUnorderedMap &&) noexcept = default;
  ScopedUnorderedMap &operator=(const ScopedUnorderedMap &) = default;
  ScopedUnorderedMap &operator=(ScopedUnorderedMap &&) noexcept = default;
  ~ScopedUnorderedMap() = default;

  // Iterators.
  //
  // @note We only provide 'const' iterators because any modification
  // should be done explicitly via its APIs so that we can keep track
  // of changes and undo when pop() is called.
  const_iterator begin() const { return map_.begin(); }
  const_iterator cbegin() const { return map_.cbegin(); }
  const_iterator end() const { return map_.end(); }
  const_iterator cend() const { return map_.cend(); }

  [[nodiscard]] bool empty() const { return map_.empty(); }
  size_type size() const { return map_.size(); }

  /** Clear the map. */
  void clear() {
    map_.clear();
    actions_.clear();
    stack_.clear();
  }

  /**
   * Insert a new key-value pair.
   * @param k key
   * @param v value
   */
  void insert(const Key &k, const T &v) {
    auto it = map_.find(k);
    if (it == map_.end()) {
      // Case 1) k does not exist.
      actions_.emplace_back(ActionKind::INSERT, k, v);
      map_.emplace(k, v);
    } else {
      // Case 2) k exists. Save the old value so that we can roll
      // back later.
      actions_.emplace_back(ActionKind::UPDATE, k, it->second);
      it->second = v;  // Perform Update.
    }
  }

  /**
   * Lookup the value for the given key.
   * @param key key to use for the lookup
   * @throw runtime_error if the key does not exist
   * @return element with the given key, if it exists
   */
  const T &operator[](const Key &key) const {
    const auto it = map_.find(key);
    if (it == map_.end()) {
      throw std::runtime_error("ScopedUnorderedMap has no entry for the key {}" + std::to_string(key));
    }
    return it->second;
  }

  /**
   * Lookup the value for the given key.
   * @param key key to use for the lookup
   * @throw runtime_error if the key does not exist
   * @return element with the given key, if it exists
   */
  const T &at(const Key &key) const { return map_.at(key); }

  size_type count(const Key &key) const { return map_.count(key); }
  // @note It returns 'const' iterator.
  const_iterator find(const Key &key) const { return map_.find(key); }

  // Push/Pop
  void push() { stack_.push_back(actions_.size()); }
  void pop() {
    if (stack_.empty()) {
      throw std::runtime_error("ScopedUnorderedMap cannot be popped because it's scope is empty.");
    }
    size_type idx = stack_.back();
    while (idx < actions_.size()) {
      const Action &item{actions_.back()};
      const ActionKind kind{std::get<0>(item)};
      const Key &k{std::get<1>(item)};
      const T &v{std::get<2>(item)};
      auto it = map_.find(k);
      switch (kind) {
        case ActionKind::INSERT:
          // Remove (k, v).
          map_.erase(it);
          break;
        case ActionKind::UPDATE:
          // Roll back to map_[k] = v.
          it->second = v;
          break;
      }
      actions_.pop_back();
    }
    stack_.pop_back();
  }

 private:
  std::vector<Action> actions_;  ///< Vector of actions that have been applied.
  std::vector<size_type> stack_;
  UnorderedMapType map_;  ///< Actual map.
};

}  // namespace dlinear
