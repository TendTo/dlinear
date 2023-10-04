/**
 * @file hash.hpp
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright drake robotlocomotion
 * @brief Utilities for filesystem operations.
 *
 * Taken from drake's implementation
 * https://github.com/RobotLocomotion/drake/tree/master
 */
#pragma once

#include <cstddef>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

namespace dlinear {

/**
 * Combines a given starting hash @p seed and generic input @p v into a new
 * hash. The following code is public domain according to
 * http://www.burtleburtle.net/bob/hash/doobs.html.
 * @param seed The starting hash.
 * @param v The input value.
 * @return The combined hash.
 */
template <class T>
size_t hash_combine(size_t seed, const T &v);

template <class T, class... Rest>
size_t hash_combine(size_t seed, const T &v, Rest... rest) {
  return hash_combine(hash_combine(seed, v), rest...);
}

/** Computes the combined hash value of the elements of an iterator range. */
template <typename It>
size_t hash_range(It first, It last) {
  size_t seed{};
  for (; first != last; ++first) {
    seed = hash_combine(seed, *first);
  }
  return seed;
}

/** Computes the hash value of @p v using std::hash. */
template <class T>
inline size_t hash(const T &v) {
  return std::hash<T>{}(v);
}

/** Computes the hash value of a pair @p p. */
template <class T1, class T2>
inline size_t hash(const std::pair<T1, T2> &p) {
  return hash_combine(0, p.first, p.second);
}

/** Computes the hash value of a vector @p vec. */
template <class T>
inline size_t hash(const std::vector<T> &vec) {
  return hash_range(vec.begin(), vec.end());
}

/** Computes the hash value of a set @p s. */
template <class T>
inline size_t hash(const std::set<T> &s) {
  return hash_range(s.begin(), s.end());
}

/** Computes the hash value of a map @p map. */
template <class T1, class T2>
inline size_t hash(const std::map<T1, T2> &map) {
  return hash_range(map.begin(), map.end());
}

/**
 * Combines a given starting hash @p seed and generic input @p v into a new
 * hash. The following code is public domain according to
 * http://www.burtleburtle.net/bob/hash/doobs.html.
 * @param seed The starting hash.
 * @param v The input value.
 * @return The combined hash.
 */
template <class T>
inline size_t hash_combine(size_t seed, const T &v) {
  return seed ^ (hash(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2));
}

}  // namespace dlinear
