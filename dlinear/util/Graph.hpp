/**
 * @file Graph.hpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Graph class.
 *
 * Generic graph implementation that can be used to represent a graph with vertices of type @p T.
 */
#pragma once

#include <functional>
#include <iostream>
#include <queue>
#include <stack>
#include <unordered_map>
#include <unordered_set>

namespace dlinear {

/**
 * Graph class.
 *
 * Generic implementation that can be used to represent a graph with vertices of type @p T.
 * @tparam T element type of the vertices
 */
template <class T>
class Graph {
 public:
  /**
   * Add an edge to the graph from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @param bidirectional whether to add another edge from @p v to @p u
   */
  void AddEdge(const T& u, const T& v, bool bidirectional = true) {
    adj_list_[u].insert(v);
    if (bidirectional) adj_list_[v].insert(u);
  }

  /**
   * Add a vertex @p v to the graph.
   *
   * The edge set for the vertex is initialized to an empty set.
   * @param v vertex to add
   */
  void AddVertex(const T& v) {
    if (adj_list_.find(v) == adj_list_.end()) adj_list_[v] = std::unordered_set<T>();
  }

  /**
   * Check if the graph contains an edge from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @return true if the graph contains an edge from @p u to @p v
   * @return false if either @p u or @p v is not in the graph or if there is no edge from @p u to @p v
   */
  bool HasEdge(const T& u, const T& v) const {
    return adj_list_.find(u) != adj_list_.cend() && adj_list_.at(u).find(v) != adj_list_.at(u).cend();
  }

  /**
   * Return the adjacency list of the graph
   * @return a map from vertex to the set of vertices that are adjacent to it
   */
  const std::unordered_map<T, std::unordered_set<T>>& adj_list() const { return adj_list_; }

  /**
   * Remove an edge from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @param bidirectional whether to remove the edge from @p v to @p u too
   */
  void RemoveEdge(const T& u, const T& v, bool bidirectional = true) {
    adj_list_[u].erase(v);
    if (bidirectional) adj_list_[v].erase(u);
  }

  /**
   * Remove a vertex @p v from the graph
   * @param v vertex to remove
   */
  void RemoveVertex(const T& v) {
    adj_list_.erase(v);
    for (auto& [node, edges] : adj_list_) edges.erase(v);
  }

  /** Clear the graph, removing all vertices and edges. */
  void Clear() { adj_list_.clear(); }

  /**
   * Check if the graph is empty
   * @return true if the graph is empty
   * @return false if the graph is not empty
   */
  [[nodiscard]] bool IsEmpty() const { return adj_list_.empty(); }

  /**
   * Explore the graph using depth-first search starting from vertex @p start.
   *
   * Each vertex is visited exactly once and the function @p func is called on each one.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it
   */
  void DFS(const T& start, const std::function<void(const T&)>& func) {
    std::unordered_set<T> visited{};
    visited.reserve(adj_list_.size());
    std::stack<T> stack;

    stack.push(start);
    visited.insert(start);
    while (!stack.empty()) {
      T current = stack.top();
      stack.pop();
      func(current);
      for (const T& adjVertex : adj_list_[current]) {
        if (visited.find(adjVertex) == visited.end()) {
          stack.push(adjVertex);
          visited.insert(adjVertex);
        }
      }
    }
  }

  /**
   * Explore the graph using breadth-first search starting from vertex @p start.
   *
   * Each vertex is visited exactly once and the function @p func is called on each one.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it
   */
  void BFS(const T& start, const std::function<void(const T&)>& func) {
    std::unordered_set<T> visited{};
    visited.reserve(adj_list_.size());
    std::queue<T> queue;
    visited.insert(start);
    queue.push(start);
    while (!queue.empty()) {
      func(queue.front());
      for (auto& neighbour : adj_list_[queue.front()]) {
        if (visited.find(neighbour) != visited.end()) continue;
        visited.insert(neighbour);
        queue.push(neighbour);
      }
      queue.pop();
    }
  }

 private:
  std::unordered_map<T, std::unordered_set<T>> adj_list_;  ///< Adjacency list of the graph
};

template <typename T>
std::ostream& operator<<(std::ostream& os, const Graph<T>& s) {
  os << "Graph{";
  for (auto& [node, edges] : s.adj_list()) {
    std::cout << node << " -> ";
    for (auto& edge : edges) std::cout << edge << ", ";
  }
  return os << "}";
}

}  // namespace dlinear
