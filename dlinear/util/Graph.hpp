/**
 * @file Graph.hpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Graph class.
 *
 * Generic graph implementation that can be used to represent a graph with vertices of type @p T.
 */
#include <functional>
#include <numeric>
#include <queue>
#include <stack>
#include <unordered_map>
#include <unordered_set>

namespace dlinear {

/**
 * Result returned by the visit function.
 *
 * Depending on the result, the search algorithm will continue, skip adding the adjacent vertices to the stack/queue,
 * or stop the search altogether.
 * @see DFS
 * @see BFS
 */
enum class VisitResult {
  CONTINUE,  ///< Continue the search as usual and add the adjacent vertices to the stack/queue
  SKIP,      ///< Skip adding the adjacent vertices to the stack/queue, but continue the search
  STOP,      ///< Stop the search altogether
};

template <class T, class W>
struct _EdgeHash {
  size_t operator()(const std::pair<T, W>& lhs) const { return std::hash<T>{}(lhs.first); }
};

template <class T, class W>
struct _EdgeEqual {
  bool operator()(const std::pair<T, W>& lhs, const std::pair<T, W>& rhs) const { return lhs.first == rhs.first; }
};

/**
 * Graph class.
 *
 * Generic implementation that can be used to represent a graph with vertices of type @p T.
 * @tparam T element type of the vertices.
 * @tparam W element type of the edge weights.
 * @tparam EdgeHash hash function for the edges.
 * @tparam EdgeEqual equality function for the edges.
 * It implements basic graph operations such as adding and removing vertices and edges, as well as graph traversal
 * algorithms such as depth-first search @ref Graph::DFS and breadth-first search @ref Graph::BFS.
 */

// using T = int;
// using W = double;
// using EdgeHash = _EdgeHash<T, W>;
// using EdgeEqual = _EdgeEqual<T, W>;
template <class T, class W, class EdgeHash = _EdgeHash<T, W>, class EdgeEqual = _EdgeEqual<T, W>>
class Graph {
 public:
  using Edge = std::pair<T, W>;
  using AdjSet = std::unordered_set<Edge, EdgeHash, EdgeEqual>;
  /**
   * Add an edge to the graph from vertex @p u to vertex @p v.
   *
   * If the edge already exists no operation is performed.
   * @param u from vertex
   * @param v to vertex
   * @param bidirectional whether to add another edge from @p v to @p u
   */
  void AddEdge(const T& u, const T& v, bool bidirectional = true) {
    adj_list_[u].emplace(v, 1);
    if (bidirectional) adj_list_[v].emplace(u, 1);
  }

  /**
   * Add an edge to the graph from vertex @p u to vertex @p v.
   *
   * If the edge already exists, the weight is updated.
   * @param u from vertex
   * @param v to vertex
   * @param weight weight of the edge
   * @param bidirectional whether to add another edge from @p v to @p u
   */
  void AddEdge(const T& u, const T& v, W weight, bool bidirectional = true) {
    const auto [it, inserted] = adj_list_[u].emplace(v, weight);
    if (it->second != weight) {
      adj_list_.at(u).erase(it);
      adj_list_.at(u).emplace(v, weight);
    }
    if (bidirectional) {
      const auto [b_it, b_inserted] = adj_list_[v].emplace(u, 1 / weight);
      if (b_it->second != 1 / weight) {
        adj_list_.at(v).erase(b_it);
        adj_list_.at(v).emplace(u, 1 / weight);
      }
    }
  }

  /**
   * Add a vertex @p v to the graph.
   *
   * The edge set for the vertex is initialized to an empty set.
   * @param v vertex to add
   */
  void AddVertex(const T& v) {
    if (adj_list_.find(v) == adj_list_.end()) adj_list_.emplace(v, AdjSet{});
  }

  /**
   * Check if the graph contains an edge from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @return true if the graph contains an edge from @p u to @p v
   * @return false if either @p u or @p v is not in the graph or if there is no edge from @p u to @p v
   */
  bool HasEdge(const T& u, const T& v) const {
    return adj_list_.find(u) != adj_list_.cend() && adj_list_.at(u).find({v, 0}) != adj_list_.at(u).cend();
  }

  /**
   * Get a pointer to the weight of the edge from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @return pointer to the weight of the edge from @p u to @p v
   * @return nullptr if either @p u or @p v is not in the graph or if there is no edge from @p u to @p v
   */
  const W* GetEdgeWeight(const T& u, const T& v) const {
    if (auto it = adj_list_.find(u); it != adj_list_.cend()) {
      if (auto it2 = adj_list_.at(u).find({v, 0}); it2 != adj_list_.at(u).cend()) {
        return &it2->second;
      }
    }
    return nullptr;
  }

  /**
   * Return the adjacency list of the graph
   * @return a map from vertex to the set of vertices that are adjacent to it
   */
  const std::unordered_map<T, AdjSet>& adj_list() const { return adj_list_; }

  /**
   * Remove an edge from vertex @p u to vertex @p v
   * @param u from vertex
   * @param v to vertex
   * @param bidirectional whether to remove the edge from @p v to @p u too
   */
  void RemoveEdge(const T& u, const T& v, bool bidirectional = true) {
    adj_list_[u].erase({v, 0});
    if (bidirectional) adj_list_[v].erase({u, 0});
  }

  /**
   * Remove a vertex @p v from the graph
   * @param v vertex to remove
   */
  void RemoveVertex(const T& v) {
    adj_list_.erase(v);
    for (auto& [node, edges] : adj_list_) edges.erase({v, 0});
  }

  /** Clear the graph, removing all vertices and edges. */
  void Clear() { adj_list_.clear(); }

  /**
   * Return the number of vertices in the graph
   * @return number of vertices
   */
  [[nodiscard]] size_t Size() const {
    return std::accumulate(adj_list_.begin(), adj_list_.end(), 0,
                           [](size_t acc, const auto& pair) { return acc + pair.second.size(); });
  }

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
   * The return value of @p func will determine whether the search continues, skips adding the adjacent
   * vertices to the stack, or stops altogether.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it
   * @see VisitResult
   */
  void DFS(const T& start, const std::function<VisitResult(const T&)>& func) {
    std::unordered_set<T> visited{};
    DFS(start, func, visited);
  }
  /**
   * Explore the graph using depth-first search starting from vertex @p start.
   *
   * Each vertex is visited exactly once and the function @p func is called on each one.
   * The function exposes the @p visited set, which can be used to keep track of visited vertices or to
   * change the behavior of the search.
   * The return value of @p func will determine whether the search continues, skips adding the adjacent
   * vertices to the stack, or stops altogether.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it. If the function returns false, the search stops.
   * @param visited set of visited vertices
   * @see VisitResult
   */
  void DFS(const T& start, const std::function<VisitResult(const T&)>& func, std::unordered_set<T>& visited) {
    visited.clear();
    visited.reserve(adj_list_.size());
    std::stack<T> stack;

    stack.push(start);
    while (!stack.empty()) {
      const T current = std::move(stack.top());
      stack.pop();
      if (visited.find(current) != visited.end()) continue;
      visited.insert(current);
      const VisitResult res = func(current);
      if (res == VisitResult::STOP) return;
      if (res == VisitResult::SKIP) continue;
      for (const auto& [adj_vertex, weight] : adj_list_[current]) {
        if (visited.find(adj_vertex) == visited.end()) stack.push(adj_vertex);
      }
    }
  }

  /**
   * Explore the graph using breadth-first search starting from vertex @p start.
   *
   * Each vertex is visited exactly once and the function @p func is called on each one.
   * The return value of @p func will determine whether the search continues, skips adding the adjacent
   * vertices to the stack, or stops altogether.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it
   * @see VisitResult
   */
  void BFS(const T& start, const std::function<VisitResult(const T&)>& func) {
    std::unordered_set<T> visited{};
    BFS(start, func, visited);
  }
  /**
   * Explore the graph using breadth-first search starting from vertex @p start.
   *
   * Each vertex is visited exactly once and the function @p func is called on each one.
   * The function exposes the @p visited set, which can be used to keep track of visited vertices or to
   * change the behavior of the search.
   * The return value of @p func will determine whether the search continues, skips adding the adjacent
   * vertices to the stack, or stops altogether.
   * @param start starting vertex
   * @param func function to call on each vertex upon visiting it
   * @param visited set of visited vertices
   * @see VisitResult
   */
  void BFS(const T& start, const std::function<VisitResult(const T&)>& func, std::unordered_set<T>& visited) {
    visited.reserve(adj_list_.size());
    std::queue<T> queue;
    visited.insert(start);
    queue.push(start);
    while (!queue.empty()) {
      const VisitResult res = func(queue.front());
      if (res == VisitResult::STOP) return;
      if (res == VisitResult::SKIP) {
        queue.pop();
        continue;
      }
      for (auto& [adj_vertex, weight] : adj_list_[queue.front()]) {
        if (visited.find(adj_vertex) != visited.end()) continue;
        visited.insert(adj_vertex);
        queue.push(adj_vertex);
      }
      queue.pop();
    }
  }

  /**
   * Find all paths from vertex @p start to vertex @p end.
   *
   * Each path will be encountered exactly once and the function @p func is called on each one.
   * Some path may contain the same vertexes but in different order.
   * The return value of @p func will determine whether the search continues or should stop after the first path is
   * found.
   * @warning The path is passed to the function by reference.
   * It should not be modified unless that is the intended behavior.
   * @param start starting vertex
   * @param end ending vertex
   * @param func function to call on each path
   * @see VisitResult
   */
  void AllPaths(const T& start, const T& end, const std::function<VisitResult(std::vector<T>&)>& func) {
    std::unordered_set<T> visited;
    AllPaths(start, end, func, visited);
  }
  /**
   * Find all paths from vertex @p start to vertex @p end.
   *
   * Each path will be encountered exactly once and the function @p func is called on each one.
   * Some path may contain the same vertexes but in different order.
   * The function exposes the @p visited set, which can be used to keep track of visited vertices or to
   * change the behavior of the search.
   * The return value of @p func will determine whether the search continues or should stop after the first path is
   * found.
   * @warning The path is passed to the function by reference.
   * It should not be modified unless that is the intended behavior.
   * @param start starting vertex
   * @param end ending vertex
   * @param func function to call on each path
   * @param visited set of visited vertices
   * @see VisitResult
   */
  void AllPaths(const T& start, const T& end, const std::function<VisitResult(std::vector<T>&)>& func,
                std::unordered_set<T>& visited) {
    std::stack<T> stack;
    std::unordered_map<T, typename std::unordered_set<Edge>::iterator> iterators;
    std::vector<T> path;

    iterators.reserve(adj_list_.size());
    visited.reserve(adj_list_.size());
    path.reserve(adj_list_.size());

    stack.push(start);
    visited.insert(start);
    path.push_back(start);
    iterators[start] = adj_list_[start].begin();

    while (!stack.empty()) {
      const T current = stack.top();

      if (current == end) {
        if (func(path) != VisitResult::CONTINUE) return;
        stack.pop();
        visited.erase(current);
        path.pop_back();
        continue;
      }

      auto& it = iterators.at(current);
      if (it == adj_list_.at(current).end()) {
        stack.pop();
        visited.erase(current);
        path.pop_back();
        continue;
      }

      const T next = it->first;
      ++it;
      if (visited.find(next) == visited.end()) {
        stack.push(next);
        visited.insert(next);
        path.push_back(next);
        iterators.insert_or_assign(next, adj_list_.at(next).begin());
      }
    }
  }

 private:
  std::unordered_map<T, AdjSet> adj_list_;  ///< Adjacency list of the graph
};

template <class T, class E>
std::ostream& operator<<(std::ostream& os, const Graph<T, E>& s) {
  os << "Graph{";
  for (const auto& [vertex, edges] : s.adj_list()) {
    os << vertex << " -> ";
    for (const auto& [adj_vertex, weight] : edges) os << adj_vertex << "(" << weight << "), ";
  }
  return os << "}";
}

}  // namespace dlinear
