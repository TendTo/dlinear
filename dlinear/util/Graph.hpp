#include <functional>
#include <iostream>
#include <queue>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace dlinear {

template <class T>
class Graph {
 public:
  // Constructor not needed if you don't have any initializations different from the default ones

  void AddEdge(const T& u, const T& v, bool bidir = true) {
    adj_list_[u].insert(v);
    if (bidir) adj_list_[v].insert(u);
  }

  void AddVertex(const T& v) {
    if (adj_list_.find(v) == adj_list_.end()) adj_list_[v] = std::unordered_set<T>();
  }

  bool HasEdge(const T& u, const T& v) const {
    return adj_list_.find(u) != adj_list_.cend() && adj_list_.at(u).find(v) != adj_list_.at(u).cend();
  }

  const std::unordered_map<T, std::unordered_set<T>>& adj_list() const { return adj_list_; }

  void RemoveEdge(const T& u, const T& v, bool bidir = true) {
    adj_list_[u].erase(v);
    if (bidir) adj_list_[v].erase(u);
  }

  void RemoveVertex(const T& v) {
    adj_list_.erase(v);
    for (auto& [node, edges] : adj_list_) edges.erase(v);
  }

  [[nodiscard]] bool IsEmpty() const { return adj_list_.empty(); }

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
  std::unordered_map<T, std::unordered_set<T>> adj_list_;
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
