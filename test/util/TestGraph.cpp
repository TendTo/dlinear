/**
 * @file TestGraph.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "dlinear/util/Graph.hpp"

using dlinear::Graph;

template <class T>
class TestGraph : public ::testing::Test {
 protected:
  /*
   * 0 - 1 - 2
   * | \   \
   * 4 - 3 - 5
   * |
   * 6 -> 7 - 8
   */
  Graph<T> graph_;
  Graph<T> empty_graph_;

  TestGraph() {
    graph_.AddEdge(0, 1);
    graph_.AddEdge(0, 3);
    graph_.AddEdge(0, 4);
    graph_.AddEdge(1, 2);
    graph_.AddEdge(1, 5);
    graph_.AddEdge(4, 3);
    graph_.AddEdge(3, 5);
    graph_.AddEdge(4, 6);
    graph_.AddEdge(6, 7, false);
    graph_.AddEdge(7, 8);
  }
};

using TestParams = ::testing::Types<int, char>;
TYPED_TEST_SUITE(TestGraph, TestParams);

TYPED_TEST(TestGraph, Contructor) {
  const Graph<TypeParam> graph;
  EXPECT_TRUE(graph.IsEmpty());
}

TYPED_TEST(TestGraph, AddVertex) {
  const TypeParam vertex = 0;
  Graph<TypeParam> graph;
  graph.AddVertex(vertex);
  EXPECT_FALSE(graph.IsEmpty());
  EXPECT_FALSE(graph.HasEdge(vertex, 0));
  EXPECT_FALSE(graph.HasEdge(0, vertex));
  EXPECT_EQ(graph.adj_list().at(vertex).size(), 0u);
}

TYPED_TEST(TestGraph, AddEdge) {
  const TypeParam vertex = 0, other_vertex = 1;
  Graph<TypeParam> graph;
  graph.AddEdge(vertex, other_vertex);
  EXPECT_FALSE(graph.IsEmpty());
  EXPECT_TRUE(graph.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(graph.HasEdge(other_vertex, vertex));
  EXPECT_EQ(graph.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(graph.adj_list().at(other_vertex).size(), 1u);
}

TYPED_TEST(TestGraph, AddEdgeTwice) {
  const TypeParam vertex = 0, other_vertex = 1;
  Graph<TypeParam> graph;
  graph.AddEdge(vertex, other_vertex);
  graph.AddEdge(vertex, other_vertex);
  EXPECT_FALSE(graph.IsEmpty());
  EXPECT_TRUE(graph.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(graph.HasEdge(other_vertex, vertex));
  EXPECT_EQ(graph.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(graph.adj_list().at(other_vertex).size(), 1u);
}

TYPED_TEST(TestGraph, AddEdgeDirected) {
  const TypeParam vertex = 0, other_vertex = 1;
  Graph<TypeParam> graph;
  graph.AddEdge(vertex, other_vertex, false);
  EXPECT_FALSE(graph.IsEmpty());
  EXPECT_TRUE(graph.HasEdge(vertex, other_vertex));
  EXPECT_FALSE(graph.HasEdge(other_vertex, vertex));
  EXPECT_EQ(graph.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(graph.adj_list().count(other_vertex), 0u);
}

TYPED_TEST(TestGraph, DFSVisitAllVerticesOnce) {
  std::vector<TypeParam> visited;
  this->graph_.DFS(0, [&visited](const TypeParam& val) { visited.push_back(val); });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(0, 1, 2, 3, 5, 4, 6, 7, 8));
}

TYPED_TEST(TestGraph, DFSVisitIsolatedVerticesOnce) {
  std::vector<TypeParam> visited;
  this->graph_.DFS(8, [&visited](const TypeParam& val) { visited.push_back(val); });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(7, 8));
}

TYPED_TEST(TestGraph, BFSVisitAllVerticesOnce) {
  std::vector<TypeParam> visited;
  this->graph_.BFS(0, [&visited](const TypeParam& val) { visited.push_back(val); });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(0, 1, 3, 4, 5, 2, 6, 7, 8));
}

TYPED_TEST(TestGraph, BFSVisitIsolatedVerticesOnce) {
  std::vector<TypeParam> visited;
  this->graph_.BFS(8, [&visited](const TypeParam& val) { visited.push_back(val); });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(7, 8));
}

TYPED_TEST(TestGraph, Stdout) { EXPECT_NO_THROW(std::cout << this->graph_); }
