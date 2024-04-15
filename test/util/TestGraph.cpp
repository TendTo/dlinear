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
using dlinear::VisitResult;

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
  Graph<T, float> graph_;
  Graph<T, float> empty_graph_;

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
  const Graph<TypeParam, float> graph;
  EXPECT_TRUE(graph.IsEmpty());
}

TYPED_TEST(TestGraph, AddVertex) {
  const TypeParam vertex = 0;
  Graph<TypeParam, float> graph;
  graph.AddVertex(vertex);
  EXPECT_FALSE(graph.IsEmpty());
  EXPECT_FALSE(graph.HasEdge(vertex, 0));
  EXPECT_FALSE(graph.HasEdge(0, vertex));
  EXPECT_EQ(graph.adj_list().at(vertex).size(), 0u);
}

TYPED_TEST(TestGraph, AddEdge) {
  const TypeParam vertex = 0, other_vertex = 1;
  this->empty_graph_.AddEdge(vertex, other_vertex);
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().at(other_vertex).size(), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 1.0f);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(other_vertex, vertex), 1.0f);
}

TYPED_TEST(TestGraph, AddEdgeTwice) {
  const TypeParam vertex = 0, other_vertex = 1;
  this->empty_graph_.AddEdge(vertex, other_vertex);
  this->empty_graph_.AddEdge(vertex, other_vertex);
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().at(other_vertex).size(), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 1.0f);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(other_vertex, vertex), 1.0f);
}

TYPED_TEST(TestGraph, AddEdgeDirected) {
  const TypeParam vertex = 0, other_vertex = 1;
  this->empty_graph_.AddEdge(vertex, other_vertex, false);
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_FALSE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().count(other_vertex), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 1.0f);
  EXPECT_EQ(this->empty_graph_.GetEdgeWeight(other_vertex, vertex), nullptr);
}

TYPED_TEST(TestGraph, AddEdgeWeighted) {
  const TypeParam vertex = 0, other_vertex = 1;
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f));
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().at(other_vertex).size(), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 2.0f);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(other_vertex, vertex), 1.0f / 2.0f);
}

TYPED_TEST(TestGraph, AddEdgeTwiceWeighted) {
  const TypeParam vertex = 0, other_vertex = 1;
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f));
  EXPECT_TRUE(this->empty_graph_.AddEdge(vertex, other_vertex, 4.0f));
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_TRUE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().at(other_vertex).size(), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 4.0f);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(other_vertex, vertex), 1.0f / 4.0f);
}

TYPED_TEST(TestGraph, AddEdgeDirectedWeighted) {
  const TypeParam vertex = 0, other_vertex = 1;
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f, false));
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f, false));
  EXPECT_FALSE(this->empty_graph_.IsEmpty());
  EXPECT_TRUE(this->empty_graph_.HasEdge(vertex, other_vertex));
  EXPECT_FALSE(this->empty_graph_.HasEdge(other_vertex, vertex));
  EXPECT_EQ(this->empty_graph_.adj_list().at(vertex).size(), 1u);
  EXPECT_EQ(this->empty_graph_.adj_list().count(other_vertex), 1u);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 2.0f);
  EXPECT_EQ(this->empty_graph_.GetEdgeWeight(other_vertex, vertex), nullptr);
}

TYPED_TEST(TestGraph, GetEdgeWeightPresent) {
  const TypeParam vertex = 0, other_vertex = 1;
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f));
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 2.0f);
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(other_vertex, vertex), 1.0f / 2.0f);
}

TYPED_TEST(TestGraph, GetEdgeWeightAbsent) {
  const TypeParam vertex = 0, other_vertex = 1;
  EXPECT_FALSE(this->empty_graph_.AddEdge(vertex, other_vertex, 2.0f, false));
  EXPECT_EQ(*this->empty_graph_.GetEdgeWeight(vertex, other_vertex), 2.0f);
  EXPECT_EQ(this->empty_graph_.GetEdgeWeight(other_vertex, vertex), nullptr);
  EXPECT_EQ(this->empty_graph_.GetEdgeWeight(other_vertex + 100, vertex), nullptr);
  EXPECT_EQ(this->empty_graph_.GetEdgeWeight(other_vertex, vertex + 100), nullptr);
}

TYPED_TEST(TestGraph, DFSVisitAllVerticesOnce) {
  const TypeParam start = 0;
  std::vector<TypeParam> visited;
  this->graph_.DFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    visited.push_back(to);
    return VisitResult::CONTINUE;
  });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(0, 1, 2, 3, 5, 4, 6, 7, 8));
}

TYPED_TEST(TestGraph, DFSVisitIsolatedVerticesOnce) {
  const TypeParam start = 8;
  std::vector<TypeParam> visited;
  this->graph_.DFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    visited.push_back(to);
    return VisitResult::CONTINUE;
  });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(7, 8));
}

TYPED_TEST(TestGraph, DFSOnAbsentVertexFrom) {
  int counter = 0;
  this->graph_.DFS(10, [&counter](const TypeParam&, const TypeParam&, const float&) {
    counter++;
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(counter, 0);
}

TYPED_TEST(TestGraph, DFSOnAbsentVertexTo) {
  int counter = 0;
  const TypeParam start = 20, end = 30;
  this->graph_.AddEdge(start, end, false);
  this->graph_.DFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      counter++;
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(counter, 1);
}

TYPED_TEST(TestGraph, BFSVisitAllVerticesOnce) {
  const TypeParam start = 0;
  std::vector<TypeParam> visited;
  this->graph_.BFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    visited.push_back(to);
    return VisitResult::CONTINUE;
  });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(0, 1, 3, 4, 5, 2, 6, 7, 8));
}

TYPED_TEST(TestGraph, BFSVisitIsolatedVerticesOnce) {
  const TypeParam start = 8;
  std::vector<TypeParam> visited;
  this->graph_.BFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    visited.push_back(to);
    return VisitResult::CONTINUE;
  });
  EXPECT_THAT(visited, ::testing::UnorderedElementsAre(7, 8));
}

TYPED_TEST(TestGraph, BFSOnAbsentVertexFrom) {
  int counter = 0;
  this->graph_.BFS(10, [&counter](const TypeParam&, const TypeParam&, const float&) {
    counter++;
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(counter, 0);
}

TYPED_TEST(TestGraph, BFSOnAbsentVertexTo) {
  int counter = 0;
  const TypeParam start = 20, end = 30;
  this->graph_.AddEdge(start, end, false);
  this->graph_.BFS(start, [&](const TypeParam& from, const TypeParam& to, const float& weight) {
    if (to == start) {
      EXPECT_EQ(from, to);
      EXPECT_EQ(weight, 0);
    } else {
      counter++;
      EXPECT_NE(from, to);
      EXPECT_EQ(weight, *this->graph_.GetEdgeWeight(from, to));
    }
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(counter, 1);
}

TYPED_TEST(TestGraph, AllPathsIsolated) {
  int count = 0;
  this->graph_.AllPaths(8, 7, [&count](std::vector<TypeParam>& path) {
    count++;
    EXPECT_THAT(path, ::testing::Contains(7));
    EXPECT_THAT(path, ::testing::Contains(8));
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(count, 1);
}

TYPED_TEST(TestGraph, AllPaths) {
  int count = 0;
  this->graph_.AllPaths(0, 6, [&count](std::vector<TypeParam>& path) {
    count++;
    EXPECT_THAT(path, ::testing::Contains(0));
    EXPECT_THAT(path, ::testing::Contains(6));
    return VisitResult::CONTINUE;
  });
  EXPECT_EQ(count, 3);
}

TYPED_TEST(TestGraph, AllPathsStop) {
  int count = 0;
  this->graph_.AllPaths(0, 6, [&count](std::vector<TypeParam>& path) {
    count++;
    EXPECT_THAT(path, ::testing::Contains(0));
    EXPECT_THAT(path, ::testing::Contains(6));
    return VisitResult::STOP;
  });
  EXPECT_EQ(count, 1);
}

TYPED_TEST(TestGraph, AllPathsSingle) {
  int count = 0;
  this->empty_graph_.AddEdge(0, 6, false);
  std::cout << this->empty_graph_ << std::endl;
  this->empty_graph_.AllPaths(0, 6, [&count](std::vector<TypeParam>& path) {
    count++;
    EXPECT_THAT(path, ::testing::Contains(0));
    EXPECT_THAT(path, ::testing::Contains(6));
    return VisitResult::STOP;
  });
  EXPECT_EQ(count, 1);
}

TYPED_TEST(TestGraph, Stdout) { EXPECT_NO_THROW(std::cout << this->graph_ << std::endl); }
