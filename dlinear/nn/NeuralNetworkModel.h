/**
 * @file NeuralNetworkModel.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Neural network model.
 */
#pragma once

#include <string>
#include <unordered_map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libonnx.h"
#include "dlinear/nn/NodeOpType.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class NeuralNetworkModel {
 public:
  explicit NeuralNetworkModel(const std::string& filename);
  explicit NeuralNetworkModel(std::ifstream& input);

  Variables all_variables() const;
  const std::unordered_map<std::string, Variables>& variables() const { return variables_; }
  const std::unordered_map<std::string, std::vector<mpq_class>>& initializers() const { return initializers_; }
  const onnx::ModelProto& model() const { return model_; }
  const onnx::GraphProto& graph() const { return model_.graph(); }

 private:
  void ParseGraph();
  void AddNode(const onnx::NodeProto& node);
  void AddValueInfo(const onnx::ValueInfoProto& value_info);
  void AddValueInfoTensor(const onnx::ValueInfoProto& value_info);
  void AddInitializer(const onnx::TensorProto& tensor);

  template <NodeOpType T>
  void AddNodeImpl(const onnx::NodeProto& node);

  onnx::ModelProto model_;
  std::unordered_map<std::string, Variables> variables_;
  std::unordered_map<std::string, std::vector<mpq_class>> initializers_;
};

std::ostream& operator<<(std::ostream& os, const NeuralNetworkModel& model);

}  // namespace dlinear
