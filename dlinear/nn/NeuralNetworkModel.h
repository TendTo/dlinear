/**
 * @file NeuralNetworkModel.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Neural network model.
 */
#pragma once

#include <list>
#include <string>
#include <unordered_map>

#include "dlinear/libs/libeigen.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libonnx.h"
#include "dlinear/nn/Matrix.h"
#include "dlinear/nn/NodeOpType.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class NeuralNetworkModel {
 public:
  explicit NeuralNetworkModel(const std::string& filename);
  explicit NeuralNetworkModel(std::ifstream& input);

  const std::unordered_map<std::string, const Matrix*>& variables() const { return variables_; }
  const std::unordered_map<std::string, Matrix>& available_inputs() const { return available_inputs_; }
  const onnx::ModelProto& model() const { return model_; }
  const onnx::GraphProto& graph() const { return model_.graph(); }

 private:
  void ParseGraph();
  void AddNodes();
  bool AddNode(const onnx::NodeProto& node);
  void AddValueInfo(const onnx::ValueInfoProto& value_info);
  void AddValueInfoTensor(const onnx::ValueInfoProto& value_info);
  void AddInitializer(const onnx::TensorProto& tensor);

  template <NodeOpType T>
  bool AddNodeImpl(const onnx::NodeProto& node);

  onnx::ModelProto model_;
  std::unordered_map<std::string, const Matrix*> variables_;
  std::unordered_map<std::string, Matrix> available_inputs_;
};

std::ostream& operator<<(std::ostream& os, const NeuralNetworkModel& model);

}  // namespace dlinear
