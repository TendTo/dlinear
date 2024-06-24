#pragma once

#include <istream>
#include <list>
#include <string>
#include <unordered_map>

#include "dlinear/libs/libeigen.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libonnx.h"
#include "dlinear/parser/Driver.h"
#include "dlinear/parser/onnx/Matrix.h"
#include "dlinear/parser/onnx/NodeOpType.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear::onnxfile {

class OnnxDriver : public Driver {
 public:
  /// construct a new parser driver context
  explicit OnnxDriver(Context& context);  // NOLINT(runtime/references): Reference context filled during parsing.

  bool ParseStreamCore(std::istream& in) override;
  bool ParseFile(const std::string& filename) override;

  const std::unordered_map<std::string, Matrix>& variables() const { return variables_; }
  const std::unordered_map<std::string, Matrix>& available_inputs() const { return available_inputs_; }
  const ::onnx::ModelProto& model() const { return model_; }
  const ::onnx::GraphProto& graph() const { return model_.graph(); }

 private:
  void ParseGraph();
  void AddNodes();
  bool AddNode(const ::onnx::NodeProto& node);
  void AddValueInfo(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  void AddValueInfoTensor(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  void AddInitializer(const ::onnx::TensorProto& tensor);
  void AddFormula(const std::string& output);

  template <NodeOpType T>
  void AddNodeImpl(const ::onnx::NodeProto& node);

  ::onnx::ModelProto model_{};
  std::unordered_map<std::string, Matrix> variables_;
  std::unordered_map<std::string, Matrix> available_inputs_;
};
}  // namespace dlinear::onnxfile
