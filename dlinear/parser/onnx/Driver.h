#pragma once

#include <functional>
#include <istream>
#include <list>
#include <map>
#include <optional>
#include <string>
#include <unordered_map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libonnx.h"
#include "dlinear/parser/Driver.h"
#include "dlinear/parser/onnx/NodeOpType.h"
#include "dlinear/parser/onnx/Tensor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/concepts.h"

namespace dlinear::onnx {

class OnnxDriver : public Driver {
 public:
  /// construct a new parser driver context
  explicit OnnxDriver(Context& context);  // NOLINT(runtime/references): Reference context filled during parsing.

  bool ParseStreamCore(std::istream& in) override;
  bool ParseFile(const std::string& filename) override;

  const std::unordered_map<std::string, Tensor>& variables() const { return variables_; }
  const std::unordered_map<std::string, Tensor>& available_inputs() const { return available_inputs_; }
  const ::onnx::ModelProto& model() const { return model_; }
  const ::onnx::GraphProto& graph() const { return model_.graph(); }

 private:
  static const std::map<std::string, std::function<void(OnnxDriver&, const ::onnx::NodeProto&)>> node_handlers;

  static const ::onnx::AttributeProto* FindAttribute(const ::onnx::NodeProto& node, const std::string& name,
                                                     ::onnx::AttributeProto_AttributeType expectedType,
                                                     bool throw_on_missing = false);

  template <IsAnyOf<bool, float, std::int64_t, std::string, std::vector<float>, std::vector<std::int64_t>,
                    std::vector<std::string>, const ::onnx::TensorProto*>
                T>
  T GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                 const std::optional<T>& default_value = {}) const;

  static void EnsureInput(const ::onnx::NodeProto& node, int lb, int ub);
  static void EnsureInput(const ::onnx::NodeProto& node, int exact);

  void ParseGraph();
  void AddNodes();
  bool AddNode(const ::onnx::NodeProto& node);
  void AddValueInfo(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  void AddValueInfoTensor(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  void AddInitializer(const ::onnx::TensorProto& tensor);
  void AddFormula(const std::string& output);

  template <NodeOpType T>
  void AddNode(const ::onnx::NodeProto& node);

  ::onnx::ModelProto model_{};
  std::unordered_map<std::string, Tensor> variables_;
  std::unordered_map<std::string, Tensor> available_inputs_;
};
}  // namespace dlinear::onnx
