/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Driver form the parsing and execution of onnx files.
 *
 * The drivers reads the onnx file and uses the information in it to update the context by running all the nodes
 * from the input to the output of the graph.
 */
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

/**
 * The OnnxDriver class reads the onnx file.
 *
 * The information collected is used to update the context by running all the nodes,
 * from the input to the output of the graph.
 */
class OnnxDriver : public Driver {
 public:
  /**
   * Construct a new parser driver context.
   * @param context context filled during parsing
   */
  explicit OnnxDriver(Context& context);  // NOLINT(runtime/references): Reference context filled during parsing.

  bool ParseStreamCore(std::istream& in) override;
  bool ParseFile(const std::string& filename) override;

  /** @getter{variables, Driver} */
  [[nodiscard]] const std::unordered_map<std::string, Tensor>& variables() const { return variables_; }
  /** @getter{available_inputs, Driver} */
  [[nodiscard]] const std::unordered_map<std::string, Tensor>& available_inputs() const { return available_inputs_; }
  /** @getter{model, Driver} */
  [[nodiscard]] const ::onnx::ModelProto& model() const { return model_; }
  /** @getter{graph, Driver} */
  [[nodiscard]] const ::onnx::GraphProto& graph() const { return model_.graph(); }

 private:
  static const std::map<std::string, std::function<void(OnnxDriver&, const ::onnx::NodeProto&)>>
      node_handlers;  ///< Map between node op_type and the corresponding handler..

  /**
   * Get the attribute @p name from the @p node.
   *
   * If the attribute is not found, the @p default_value is returned.
   * If no @p default_value is provided, an exception is thrown.
   * @tparam T type of the attribute to get.
   * Limited to
   * - bool
   * - float
   * - int64_t
   * - string
   * - vector<float>,
   * - vector<int64_t>
   * - vector<string>
   * - const ::onnx::TensorProto*.
   * @param node node to get the attribute from
   * @param name name of the attribute
   * @param default_value optional default value. If the attribute is not found, this value is returned.
   * @return attribute value
   * @throw std::runtime_error if the attribute is not found and no default value is provided
   */
  template <IsAnyOf<bool, float, std::int64_t, std::string, std::vector<float>, std::vector<std::int64_t>,
                    std::vector<std::string>, const ::onnx::TensorProto*>
                T>
  T GetAttribute(const ::onnx::NodeProto& node, const std::string& name,
                 const std::optional<T>& default_value = {}) const;

  static void EnsureInput(const ::onnx::NodeProto& node, int lb, int ub);
  static void EnsureInput(const ::onnx::NodeProto& node, int exact);

  /** Parse the @ref model_ 's graph */
  void ParseGraph();
  /**
   * Go through all the nodes in the graph and construct the final assertions.
   *
   * For a queue with all the nodes in the graph.
   * The queue is iterated until it is empty, or until no other node can be added.
   * After a node has been successfully added, the corresponding node is removed from the queue and its outputs are
   * made available in the @ref available_inputs_.
   */
  void AddNodes();
  /**
   * Go through a specific node and add the corresponding assertions.
   *
   * If any of the inputs required by the node is missing, the node is not added.
   * If the node is successfully added, the outputs are made available in the @ref available_inputs_.
   * @param node node to add
   * @return true if the node was added
   * @return false if the node was not added (e.g. some of the inputs are not yet available)
   */
  bool AddNode(const ::onnx::NodeProto& node);
  /**
   * Add the input and output to the Context.
   * @param value_info value_info to add
   * @param is_input true if the value_info is an input
   */
  void AddValueInfo(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  /**
   * Add the input and output to the Context.
   * @param value_info value_info to add
   * @param is_input true if the value_info is an input
   */
  void AddValueInfoTensor(const ::onnx::ValueInfoProto& value_info, bool is_input = false);
  /**
   * Add an initializer to the @ref available_inputs_.
   * @param tensor tensor to add
   */
  void AddInitializer(const ::onnx::TensorProto& tensor);
  /**
   * Add the formulas to the Context.
   * @param output name of the output
   */
  void AddFormula(const std::string& output);

  /**
   * Add a node to the context.
   * @tparam T type of the node
   * @param node node to add
   */
  template <NodeOpType T>
  void AddNode(const ::onnx::NodeProto& node);

  /**
   * Associate to a linear expression a fresh variable.
   *
   * The variable is created and added to the @ref equal_vars_.
   * If the same expression is passed again, the same variable is returned.
   * @param expression expression to associate with a variable
   * @return corresponding variable
   */
  const Variable& ToEqualVar(const Expression& expression);

  ::onnx::ModelProto model_{};                                ///< The onnx model obtained from the file.
  std::unordered_map<std::string, Tensor> variables_;         ///< Variables in the model.
  std::unordered_map<std::string, Tensor> available_inputs_;  ///< Available inputs in the model.
  std::unordered_map<Expression, Variable> equal_vars_;       ///< Variables created to summarize linear constraints.
};
}  // namespace dlinear::onnx
