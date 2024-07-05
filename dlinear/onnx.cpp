#include <fstream>
#include <numeric>

#include "dlinear/libs/libonnx.h"

using namespace ::onnx;

void set_dim(TensorShapeProto& shape, std::int64_t value) {
  TensorShapeProto_Dimension dim{};
  dim.set_dim_value(value);
  shape.mutable_dim()->Add(std::move(dim));
}

void set_dim(TensorShapeProto& shape, std::initializer_list<int64_t> values) {
  shape.mutable_dim()->Clear();
  for (int64_t value : values) {
    set_dim(shape, value);
  }
}

void set_dims(TensorShapeProto& shape, std::initializer_list<int64_t> values) {
  shape.mutable_dim()->Clear();
  for (int64_t value : values) {
    set_dim(shape, value);
  }
}

void set_dims_input(GraphProto& graph, int input_idx, std::initializer_list<int64_t> values) {
  set_dims(*graph.mutable_input(input_idx)->mutable_type()->mutable_tensor_type()->mutable_shape(), values);
}

void set_dims_output(GraphProto& graph, int output_idx, std::initializer_list<int64_t> values) {
  set_dims(*graph.mutable_output(output_idx)->mutable_type()->mutable_tensor_type()->mutable_shape(), values);
}

void set_node_op_type(GraphProto& graph, int node_idx, const std::string& op_type) {
  graph.mutable_node(node_idx)->mutable_op_type()->assign(op_type);
}

void set_initializer_dims(GraphProto& graph, int initializer_idx, std::initializer_list<int64_t> dims,
                          std::initializer_list<float> values) {
  if (static_cast<int64_t>(values.size()) != std::accumulate(dims.begin(), dims.end(), 1, std::multiplies<>())) {
    throw std::runtime_error("values size does not match dims");
  }
  std::vector<float> data(values.begin(), values.end());
  graph.mutable_initializer(initializer_idx)->mutable_float_data()->Add(data.begin(), data.end());
  graph.mutable_initializer(initializer_idx)->mutable_dims()->Clear();
  for (int64_t dim : dims) {
    graph.mutable_initializer(initializer_idx)->mutable_dims()->Add(dim);
  }
  graph.mutable_initializer(initializer_idx)->mutable_name()->assign("initializer" + std::to_string(initializer_idx));
  graph.mutable_initializer(initializer_idx)->set_data_type(TensorProto_DataType_FLOAT);
}

void set_initializer_dims(GraphProto& graph, int initializer_idx, std::initializer_list<int64_t> dims,
                          std::initializer_list<std::int64_t> values) {
  if (static_cast<int64_t>(values.size()) != std::accumulate(dims.begin(), dims.end(), 1, std::multiplies<>())) {
    throw std::runtime_error("values size does not match dims");
  }
  std::vector<int> data(values.begin(), values.end());
  graph.mutable_initializer(initializer_idx)->mutable_int64_data()->Add(data.begin(), data.end());
  graph.mutable_initializer(initializer_idx)->mutable_dims()->Clear();
  for (int64_t dim : dims) {
    graph.mutable_initializer(initializer_idx)->mutable_dims()->Add(dim);
  }
  graph.mutable_initializer(initializer_idx)->mutable_name()->assign("initializer" + std::to_string(initializer_idx));
  graph.mutable_initializer(initializer_idx)->set_data_type(TensorProto_DataType_INT64);
}

template <class T>
void add_initializer(GraphProto& graph, std::initializer_list<int64_t> dims, std::initializer_list<T> values) {
  graph.add_initializer();
  set_initializer_dims(graph, graph.initializer_size() - 1, dims, values);
}

void set_node_input(GraphProto& graph, int node_idx, std::initializer_list<std::string> inputs) {
  graph.mutable_node(node_idx)->clear_input();
  for (const std::string& input : inputs) {
    graph.mutable_node(node_idx)->add_input()->assign(input);
  }
}

void add_node_attribute(GraphProto& graph, int node_idx, const AttributeProto& attr) {
  graph.mutable_node(node_idx)->add_attribute()->CopyFrom(attr);
}

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <onnx_model>" << std::endl;
    return 1;
  }
  std::ifstream in(argv[1], std::ios::binary);
  ModelProto model_;
  const bool res = model_.ParseFromIstream(&in);
  if (!res) {
    std::cerr << "OnnxDriver::ParseStreamCore(): Failed to parse model from input stream" << std::endl;
    return 1;
  }

  GraphProto& graph = *model_.mutable_graph();
  std::set<std::string> op_types;
  for (const NodeProto& node : graph.node()) {
    op_types.insert(node.op_type());
  }
  std::cout << "Op types: ";
  for (const std::string& op_type : op_types) {
    std::cout << op_type << " ";
  }
  std::cout << std::endl;

  set_dims_input(graph, 0, {3, 2});
  set_dims_output(graph, 0, {2, 2, 2});

  set_node_op_type(graph, 0, "Gather");
  set_node_input(graph, 0, {"x", "initializer0"});
  //  TensorProto tensor{};
  //  std::vector<float> data{1.0f,  -2.0f,  3.0f,  -4.0f,  5.0f,  -6.0f,  7.0f,  -8.0f,  9.0f,  -10.0f,
  //                          11.0f, -12.0f, 13.0f, -14.0f, 15.0f, -16.0f, 17.0f, -18.0f, 19.0f, -20.0f,
  //                          21.0f, -22.0f, 23.0f, -24.0f, 25.0f, -26.0f, 27.0f, -28.0f, 29.0f, -30.0f,
  //                          31.0f, -32.0f, 33.0f, -34.0f, 35.0f, -36.0f, 37.0f, -38.0f, 39.0f, -40.0f};
  //  tensor.mutable_float_data()->Assign(data.begin(), data.end());
  //  tensor.mutable_dims()->Add(2);
  //  tensor.mutable_dims()->Add(4);
  //  tensor.mutable_dims()->Add(5);
  //  tensor.set_data_type(TensorProto_DataType_FLOAT);
  AttributeProto attr{};
  attr.set_i(0);
  add_node_attribute(graph, 0, attr);

  add_initializer(graph, {2, 2}, {0l, 1l, 1l, 2l});

  std::cout << "GraphProto: " << graph.DebugString() << std::endl;
  std::ofstream out(std::string{argv[1]} + ".out.onnx", std::ios::binary);
  model_.SerializePartialToOstream(&out);
  return 0;
}
