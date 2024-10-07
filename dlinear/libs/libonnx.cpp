/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "libonnx.h"

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const onnx::GraphProto &graph) {
  return os << "GraphProto(" << graph.name() << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TensorProto &tensor) {
  os << "TensorProto(";
  if (tensor.has_data_type()) os << "data_type: " << tensor.data_type() << ", ";
  if (tensor.has_doc_string()) os << "doc_string: " << tensor.doc_string() << ", ";
  if (tensor.has_name()) os << "name: " << tensor.name() << ", ";
  if (tensor.has_segment()) os << "segment: " << tensor.segment() << ", ";
  return os << "dims: " << tensor.dims() << ")";
}

std::ostream &operator<<(std::ostream &os, const google::protobuf::RepeatedField<int64_t> &int64s) {
  os << "[";
  std::copy(int64s.begin(), std::prev(int64s.end()), std::ostream_iterator<int64_t>(os, ", "));
  return os << *(int64s.rbegin()) << "]";
}

std::ostream &operator<<(std::ostream &os, const onnx::TensorProto_Segment &tensor_segment) {
  os << "TensorProto_Segment(";
  if (tensor_segment.has_begin()) os << "begin: " << tensor_segment.begin() << ", ";
  if (tensor_segment.has_end()) os << "end: " << tensor_segment.end() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::SparseTensorProto &tensor) {
  os << "SparseTensorProto(";
  if (tensor.has_indices()) os << "indices: " << tensor.indices() << ", ";
  if (tensor.has_values()) os << "values: " << tensor.values() << ", ";
  std::cout << "dims: " << tensor.dims();
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::AttributeProto &attribute) {
  os << "AttributeProto(";
  if (attribute.has_name()) os << "name: " << attribute.name() << ", ";
  if (attribute.has_type()) os << "type: " << attribute.type() << ", ";
  if (attribute.has_doc_string()) os << "doc_string: " << attribute.doc_string() << ", ";
  if (attribute.has_f()) os << "f: " << attribute.f() << ", ";
  if (attribute.has_i()) os << "i: " << attribute.i() << ", ";
  if (attribute.has_s()) os << "s: " << attribute.s() << ", ";
  if (attribute.has_t()) os << "t: " << attribute.t() << ", ";
  if (attribute.has_g()) os << "g: " << attribute.g() << ", ";
  if (attribute.has_sparse_tensor()) os << "sparse_tensor: " << attribute.sparse_tensor() << ", ";
  if (attribute.floats_size() > 0) {
    os << "floats: [";
    std::copy(attribute.floats().begin(), std::prev(attribute.floats().end()), std::ostream_iterator<float>(os, ", "));
    os << attribute.floats().rbegin()[0] << "], ";
  }
  if (attribute.ints_size() > 0) {
    os << "ints: [";
    std::copy(attribute.ints().begin(), std::prev(attribute.ints().end()), std::ostream_iterator<int64_t>(os, ", "));
    os << attribute.ints().rbegin()[0] << "], ";
  }
  if (attribute.strings_size() > 0) {
    os << "strings: [";
    std::copy(attribute.strings().begin(), std::prev(attribute.strings().end()),
              std::ostream_iterator<std::string>(os, ", "));
    os << attribute.strings().rbegin()[0] << "], ";
  }
  if (attribute.tensors_size() > 0) {
    os << "tensors: [";
    for (const auto &tensor : attribute.tensors()) os << tensor << ", ";
    os << "], ";
  }
  //  if (attribute.graphs_size() > 0) {
  //    os << "graphs: [";
  //    std::copy(attribute.graphs().begin(), std::prev(attribute.graphs().end()),
  //              std::ostream_iterator<onnx::GraphProto>(os, ", "));
  //    os << *attribute.graphs().rbegin() << "], ";
  //  }
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::NodeProto &node) {
  os << "NodeProto(";
  if (node.has_name()) os << "name: " << node.name() << ", ";
  if (node.has_op_type()) os << "op_type: " << node.op_type() << ", ";
  if (node.has_domain()) os << "domain: " << node.domain() << ", ";
  if (node.has_doc_string()) os << "doc_string: " << node.doc_string() << ", ";
  if (node.input_size() > 0) {
    os << "inputs: [";
    std::copy(node.input().begin(), std::prev(node.input().end()), std::ostream_iterator<std::string>(os, ", "));
    os << node.input().rbegin()[0] << "], ";
  }
  if (node.output_size() > 0) {
    os << "outputs: [";
    std::copy(node.output().begin(), std::prev(node.output().end()), std::ostream_iterator<std::string>(os, ", "));
    os << node.output().rbegin()[0] << "], ";
  }
  if (node.attribute_size() > 0) {
    os << "attributes: [";
    for (const auto &attr : node.attribute()) os << attr << ", ";
    os << "], ";
  }
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::ValueInfoProto &value_info) {
  os << "ValueInfoProto(";
  if (value_info.has_name()) os << "name: " << value_info.name() << ", ";
  if (value_info.has_type()) os << "type: " << value_info.type() << ", ";
  if (value_info.has_doc_string()) os << "doc_string: " << value_info.doc_string() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto &type) {
  os << "TypeProto(";
  if (type.has_tensor_type()) os << "tensor_type: " << type.tensor_type() << ", ";
  if (type.has_sequence_type()) os << "sequence_type: " << type.sequence_type() << ", ";
  if (type.has_map_type()) os << "map_type: " << type.map_type() << ", ";
  if (type.has_opaque_type()) os << "opaque_type: " << type.opaque_type() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Sequence &type_sequence) {
  os << "TypeProto_Sequence(";
  if (type_sequence.has_elem_type()) os << "elem_type: " << type_sequence.elem_type() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Map &type_map) {
  os << "TypeProto_Map(";
  if (type_map.has_key_type()) os << "key_type: " << type_map.key_type() << ", ";
  if (type_map.has_value_type()) os << "value_type: " << type_map.value_type() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Tensor &type_tensor) {
  os << "TypeProto_Tensor(";
  if (type_tensor.has_elem_type()) os << "elem_type: " << type_tensor.elem_type() << ", ";
  if (type_tensor.has_shape()) os << "shape: " << type_tensor.shape() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Opaque &type_opaque) {
  os << "TypeProto_Opaque(";
  if (type_opaque.has_domain()) os << "domain: " << type_opaque.domain() << ", ";
  if (type_opaque.has_name()) os << "name: " << type_opaque.name() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TensorShapeProto &tensor_shape) {
  os << "TensorShapeProto(";
  for (const auto &dim : tensor_shape.dim()) os << "dim: " << dim << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os, const onnx::TensorShapeProto_Dimension &tensor_shape_dim) {
  os << "TensorShapeProto_Dimension(";
  if (tensor_shape_dim.has_denotation()) os << "denotation: " << tensor_shape_dim.denotation() << ", ";
  if (tensor_shape_dim.has_dim_value()) os << "dim_value: " << tensor_shape_dim.dim_value() << ", ";
  if (tensor_shape_dim.has_dim_param()) os << "dim_param: " << tensor_shape_dim.dim_param() << ", ";
  return os << ")";
}

std::ostream &operator<<(std::ostream &os,
                         const google::protobuf::RepeatedPtrField<onnx::ValueInfoProto> &value_infos) {
  os << "ValueInfoProto[";
  for (const auto &value_info : value_infos) os << value_info << ", ";
  return os << "]";
}
std::ostream &operator<<(std::ostream &os, const google::protobuf::RepeatedPtrField<onnx::TensorProto> &tensors) {
  os << "TensorProto[";
  for (const auto &tensor : tensors) os << tensor << ", ";
  return os << "]";
}

}  // namespace dlinear
