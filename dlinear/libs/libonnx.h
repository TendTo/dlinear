/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Onnx wrapper.
 */
#pragma once

#include <istream>

#pragma GCC system_header

#include "onnx/onnx-data.pb.h"
#include "onnx/onnx-ml.pb.h"
#include "onnx/onnx-operators-ml.pb.h"

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const onnx::ModelProto &model);
std::ostream &operator<<(std::ostream &os, const onnx::GraphProto &graph);
std::ostream &operator<<(std::ostream &os, const onnx::NodeProto &node);
std::ostream &operator<<(std::ostream &os, const onnx::AttributeProto &attribute);
std::ostream &operator<<(std::ostream &os, const onnx::ValueInfoProto &value_info);

std::ostream &operator<<(std::ostream &os, const onnx::SparseTensorProto &tensor);
std::ostream &operator<<(std::ostream &os, const onnx::TensorProto &tensor);
std::ostream &operator<<(std::ostream &os, const onnx::TensorProto_Segment &tensor_segment);

std::ostream &operator<<(std::ostream &os, const onnx::TypeProto &type);
std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Map &type_map);
std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Tensor &type_tensor);
std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Opaque &type_opaque);
std::ostream &operator<<(std::ostream &os, const onnx::TypeProto_Sequence &type_sequence);

std::ostream &operator<<(std::ostream &os, const onnx::TensorShapeProto &tensor_shape);
std::ostream &operator<<(std::ostream &os, const onnx::TensorShapeProto_Dimension &tensor_shape_dim);

std::ostream &operator<<(std::ostream &os, const google::protobuf::RepeatedField<int64_t> &int64s);

std::ostream &operator<<(std::ostream &os, const google::protobuf::RepeatedPtrField<onnx::ValueInfoProto> &value_infos);
std::ostream &operator<<(std::ostream &os, const google::protobuf::RepeatedPtrField<onnx::TensorProto> &tensors);

}  // namespace dlinear
