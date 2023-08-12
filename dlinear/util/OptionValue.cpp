/**
 * @file OptionValue.cpp
 * @author tend
 * @date 12 Aug 2023
 * @copyright 2023 tend
 */

#include "OptionValue.h"

namespace dlinear {

template<typename T>
OptionValue<T> &OptionValue<T>::operator=(const T &value) {
  value_ = value;
  type_ = Type::FROM_CODE;
  return *this;
}

template<typename T>
OptionValue<T> &OptionValue<T>::operator=(T &&value) {
  value_ = std::move(value);
  type_ = Type::FROM_CODE;
  return *this;
}

template<typename T>
void OptionValue<T>::set_from_command_line(const T &value) {
  if (type_ != Type::FROM_CODE) {
    value_ = value;
    type_ = Type::FROM_COMMAND_LINE;
  }
}

template<typename T>
void OptionValue<T>::set_from_file(const T &value) {
  switch (type_) {
    case Type::DEFAULT:
    case Type::FROM_FILE:value_ = value;
      type_ = Type::FROM_FILE;
      return;

    case Type::FROM_COMMAND_LINE:
    case Type::FROM_CODE:
      // No operation.
      return;
  }
}

template<typename T>
std::ostream &operator<<(std::ostream &os, typename OptionValue<T>::Type type) {
  switch (type) {
    case OptionValue<T>::Type::DEFAULT:return os << "DEFAULT";
    case OptionValue<T>::Type::FROM_FILE:return os << "FROM_FILE";
    case OptionValue<T>::Type::FROM_COMMAND_LINE:return os << "FROM_COMMAND_LINE";
    case OptionValue<T>::Type::FROM_CODE:return os << "FROM_CODE";
  }
}
} // dlinear