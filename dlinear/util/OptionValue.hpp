/**
 * @file OptionValue.h
 * @author tend
 * @date 12 Aug 2023
 * @copyright 2023 tend
 * OptionValue class.
 *
 * It is used to wrap a value that can be set from multiple sources.
 * The value is overwritten only if it is not set from a higher priority source.
 * The priority is defined as follows, where the higher the number, the higher the priority:
 * 1. Default value
 * 2. Value set by a command-line argument
 * 3. Value provided from a file
 * 4. Value set by a code
 * @see Type
 */

#ifndef DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_HPP_
#define DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_HPP_

#include <iostream>
#include <utility>

using std::ostream;

namespace dlinear {

/**
 * Represents an optional value in dLinear.
 *
 * There are four ways that an option can have its value -- by default, by a
 * command-line argument, by a set-info/set-option command from a .smt2 file,
 * and a manual update in a code. We define an order in these types and make
 * sure that an update is executed only if it is requested by the same type or
 * a higher type. For example, a value set by command-line cannot be changed
 * by an updated requested from a file.
 * @tparam T Type of the value the class will hold.
 */
template<typename T>
class OptionValue {
 public:
  enum class Type {
    DEFAULT,            ///< Default value
    FROM_FILE,          ///< Updated by a set-option/set-info in a file
    FROM_COMMAND_LINE,  ///< Updated by a command-line argument
    FROM_CODE,          ///< Explicitly updated by a code
  };

  /**
   * Constructs an option value with @p value.
   * @param value value to be held.
   */
  explicit OptionValue(T value)
      : value_{std::move(value)}, type_{Type::DEFAULT} {}

  /** Default copy constructor */
  OptionValue(const OptionValue &) = default;

  /** Default move constructor */
  OptionValue(OptionValue &&) noexcept = default;

  /** Default copy assign operator */
  OptionValue &operator=(const OptionValue &) = default;

  /** Default move assign operator */
  OptionValue &operator=(OptionValue &&) noexcept = default;

  /** Default destructor */
  ~OptionValue() = default;

  /**
   * Copy-assign operator for T.
   * @note It sets value with `Type::FROM_CODE` type.
   */
  OptionValue &operator=(const T &value) {
    value_ = value;
    type_ = Type::FROM_CODE;
    return *this;
  }

  /**
   * Move-assign operator for T.
   * @note It sets value with `Type::FROM_CODE` type.
   */
  OptionValue &operator=(T &&value) {
    value_ = std::move(value);
    type_ = Type::FROM_CODE;
    return *this;
  }

  /**
   * Returns the value.
   * @return the value.
   */
  const T &get() const { return value_; }

  /**
   * Sets the value to @p value which is given by a command-line argument.
   * @param value new value, given by a command-line argument.
   */
  void set_from_command_line(const T &value) {
    if (type_ != Type::FROM_CODE) {
      value_ = value;
      type_ = Type::FROM_COMMAND_LINE;
    }
  }

  /**
   * Sets the value to @p value which is provided from a file.
   * @param value new value, provided from a file.
   */
  void set_from_file(const T &value) {
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

  friend ostream &operator<<(ostream &os, Type type) {
    switch (type) {
      case OptionValue<T>::Type::DEFAULT:return os << "DEFAULT";
      case OptionValue<T>::Type::FROM_FILE:return os << "FROM_FILE";
      case OptionValue<T>::Type::FROM_COMMAND_LINE:return os << "FROM_COMMAND_LINE";
      case OptionValue<T>::Type::FROM_CODE:return os << "FROM_CODE";
    }
  }

 private:
  T value_; ///< Value the class holds.
  Type type_; ///< Type of the value.
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_HPP_
