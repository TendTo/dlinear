/**
 * @file OptionValue.h
 * @author tend
 * @date 12 Aug 2023
 * @copyright 2023 tend
 * @brief OptionValue class.
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

#ifndef DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_H_
#define DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_H_

#include <iostream>

namespace dlinear {

/**
 * @brief Represents an optional value in dLinear.
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
   * @brief Constructs an option value with @p value.
   *
   * @param value value to be held.
   */
  explicit OptionValue(T value)
      : value_{std::move(value)}, type_{Type::DEFAULT} {}

  /**
   * @brief Default copy constructor.
   */
  OptionValue(const OptionValue &) = default;

  /**
   * @brief Default move constructor.
   */
  OptionValue(OptionValue &&) noexcept = default;

  /**
   * @brief Default copy assign operator.
   */
  OptionValue &operator=(const OptionValue &) = default;

  /**
   * @brief Default move assign operator.
   */
  OptionValue &operator=(OptionValue &&) noexcept = default;

  /**
   * @brief Default destructor.
   */
  ~OptionValue() = default;

  /**
   * @brief Copy-assign operator for T.
   *
   * @note It sets value with `Type::FROM_CODE` type.
   */
  OptionValue &operator=(const T &value);

  /**
   * @brief Move-assign operator for T.
   *
   * @note It sets value with `Type::FROM_CODE` type.
   */
  OptionValue &operator=(T &&value);

  /**
   * @brief Returns the value.
   */
  const T &get() const { return value_; }

  /**
   * @brief Sets the value to @p value which is given by a command-line argument.
   *
   * @param value new value, given by a command-line argument.
   */
  void set_from_command_line(const T &value);

  /**
   * @brief Sets the value to @p value which is provided from a file.
   *
   * @param value new value, provided from a file.
   */
  void set_from_file(const T &value);

  friend std::ostream &operator<<(std::ostream &os, Type type);

 private:
  T value_; ///< Value the class holds.
  Type type_; ///< Type of the value.
};

} // dlinear

#endif //DLINEAR5_DLINEAR_UTIL_OPTIONVALUE_H_
