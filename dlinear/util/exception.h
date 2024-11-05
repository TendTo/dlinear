/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Exception classes for dlinear.
 */
#pragma once

#include <stdexcept>
#include <string>

namespace dlinear {

class DlinearException : public std::runtime_error {
 public:
  explicit DlinearException(const char* const message) : std::runtime_error{message} {}
  explicit DlinearException(const std::string& message) : std::runtime_error{message} {}
};

class DlinearNotImplementedException : public DlinearException {
 public:
  DlinearNotImplementedException() : DlinearException("Not yet implemented") {}
  explicit DlinearNotImplementedException(const char* const message) : DlinearException{message} {}
  explicit DlinearNotImplementedException(const std::string& message) : DlinearException{message} {}
};

class DlinearNotSupportedException : public DlinearException {
 public:
  DlinearNotSupportedException() : DlinearException("Not supported") {}
  explicit DlinearNotSupportedException(const char* const message) : DlinearException{message} {}
  explicit DlinearNotSupportedException(const std::string& message) : DlinearException{message} {}
};

class DlinearInvalidArgumentException : public DlinearException, private std::invalid_argument {
 public:
  DlinearInvalidArgumentException() : DlinearException("Invalid argument"), std::invalid_argument{""} {}
  explicit DlinearInvalidArgumentException(const char* const message)
      : DlinearException{message}, std::invalid_argument{message} {}
  explicit DlinearInvalidArgumentException(const std::string& message)
      : DlinearException{message}, std::invalid_argument{message} {}
};

class DlinearAssertionException : public DlinearException {
 public:
  explicit DlinearAssertionException(const char* const message) : DlinearException{message} {}
  explicit DlinearAssertionException(const std::string& message) : DlinearException{message} {}
};

class DlinearLpSolverException : public DlinearException {
 public:
  explicit DlinearLpSolverException(const char* const message) : DlinearException{message} {}
  explicit DlinearLpSolverException(const std::string& message) : DlinearException{message} {}
};

class DlinearSatSolverException : public DlinearException {
 public:
  explicit DlinearSatSolverException(const char* const message) : DlinearException{message} {}
  explicit DlinearSatSolverException(const std::string& message) : DlinearException{message} {}
};

class DlinearParserException : public DlinearException {
 public:
  explicit DlinearParserException(const char* const message) : DlinearException{message} {}
  explicit DlinearParserException(const std::string& message) : DlinearException{message} {}
};

class DlinearOutOfRangeException : public DlinearException, private std::out_of_range {
 public:
  explicit DlinearOutOfRangeException(const char* const message)
      : DlinearException{message}, std::out_of_range{message} {}
  explicit DlinearOutOfRangeException(const std::string& message)
      : DlinearException{message}, std::out_of_range{message} {}
};

class DlinearUnreachableException : public DlinearException {
 public:
  DlinearUnreachableException() : DlinearException("Unreachable code") {}
  explicit DlinearUnreachableException(const char* const message) : DlinearException{message} {}
  explicit DlinearUnreachableException(const std::string& message) : DlinearException{message} {}
};

}  // namespace dlinear