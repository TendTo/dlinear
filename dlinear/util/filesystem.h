/**
 * @file filesystem.h
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 * @brief Utilities for filesystem operations.
 *
 * Simple utilities that make operations on the filesystem easier.
 */
#pragma once

#include <string>
#include <vector>

namespace dlinear {

/**
 * Check if the file exists.
 * @param name The name of the file.
 * @return whether or not the file exists.
 */
bool file_exists(const std::string &name);

/**
 * Check if the directory exists.
 * @param name The name of the directory.
 * @return whether or not the directory exists.
 */
bool dir_exists(const std::string &name);

/**
 * Get the extension of the file.
 *
 * Extracts the extension from @p name, meaning the part of the file name
 * after the last dot.
 * @note It returns an empty string if there is no extension in @p name.
 * @param name The name of the file.
 * @return The extension of the file.
 */
std::string get_extension(const std::string &name);

/**
 * Split a C-string by whitespace.
 *
 * Each word is returned as a separate string in a vector.
 * @note This function is not Unicode-aware.
 * @note The words are trimmed.
 * @param in input string to split
 * @return vector os strings
 */
std::vector<std::string> split_string_by_whitespace(const char *in);

}  // namespace dlinear
