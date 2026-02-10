/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Utility sscript used to convert an mps file to an smt file.
 *
 * In short, it uses all the linear constraints to build a series of assertions.
 */
#include <filesystem>
#include <functional>
#include <iostream>
#include <numeric>
#include <string>

#include "dlinear/parser/mps/Driver.h"
#include "dlinear/parser/smt2/Driver.h"

int mps_to_smt2(int argc, char* argv[]) {
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " <filename>" << std::endl;
    return 1;
  }
  dlinear::Config config{std::string{argv[1]}};
  dlinear::Context context{config};
  dlinear::mps::MpsDriver driver{context};
  driver.ParseFile(config.filename());
  driver.ToSmt2(std::cout);

  return 0;
}

int smt2_stats(int argc, char* argv[]) {
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " <filename>" << std::endl;
    return 1;
  }
  dlinear::Config config{std::string{argv[1]}};
  config.m_disable_expansion() = true;
  config.m_formula_evaluation_preprocess_step() = dlinear::Config::ExecutionStep::NEVER;
  config.m_simple_bound_propagation_step() = dlinear::Config::ExecutionStep::NEVER;
  config.m_eq_binomial_preprocess_step() = dlinear::Config::ExecutionStep::NEVER;
  dlinear::Context context{config};
  dlinear::smt2::Smt2Driver driver{context};
  if (!driver.ParseFile(config.filename())) {
    std::cerr << "Failed to parse file: " << config.filename() << std::endl;
    return 1;
  }

  // Get the file size of the input file
  const size_t file_size = std::filesystem::file_size(config.filename());

  const int num_variables = context.box().size();
  const size_t num_assertions = context.assertions().size();
  const size_t max_assertion_size =
      std::max_element(context.assertions().begin(), context.assertions().end(),
                       [](const auto& lhs, const auto& rhs) {
                         return lhs.GetFreeVariables().size() < rhs.GetFreeVariables().size();
                       })
          ->GetFreeVariables()
          .size();
  const size_t min_assertion_size =
      std::min_element(context.assertions().begin(), context.assertions().end(),
                       [](const auto& lhs, const auto& rhs) {
                         return lhs.GetFreeVariables().size() < rhs.GetFreeVariables().size();
                       })
          ->GetFreeVariables()
          .size();
  const size_t avg_assertion_size = std::accumulate(context.assertions().begin(), context.assertions().end(), 0,
                                                    [](const auto& acc, const auto& assertion) {
                                                      return acc + assertion.GetFreeVariables().size();
                                                    }) /
                                    num_assertions;
  std::cout << "filename,file_size,n_variables,n_assertions,avg_assertion_size,min_assertion_size,max_assertion_size"
            << std::endl;
  std::cout << argv[1] << "," << file_size << "," << num_variables << "," << num_assertions << "," << avg_assertion_size
            << "," << min_assertion_size << "," << max_assertion_size << std::endl;

  return 0;
}

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: " << argv[0] << " <command> [args...]" << std::endl;
    return 1;
  }

  const std::string command{argv[1]};
  if (command == "mps_to_smt2") {
    return mps_to_smt2(argc - 1, argv + 1);
  } else if (command == "smt2_stats") {
    return smt2_stats(argc - 1, argv + 1);
  } else {
    std::cerr << "Unknown command: " << command << std::endl;
    return 1;
  }
}
