/**
 * @file Command.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Command.h"

#include <memory>

#include "dlinear/parser/smt2/CommandCell.h"

namespace dlinear::smt2 {

std::ostream &operator<<(std::ostream &os, const Command &c) { return c.ptr_->Display(os); }

Command assert_command(const Formula &f) { return Command{std::make_shared<AssertCommand>(f)}; }

Command check_sat_command() { return Command{std::make_shared<CheckSatCommand>()}; }

Command exit_command() { return Command{std::make_shared<ExitCommand>()}; }

Command set_info_command(const std::string &key, const std::string &val) {
  return Command{std::make_shared<SetInfoCommand>(key, val)};
}

Command set_logic_command(Logic logic) { return Command{std::make_shared<SetLogicCommand>(logic)}; }

Command set_option_command(const std::string &key, const std::string &val) {
  return Command{std::make_shared<SetOptionCommand>(key, val)};
}

Command push_command(int level) { return Command{std::make_shared<PushCommand>(level)}; }

Command pop_command(int level) { return Command{std::make_shared<PopCommand>(level)}; }

Command reset_command() { return Command{std::make_shared<ResetCommand>()}; }

}  // namespace dlinear::smt2
