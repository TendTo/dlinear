#pragma once

#include <memory>
#include <ostream>
#include <string>
#include <utility>

#include "dlinear/smt2/logic.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/smt2/CommandCell.h"

namespace dlinear {

class CommandCell;

/** Command class in smt2lib. It only includes a shared_ptr to CommandCell. */
class Command {
 public:
  explicit Command(std::shared_ptr<CommandCell> ptr) : ptr_{std::move(ptr)} {}

 private:
  std::shared_ptr<CommandCell> ptr_;

  friend std::ostream &operator<<(std::ostream &os, const Command &c);
};
std::ostream &operator<<(std::ostream &os, const Command &c);

Command assert_command(const Formula &f);
Command check_sat_command();
Command exit_command();
Command pop_command(int level);
Command push_command(int level);
Command reset_command();
Command set_info_command(const std::string &key, const std::string &val);
Command set_logic_command(Logic logic);
Command set_option_command(const std::string &key, const std::string &val);

}  // namespace dlinear
