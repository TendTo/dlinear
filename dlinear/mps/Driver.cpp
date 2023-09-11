/**
 * @file Driver.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */

#include "Driver.h"

#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <utility>
#include <vector>

#include "dlinear/mps/parser.yy.hpp"

using std::cerr;
using std::cin;
using std::cout;
using std::endl;
using std::ifstream;
using std::istream;
using std::istringstream;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::string;
using std::vector;

namespace dlinear {

bool MpsDriver::parse_stream(istream &in, const string &sname) {
  streamname_ = sname;

  MpsScanner scanner(&in);
  scanner.set_debug(trace_scanning_);
  this->scanner_ = &scanner;

  MpsParser parser(*this);
  parser.set_debug_level(trace_parsing_);
  return parser.parse() == 0;
}

bool MpsDriver::parse_file(const string &filename) {
  ifstream in(filename.c_str());
  if (!in.good()) {
    return false;
  }
  return parse_stream(in, filename);
}

bool MpsDriver::parse_string(const string &input, const string &sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

void MpsDriver::error(const location &l, const string &m) { cerr << l << " : " << m << endl; }

void MpsDriver::error(const string &m) { cerr << m << endl; }

void MpsDriver::print(int number) const { cout << "Driver::Print " << number << endl; }
void MpsDriver::print(const std::string val) const { cout << "Driver::Print(str) " << val << endl; }

void MpsDriver::AddRow(char sense, const std::string &name) {
  cout << "Driver::AddRow " << sense << " " << name << endl;
}

void MpsDriver::AddColumn(const std::string &row, const std::string &column, double value) {
  cout << "Driver::AddColumn " << row << " " << column << " " << value << endl;
}

void MpsDriver::AddRhs(const std::string &row, const std::string &rhs, double value) {
  cout << "Driver::AddRHS " << row << " " << rhs << " " << value << endl;
}

void MpsDriver::AddRange(const std::string &row, const std::string &rhs, double value) {
  cout << "Driver::AddRange " << row << " " << rhs << " " << value << endl;
}

void MpsDriver::AddBound(const std::string &row, const std::string &bound, double value, const std::string &type) {
  cout << "Driver::AddBound " << row << " " << bound << " " << value << " " << type << endl;
}

}  // namespace dlinear
