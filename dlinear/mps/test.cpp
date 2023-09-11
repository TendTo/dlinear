#include "dlinear/mps/Driver.h"

int main(int, char const *[]) {
  dlinear::MpsDriver driver;
  std::cout << "Hello, world!" << std::endl;
  return driver.parse_file("/home/tend/Programming/tesi/dlinear5/test2.mps");
}
