#include <gmpxx.h>

#include <chrono>
#include <fstream>
#include <iostream>
#include <typeinfo>

#include "gauss_fp.h"
#include "gauss_np.h"
#include "gauss_pp.h"

#define EPS 1e-13

template <class T>
std::unique_ptr<T[]> benchmark(size_t size, size_t seed, std::ostream& output, const std::string& type) {
  dlinear::GaussNP<T> gauss{size};
  gauss.random_generate();

  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  std::unique_ptr<T[]> x{gauss.solve()};
  std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count();

  std::cout << "GaussNP Time:" << time << std::endl;
  output << "GaussNP," << type << "," << time << "," << seed << "," << size << std::endl;

  dlinear::GaussPP<T> gauss2{size};
  gauss2.random_generate();

  begin = std::chrono::steady_clock::now();
  std::unique_ptr<T[]> x2{gauss2.solve()};
  end = std::chrono::steady_clock::now();
  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count();

  std::cout << "GaussPP Time:" << time << std::endl;
  output << "GaussPP," << type << "," << time << "," << seed << "," << size << std::endl;

  dlinear::GaussFP<T> gauss3{size};
  gauss3.random_generate();

  begin = std::chrono::steady_clock::now();
  std::unique_ptr<T[]> x3{gauss3.solve()};
  end = std::chrono::steady_clock::now();
  time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count();

  std::cout << "GaussFP Time:" << time << std::endl;
  output << "GaussFP," << type << "," << time << "," << seed << "," << size << std::endl;

  int diff = 0;
  std::cout << "difference between GaussNP and GaussPP: " << std::endl;
  for (size_t i = 0; i < size; ++i) {
    if (x[i] - x2[i] > EPS || x[i] - x2[i] < -EPS) {
      // std::cout << i << " ->" << x[i] - x2[i] << " " << std::endl;
      diff++;
    }
  }
  std::cout << "different res: " << diff << std::endl;

  diff = 0;
  std::cout << "difference between GaussPP and GaussFP: " << std::endl;
  for (size_t i = 0; i < size; ++i) {
    if (x2[i] - x3[i] > EPS || x2[i] - x3[i] < -EPS) {
      // std::cout << i << " ->" << x2[i] - x3[i] << " " << std::endl;
      diff++;
    }
  }
  std::cout << "different res: " << diff << std::endl;

  diff = 0;
  std::cout << "difference between GaussNP and GaussFP: " << std::endl;
  for (size_t i = 0; i < size; ++i) {
    if (x[i] - x3[i] > EPS || x[i] - x3[i] < -EPS) {
      // std::cout << i << " ->" << x[i] - x[i] << " " << std::endl;
      diff++;
    }
  }
  std::cout << "different res: " << diff << std::endl;

  return x3;
}

int main(int argc, char const* argv[]) {
  size_t size = 10, seed = 42;
  const char* output_file = "benchmark.csv";
  if (argc >= 2 && std::atoi(argv[1]) > 0) {
    size = std::atoi(argv[1]);
  }
  if (argc >= 3 && std::atoi(argv[2]) > 0) {
    seed = std::atoi(argv[2]);
  }
  if (argc >= 4) {
    output_file = argv[3];
  }

  std::ofstream output{output_file};
  output << "solver,type,time,seed,size" << std::endl;
  auto x = benchmark<double>(size, seed, output, "double");
  auto y = benchmark<mpq_class>(size, seed, output, "mpq_class");

  std::cout << "difference between GaussFP (double) and GaussFP (mpq): " << std::endl;
  size_t n_diff = 0;
  for (size_t i = 0; i < size; ++i) {
    if (x[i] - y[i].get_d() > EPS || x[i] - y[i].get_d() < -EPS) {
      // std::cout << i << " ->" << x[i] - y[i].get_d() << " " << std::endl;
      n_diff++;
    }
  }
  std::cout << "different res: " << n_diff << std::endl;

  return 0;
}
