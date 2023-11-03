#include <getopt.h>
#include <gmpxx.h>

#include <chrono>
#include <fstream>
#include <future>
#include <iostream>
#include <thread>
#include <typeinfo>

#include "gauss_fp.h"
#include "gauss_np.h"
#include "gauss_pp.h"

#define EPS 1e-13

std::mutex mtx;  // mutex for critical section

template <template <class> class G, class T>
std::unique_ptr<T[]> benchmark(size_t size, size_t seed, std::ostream& output) {
  static_assert(std::is_same<T, double>::value || std::is_same<T, mpq_class>::value,
                "T must be either double or mpq_class");
  static_assert(std::is_base_of<dlinear::Gauss<T>, G<T>>::value, "G must be a subclass of Gauss<T>");
  std::unique_ptr<G<T>> gauss = std::make_unique<G<T>>(size, seed);
  mtx.lock();
  gauss->random_generate();
  mtx.unlock();

  std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
  std::unique_ptr<T[]> x{gauss->solve()};
  std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
  auto time = std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
  std::sort(x.get(), x.get() + size);

  mtx.lock();
  output << gauss->class_name() << "," << gauss->type_name() << "," << time << "," << gauss->seed() << ","
         << gauss->size() << std::endl;
  mtx.unlock();
  return x;
}

inline double get_double(const double& x) { return x; }
inline double get_double(const mpq_class& x) { return x.get_d(); }

template <class L, class R>
double average_difference(const L x[], const R y[], size_t size) {
  double sum = 0;
  for (size_t i = 0; i < size; ++i) {
    sum += std::abs(get_double(x[i]) - get_double(y[i]));
  }
  return sum / size;
}

template <class L, class R>
double abs_difference(const L x[], const R y[], size_t size) {
  double sum = 0;
  for (size_t i = 0; i < size; ++i) {
    sum += std::abs(get_double(x[i]) - get_double(y[i]));
  }
  return sum;
}

template <class L, class R>
double difference(const L x[], const R y[], size_t size) {
  double sum = 0;
  for (size_t i = 0; i < size; ++i) {
    sum += get_double(x[i]) - get_double(y[i]);
  }
  return sum;
}

/**
 * @brief Usage:
 * ./gauss [size] [seed] [output_file] [diff_file]
 */
int main(int argc, char const* argv[]) {
  size_t size = 10, seed = 42;
  const char *output_file = "gauss.csv", *diff_file = "diff.csv";
  if (argc >= 2 && std::atoi(argv[1]) > 0) {
    size = std::atoi(argv[1]);
  }
  if (argc >= 3 && std::atoi(argv[2]) > 0) {
    seed = std::atoi(argv[2]);
  }
  if (argc >= 4) {
    output_file = argv[3];
  }
  if (argc >= 5) {
    diff_file = argv[4];
  }

  std::ofstream output{output_file}, diff{diff_file};
  if (!output.is_open() || !diff.is_open()) {
    std::cerr << "Cannot open output file" << std::endl;
    return 1;
  }
  output << "solver,type,time,seed,size" << std::endl;

  auto f1 = std::async(benchmark<dlinear::GaussNP, double>, size, seed, std::ref(output));
  auto f2 = std::async(benchmark<dlinear::GaussPP, double>, size, seed, std::ref(output));
  auto f3 = std::async(benchmark<dlinear::GaussFP, double>, size, seed, std::ref(output));
  auto f4 = std::async(benchmark<dlinear::GaussNP, mpq_class>, size, seed, std::ref(output));
  auto f5 = std::async(benchmark<dlinear::GaussPP, mpq_class>, size, seed, std::ref(output));
  auto f6 = std::async(benchmark<dlinear::GaussFP, mpq_class>, size, seed, std::ref(output));

  auto x1 = f1.get();
  auto x2 = f2.get();
  auto x3 = f3.get();
  auto x4 = f4.get();
  auto x5 = f5.get();
  auto x6 = f6.get();

  diff << "solver,type,size,avg,abs,diff" << std::endl;
  diff << "GaussNP,double," << size << "," << average_difference(x1.get(), x6.get(), size) << ","
       << abs_difference(x1.get(), x6.get(), size) << "," << difference(x1.get(), x6.get(), size) << std::endl;
  diff << "GaussPP,double," << size << "," << average_difference(x2.get(), x6.get(), size) << ","
       << abs_difference(x2.get(), x6.get(), size) << "," << difference(x2.get(), x6.get(), size) << std::endl;
  diff << "GaussFP,double," << size << "," << average_difference(x3.get(), x6.get(), size) << ","
       << abs_difference(x3.get(), x6.get(), size) << "," << difference(x3.get(), x6.get(), size) << std::endl;
  diff << "GaussNP,mpq_class," << size << "," << average_difference(x4.get(), x6.get(), size) << ","
       << abs_difference(x4.get(), x6.get(), size) << "," << difference(x4.get(), x6.get(), size) << std::endl;
  diff << "GaussPP,mpq_class," << size << "," << average_difference(x5.get(), x6.get(), size) << ","
       << abs_difference(x5.get(), x6.get(), size) << "," << difference(x5.get(), x6.get(), size) << std::endl;
  diff << "GaussFP,mpq_class," << size << "," << average_difference(x6.get(), x6.get(), size) << ","
       << abs_difference(x6.get(), x6.get(), size) << "," << difference(x6.get(), x6.get(), size) << std::endl;

  return 0;
}

// 1 3 5 7 9 11 13 15 17 19 21 23 25 27 29 31 33 35 37 39 41 43 45 47 49 51 53 55 57 59 61 63 65 67 69 71 73 75 77 79 81
// 83 85 87 89 91 93 95 97 99
