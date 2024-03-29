#include <getopt.h>
#include <gmpxx.h>

#include <chrono>
#include <fstream>
#include <iostream>

#include "gauss_fp.h"
#include "gauss_np.h"
#include "gauss_pp.h"

#define PRECISION 128
#define PRECISION_STR #PRECISION

template <template <class> class G, class T>
class GaussBenchmark {
 public:
  GaussBenchmark(std::ostream& timing_, std::ostream& diff, size_t size, size_t seed)
      : timing_{timing_}, diff_{diff}, gauss_{std::move(std::make_unique<G<T>>(size, seed))}, x_{} {
    static_assert(std::is_base_of<dlinear::Gauss<T>, G<T>>(), "G must be a subclass of Gauss<T>");
    static_assert(std::is_same<T, double>() || std::is_same<T, mpq_class>() || std::is_same<T, mpf_class>(),
                  "T must be either double or mpq_class / mpf_class");
  }

  void benchmark() {
    gauss_->random_generate();

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    x_ = std::move(gauss_->solve());
    std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
    auto time = std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

    timing_ << gauss_->class_name() << "," << gauss_->type_name() << "," << time << "," << gauss_->seed() << ","
            << gauss_->size() << "," << mpf_get_default_prec() << std::endl;
  }

  mpf_class abs(const mpf_class& x) const { return x < 0 ? -x : x; }

  template <template <class> class O, class OT>
  mpf_class diff(const GaussBenchmark<O, OT>& o) const {
    ensure_same_size(o);
    mpf_class sum = 0;
    for (size_t i = 0; i < gauss_->size(); ++i) {
      sum += mpf_class{x_[i]} - mpf_class{o.x()[i]};
    }
    return sum;
  }

  template <template <class> class O, class OT>
  mpf_class asb_diff(const GaussBenchmark<O, OT>& o) const {
    ensure_same_size(o);
    mpf_class sum = 0;
    for (size_t i = 0; i < gauss_->size(); ++i) {
      sum += abs(mpf_class{x_[i]} - mpf_class{o.x()[i]});
    }
    return sum;
  }

  template <template <class> class O, class OT>
  mpf_class abs_mean(const GaussBenchmark<O, OT>& o) const {
    ensure_same_size(o);
    mpf_class sum = 0;
    for (size_t i = 0; i < gauss_->size(); ++i) {
      sum += abs(mpf_class(mpf_class{x_[i]} - mpf_class{o.x()[i]}));
    }
    return sum / gauss_->size();
  }

  template <template <class> class O, class OT>
  void print_compare_to_baseline(const GaussBenchmark<O, OT>& baseline) const {
    ensure_same_size(baseline);
    diff_ << gauss_->class_name() << "," << gauss_->type_name() << "," << gauss_->size() << "," << abs_mean(baseline)
          << "," << asb_diff(baseline) << "," << diff(baseline) << "," << mpf_get_default_prec() << std::endl;
  }

  inline const std::unique_ptr<T[]>& x() const { return x_; }
  inline size_t size() const { return gauss_->size(); }

 private:
  template <template <class> class O, class OT>
  void ensure_same_size(const GaussBenchmark<O, OT>& o) const {
    if (gauss_->size() != o.size()) throw std::runtime_error("Cannot compare different sizes");
  }

  std::ostream& timing_;
  std::ostream& diff_;
  std::unique_ptr<G<T>> gauss_;
  std::unique_ptr<T[]> x_;
};

/**
 * Usage:
 * ./gauss [size] [seed] [output_file] [diff_file]
 */
int main(int argc, char const* argv[]) {
  size_t size = 10, seed = 42;
  const char *output_file = "time.csv", *diff_file = "diff.csv";
  mpf_set_default_prec(PRECISION);

  int opt;
  while ((opt = getopt(argc, const_cast<char* const*>(argv), "d:t:p:s:r:h")) != -1) {
    switch (opt) {
      case 's':
        size = std::atoi(optarg);
        break;
      case 'r':
        seed = std::atoi(optarg);
        break;
      case 't':
        output_file = optarg;
        break;
      case 'd':
        diff_file = optarg;
        break;
      case 'p':
        mpf_set_default_prec(std::atoi(optarg));
        break;
      case 'h':
      default:
        std::cerr << "Usage: " << argv[0] << " [-n|--number SIZE] [-E|--show-ends SEED] [output_file] [diff_file]"
                  << std::endl;
        return 1;
    }
  }

  std::ofstream output{output_file}, diff{diff_file};
  if (!output.is_open() || !diff.is_open()) {
    std::cerr << "Cannot open output file" << std::endl;
    return 1;
  }
  output << "solver,type,time,seed,size,precision" << std::endl;
  diff << "solver,type,size,avg,abs,diff,precision" << std::endl;

  GaussBenchmark<dlinear::GaussNP, double> g1{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussPP, double> g2{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussFP, double> g3{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussNP, mpf_class> g4{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussPP, mpf_class> g5{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussFP, mpf_class> g6{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussNP, mpq_class> g7{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussPP, mpq_class> g8{output, diff, size, seed};
  GaussBenchmark<dlinear::GaussFP, mpq_class> g9{output, diff, size, seed};

  g1.benchmark();
  g2.benchmark();
  g3.benchmark();
  g4.benchmark();
  g5.benchmark();
  g6.benchmark();
  g7.benchmark();
  g8.benchmark();
  g9.benchmark();

  g1.print_compare_to_baseline(g9);
  g2.print_compare_to_baseline(g9);
  g3.print_compare_to_baseline(g9);
  g4.print_compare_to_baseline(g9);
  g5.print_compare_to_baseline(g9);
  g6.print_compare_to_baseline(g9);
  g7.print_compare_to_baseline(g9);
  g8.print_compare_to_baseline(g9);
  g9.print_compare_to_baseline(g9);

  return 0;
}
