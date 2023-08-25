# Dlinear 5?

## Requirements

- [g++](https://gcc.gnu.org/) and [build-essential](https://packages.ubuntu.com/bionic/build-essential)
- [Bazel](https://bazel.build/)
- [gmp](https://gmplib.org/) to compile [qsopt_ex](https://gmplib.org/) and [soplex](https://soplex.zib.de/)
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)
- [flex](https://github.com/westes/flex) and [bison](https://www.gnu.org/software/bison/) to produce the parser
  for `.smt2` files

## TODO

### Refactor

- [ ] Port the whole dlinear4
- [ ] Add tests
- [ ] Add benchmark
- [ ] Add python bindings
- [ ] Add documentation
- [ ] Add examples
- [ ] Add CI

### Compile-side

- [ ] Remove need for gmp-dev by compiling it with bazel
- [ ] Make soplex and qsopt_ex depend on the compiled gmp withing bazel
- [ ] Compile flex and bison with bazel

### Useful commands

```bash
# Compile dlinear
bazel build //dlinear
```

```bash
# CPPlint
bazel test //dlinear/...
```

```bash
# Run tests
bazel test //test/...
```

### Compilation flags

- `--//tools:enable_soplex=[True|False]` to enable or disable soplex. Default is `True`
- `--//tools:enable_qsoptex=[True|False]` to enable or disable qsopt_ex. Default is `True`

## MWP

```c++
// dlinear/test.cpp
#include
<iostream>
#include
"dlinear/util/logging.h"
#include
"dlinear/libs/gmp.h"
#include
"dlinear/libs/soplex.h"
#include
"dlinear/libs/qsopt_ex.h"

using namespace soplex;

void test_rational() {
SoPlex mysoplex;

/* set the objective sense */
mysoplex.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MINIMIZE);

/* we first add variables */
DSVector dummycol(0);
mysoplex.addColReal(LPCol(3.0, dummycol, infinity, 1.0));
mysoplex.addColReal(LPCol(2.0, dummycol, infinity, 1.0));

/* then constraints one by one */
DSVector row1(2);
row1.add(0, 0.2);
row1.add(1, 1.0);
mysoplex.addRowReal(LPRow(2.0, row1, infinity));

/* solve LP */
SPxSolver::Status stat;
DVector prim(2);
DVector dual(1);
stat = mysoplex.optimize();

/* get solution */
if (stat == SPxSolver::OPTIMAL) {
mysoplex.getPrimal(prim);
mysoplex.getDual(dual);
std::cout << "LP solved to optimality.\n";
std::cout << "Objective value is " << mysoplex.objValueReal() << ".\n";
std::cout << "Primal solution is [" << prim[0] << ", " << prim[1] << "].\n";
std::cout << "Dual solution is [" << dual[0] << "].\n";
} else {
std::cout << "Error: SoPlex returned with status " << stat << ".\n";
}
}

int main([[maybe_unused]]int argc,[[maybe_unused]] const char **argv) {
DLINEAR_LOG_INIT_LEVEL(DLINEAR_VERBOSITY_TO_LOG_LEVEL(5));
DLINEAR_TRACE("Start qsopt_ex");
dlinear::qsopt_ex::QSXStart();
dlinear::qsopt_ex::QSXFinish();
DLINEAR_TRACE("Finish qsopt_ex");

DLINEAR_TRACE("Start soplex");
test_rational();
DLINEAR_TRACE("Finish soplex");

DLINEAR_TRACE("Start gmp");
mpq_class a{ 1 }, b{ 2 };
mpq_class c = a + b;
std::cout << c << std::endl;
DLINEAR_TRACE("Finish gmp");
return 0;
}
```

```bazel
# dlinear/BUILD
dlinear_cc_binary(
    name = "test",
    srcs = ["test.cpp"],
    features = ["fully_static_link"],
    linkstatic = 1,
    deps = [
    "//dlinear/libs:gmp",
    "//dlinear/libs:qsopt_ex",
    "//dlinear/libs:soplex",
    ],
)
```