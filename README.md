# Dlinear 5

## Requirements

- [g++](https://gcc.gnu.org/) and [build-essential](https://packages.ubuntu.com/bionic/build-essential)
- [Bazel](https://bazel.build/)
- [gmp](https://gmplib.org/) to compile [qsopt_ex](https://gmplib.org/) and [soplex](https://soplex.zib.de/)
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)

## TODO

- [ ] Compile qsopt_ex with bazel
- [ ] Make soplex depend on the compiled gmp withing bazel
- [ ] Remove need for gmp-dev and compile it with bazel

```bazel
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