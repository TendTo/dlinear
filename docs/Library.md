# Library

`dlinear` comes with a shared C++ library that can be used to interact with the solver programmatically.  
See the [Installation](./Installation.md) page for instructions on how to install the library.

## Linking

When including the shared library in a project, you can include the main dlinear header

```cpp
/** @file <my_file>.cpp */
#include <dlinear/dlinear.h>
```

and link the library with the flags `-ldlinear`. Add the `-lgmp` flag if your project needs to manipulate rational numbers.

```bash
g++ -std=c++20 <my_file>.cpp -ldlinear -o <out_file>
```

Finally, the executable can be run with

```bash
./<out_file>
```

## Example

The following example demonstrates how to use the library to check the satisfiability of a problem in SMT2 format:

```cpp
/** @file test.cpp */
#include <dlinear/solver/SmtSolver.h>

#include <iostream>

int main() {
  dlinear::SmtSolver solver;
  solver.Parse("input.smt2");
}
```

The example can be compiled with

```bash
g++ -std=c++20 test.cpp -ldlinear -o test
```

and run with

```bash
./test
```

## Troubleshooting

### Missing `-lgmp` flag

If compiling the example results in an error similar to

```bash
/usr/bin/ld: /tmp/cc7JxRt4.o: undefined reference to symbol '__gmpq_clear'
/usr/bin/ld: /lib/x86_64-linux-gnu/libgmp.so.10: error adding symbols: DSO missing from command line
```

it is probably because you are either missing the `-lgmp` flag or the library is not installed on your system.

### Missmatch `fmt` of `spdlog` library version

If compiling the example results in an error similar to

```bash
/usr/include/dlinear/libs/libgmp.h:244:1: error: expected class-name before ‘{’ token
  244 | OSTREAM_FORMATTER(mpq_class)
```

or

```bash
/usr/include/spdlog/common.h:127:111: error: ‘basic_runtime’ is not a member of ‘fmt’
  127 |           std::is_convertible<T, fmt::basic_string_view<Char>>::value || std::is_same<remove_cvref_t<T>, fmt::basic_runtime<Char>>::value>
```

it is probably because the version of the `fmt` and `spdlog` libraries respectively are not compatible with the one used in `dlinear`.
If you can't update the installed ones, it should be sufficient to download the header files from the [fmt](http://github.com/fmtlib/fmt) or [spdlog](https://github.com/gabime/spdlog) repositories and include them in the project.

For example, the project structure could look like this:

```bash
├── include # Create a directory for the external headers
│   ├── fmt # fmt headers
│   └── spdlog # spdlog headers
└── test.cpp
```

and the compilation command would look like this:

```bash
g++ -std=c++20 test.cpp -Iinclude -lgmp -ldlinear -o test -DSPDLOG_FMT_EXTERNAL -DSPDLOG_COMPILED_LIB
```

### Missing `SPDLOG_FMT_EXTERNAL` or `SPDLOG_COMPILED_LIB` macros

If compiling the example results in an error similar to

```bash
temp/spdlog/fmt/bundled/core.h:281:30: error: redefinition of ‘struct fmt::v10::type_identity<T>’
  281 | template <typename T> struct type_identity {
```

it is probably because the `SPDLOG_FMT_EXTERNAL` or `SPDLOG_COMPILED_LIB` macros are missing.
Make sure to define them before including the `dlinear` header or in the compilation command.
