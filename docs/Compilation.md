# Compilation

## Configurations

Configurations are used to specify the build type, as they usually group a set of flags.
The following configurations are available:

- `--config=debug` for a debug build
- `--config=opt` for an optimized build
- `--config=bench` for an optimized build without logging and using full static linking
- `--config=pydlinear` to build the python bindings
- `--config=iwyu` to run the include-what-you-use check
- `--config=dwyu` to run the depend-on-what-you-use check

### Low-level compilation flags

It not advisable to use these flags directly, as the configurations already group them in a predefined way.
But if you need more control when compiling, the following flags are supported:

- `--enable_static_build` to use fully static linking between all the submodules and the binary. Default is `False`
- `--enable_dynamic_build` to use dynamic linking between all the submodules and the binary. Default is `False`
- `--enable_pydlinear_build` to build the python bindings. Default is `False`
- `--enable_fpic_build` to enable position independent code. Default is `False`
- `--enable_threads_build` to enable thread safe operations. Default is `False`
- `--static_boost` build boost statically. Default is `True`
- `--enable_qsoptex` to include the QSOptEx LP solver. Default is `True`
- `--enable_soplex` to include the SoPlex LP solver. Default is `True`
- `--enable_picosat` to include the PicoSAT SAT solver. Default is `True`
- `--enable_cadical` to include the Cadical SAT solver. Default is `True`

## DWYU

Depend on What You Use (DWYU) is an aspect of the Bazel build that checks the dependencies of a target and only includes the necessary ones, also distinguishing between implementation dependencies, which are not propagated, and standard dependencies which are.  
To run the check, use the following command:

```bash
bazel build --config=dwyu //dlinear
```
