"""Based on Drake's drake.bzl file https://github.com/RobotLocomotion/drake/blob/master/tools/drake.bzl"""

load("@rules_python//python:defs.bzl", "py_test")

DLINEAR_NAME = "dlinear"
DLINEAR_VERSION = "0.0.1"

# The CXX_FLAGS will be enabled for all C++ rules in the project
# building with any compiler.
CXX_FLAGS = [
    "-std=c++17",
    "-Wall",
    "-Wattributes",
    "-Wdeprecated",
    "-Wdeprecated-declarations",
    "-Wextra",
    "-Wignored-qualifiers",
    "-Wold-style-cast",
    "-Woverloaded-virtual",
    "-Wpedantic",
    "-Wshadow",
    "-Werror",
]

# The CLANG_FLAGS will be enabled for all C++ rules in the project when
# building with clang.
CLANG_FLAGS = CXX_FLAGS + [
    "-Wabsolute-value",
    "-Winconsistent-missing-override",
    "-Wnon-virtual-dtor",
    "-Wreturn-stack-address",
    "-Wsign-compare",
]

# The GCC_FLAGS will be enabled for all C++ rules in the project when
# building with gcc.
GCC_FLAGS = CXX_FLAGS + [
    "-Wlogical-op",
    "-Wnon-virtual-dtor",
    "-Wreturn-local-addr",
    "-Wunused-but-set-parameter",
]

# The GCC_CC_TEST_FLAGS will be enabled for all cc_test rules in the project
# when building with gcc.
GCC_CC_TEST_FLAGS = []

def _get_copts(rule_copts, cc_test = False):
    """Returns both the rule_copts, and platform-specific copts.

    When cc_test is True, the GCC_CC_TEST_FLAGS will be added.
    It should only be set on cc_test rules or rules that are boil down to cc_test rules.

    Args:
        rule_copts: The copts passed to the rule.
        cc_test: Whether the rule is a cc_test rule.

    Returns:
        A list of copts.
    """
    extra_gcc_flags = GCC_CC_TEST_FLAGS if cc_test else []
    return select({
        "//tools:gcc_build": GCC_FLAGS + extra_gcc_flags + rule_copts,
        "//tools:clang_build": CLANG_FLAGS + rule_copts,
        "//conditions:default": CXX_FLAGS + rule_copts,
    })

def dlinear_cc_library(
        name,
        hdrs = None,
        srcs = None,
        deps = None,
        copts = [],
        linkstatic = True,
        **kwargs):
    """Creates a rule to declare a C++ library.
    """
    native.cc_library(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        copts = _get_copts(copts),
        linkstatic = linkstatic,
        **kwargs
    )

def dlinear_cc_binary(
        name,
        srcs = None,
        deps = None,
        copts = [],
        **kwargs):
    """Creates a rule to declare a C++ binary.
    """
    native.cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _get_copts(copts),
        **kwargs
    )

def dlinear_cc_test(
        name,
        srcs = None,
        copts = [],
        tags = [],
        **kwargs):
    """Creates a rule to declare a C++ unit test.

    Note that for almost all cases, dlinear_cc_googletest should be used instead of this rule.

    By default, sets size="small" because that indicates a unit test.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .cpp.
    For example, dlinear_cc_test(name = "test_foo_bar") will look for TestFooBar.cpp.

    Args:
        name: The name of the test.
        srcs: A list of source files to compile.
        copts: A list of compiler options.
        tags: A list of tags to add to the test. Allows for test filtering.
        **kwargs: Additional arguments to pass to native.cc_test.
    """
    if srcs == None:
        srcs = ["".join([word.capitalize() for word in name.split("_")]) + ".cpp"]
    native.cc_test(
        name = name,
        srcs = srcs,
        copts = _get_copts(copts, cc_test = True),
        tags = tags + ["dlinear"],
        **kwargs
    )

def dlinear_cc_googletest(
        name,
        srcs = None,
        deps = None,
        size = "small",
        tags = [],
        use_default_main = True,
        **kwargs):
    """Creates a rule to declare a C++ unit test using googletest.

    Always adds a deps= entry for googletest main
    (@com_google_googletest//:gtest_main).

    By default, sets size="small" because that indicates a unit test.
    By default, sets use_default_main=True to use GTest's main, via @com_google_googletest//:gtest_main.
    Otherwise, it will depend on @com_google_googlegtest//:gtest.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .cpp.
    For example, dlinear_cc_test(name = "test_foo_bar") will look for TestFooBar.cpp.

    Args:
        name: The name of the test.
        srcs: A list of source files to compile.
        deps: A list of dependencies.
        size: The size of the test.
        tags: A list of tags to add to the test. Allows for test filtering.
        use_default_main: Whether to use googletest's main.
        **kwargs: Additional arguments to pass to dlinear_cc_test.
    """
    if deps == None:
        deps = []
    if use_default_main:
        deps.append("@com_google_googletest//:gtest_main")
    else:
        deps.append("@com_google_googletest//:gtest")
    dlinear_cc_test(
        name = name,
        srcs = srcs,
        deps = deps,
        size = size,
        tags = tags + ["googletest"],
        **kwargs
    )

def solver_phased_test(
        name,
        phase,
        suffix = "smt2",
        options = [],
        tags = [],
        lp_solver = "qsoptex",
        continuous = False,
        exhaustive_ok = True,
        main = "TestSolver.py",
        **kwargs):
    """Create solver test.

    The SMT solver will parse the input file and produce an output.
    If the output is the same as the one in the corresponding .expected file, the test passes.

    Args:
        name: The name of the test.
        phase: The phase to use. Must be either 1 or 2.
        suffix: The suffix of the input file.
        options: A list of options to pass to the solver.
        tags: A list of tags to add to the test.
        lp_solver: The LP solver to use. Must be either soplex or qsoptex.
        continuous: Whether to run the solver in continuous mode.
        exhaustive_ok: Whether to run the solver in exhaustive mode.
        main: The main Python file to use.
        **kwargs: Additional arguments to pass to native.py_test.
    """
    if lp_solver not in ("soplex", "qsoptex"):
        fail("LP solver must be soplex or qsoptex", "lp_solver")
    if phase not in (1, 2):
        fail("Phase must be 1 or 2", "phase")

    input_file = "%s.%s" % (name, suffix)
    data_files = native.glob([name + "*"])
    name_extra = "_continuous" if continuous else ""

    py_test(
        name = "{}_{}_{}_phase_{}{}".format(name, suffix, lp_solver, phase, name_extra),
        args = [
            "$(location //test/solver:test_solver_binary)",
            "$(location %s)" % input_file,
            lp_solver,
            str(phase),
            ("C" if continuous else "X") if exhaustive_ok else "N",
        ] + options,
        tags = tags + ["solver", suffix],
        data = ["//test/solver:test_solver_binary"] + data_files,
        main = main,
        srcs = [main],
        srcs_version = "PY3",
        **kwargs
    )

def solver_test(name, suffix = "smt2", options = [], lp_solvers = None, size = "small", **kwargs):
    """Tests the solver over an file.

    It automatically tests both phases, and both LP solvers on the same input.
    If the lp solver is qsoptex, it also tests continuous mode.

    Args:
        name: The name of the test. It will be used to find the input file.
        suffix: The suffix of the input file.
        options: A list of options to pass to the solver.
        lp_solvers: A list of LP solvers to test. If None, tests both soplex and qsoptex.
        size: The size of the test. Defaults to "small".
        **kwargs: Additional arguments to pass to solver_test.
    """
    for lp_solver in ("soplex", "qsoptex") if lp_solvers == None else lp_solvers:
        for phase in (1, 2):
            solver_phased_test(
                name,
                lp_solver = lp_solver,
                suffix = suffix,
                phase = phase,
                options = options,
                size = size,
                **kwargs
            )

    # Continuous tests are only supported for qsoptex.
    if lp_solvers == None or "qsoptex" in lp_solvers:
        for phase in (1, 2):
            solver_phased_test(
                name,
                lp_solver = "qsoptex",
                suffix = suffix,
                phase = phase,
                options = options,
                continuous = True,
                size = size,
                **kwargs
            )

def solver_test_all(files_dir = "files", options = [], lp_solvers = None, **kwargs):
    """Tests all input files from the provided directories.

    Loops over all files in the directory and calls smt2_test on each .smt2 file.
    Then, loops over all files in the directory and calls mps_test on each .mps file.

    Args:
        files_dir: The directory containing the input files.
        options: A list of options to pass to the solver.
        lp_solvers: A list of LP solvers to test. If None, tests both soplex and qsoptex.
        **kwargs: Additional arguments to pass to the test.
    """
    files = native.glob(["%s/*.smt2" % files_dir])
    for file in files:
        solver_test(
            name = file.removesuffix(".smt2"),
            options = options,
            lp_solvers = lp_solvers,
            suffix = "smt2",
            **kwargs
        )
    files = native.glob(["%s/*.mps" % files_dir])
    for file in files:
        solver_test(
            name = file.removesuffix(".mps"),
            options = options,
            lp_solvers = lp_solvers,
            suffix = "mps",
            **kwargs
        )
