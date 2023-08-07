# Based on Drake's drake.bzl file,
# https://github.com/RobotLocomotion/drake/blob/master/tools/drake.bzl.
DLINEAR_NAME = "dlinear"
DLINEAR_VERSION = "0.0.1-dev"

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
    "-DDLINEAR_VERSION='\"%s\"'" % DLINEAR_VERSION,
    "-DDLINEAR_NAME='\"%s\"'" % DLINEAR_NAME,
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
        linkstatic = 1,
        alwayslink = 1,
        **kwargs):
    """Creates a rule to declare a C++ library.
    """
    native.cc_library(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        linkstatic = linkstatic,
        alwayslink = alwayslink,
        copts = _get_copts(copts),
        **kwargs
    )

def dlinear_cc_binary(
        name,
        srcs = None,
        deps = None,
        copts = [],
        testonly = False,
        **kwargs):
    """Creates a rule to declare a C++ binary.
    """
    native.cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _get_copts(copts),
        testonly = testonly,
        **kwargs
    )

def dlinear_cc_test(
        name,
        size = None,
        srcs = None,
        copts = [],
        **kwargs):
    """Creates a rule to declare a C++ unit test.

    Note that for almost all cases, dlinear_cc_googletest should be used instead of this rule.

    By default, sets size="small" because that indicates a unit test.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .cpp.
    For example, dlinear_cc_test(name = "test_foo_bar") will look for TestFooBar.cpp.
    """
    if size == None:
        size = "small"
    if srcs == None:
        srcs = [word.capitalize() for word in name.split("_")]
        srcs = ["".join(srcs) + ".cpp"]
    native.cc_test(
        name = name,
        size = size,
        srcs = srcs,
        copts = _get_copts(copts, cc_test = True),
        **kwargs
    )

def dlinear_cc_googletest(
        name,
        srcs = None,
        deps = None,
        use_default_main = True,
        **kwargs):
    """Creates a rule to declare a C++ unit test using googletest.

    Always adds a deps= entry for googletest main
    (@com_google_googletest//:gtest_main).

    By default, sets size="small" because that indicates a unit test.
    By default, sets use_default_main=True to use GTest's main, via
    @com_google_googletest//:gtest_main. Otherwise, it will depend on
    @com_google_googlegtest//:gtest.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .cpp.
    For example, dlinear_cc_test(name = "test_foo_bar") will look for TestFooBar.cpp.
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
        **kwargs
    )
