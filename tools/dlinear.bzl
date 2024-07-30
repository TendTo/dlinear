"""Based on Drake's drake.bzl file https://github.com/RobotLocomotion/drake/blob/master/tools/drake.bzl"""

load("@rules_cc//cc:defs.bzl", "cc_binary", "cc_library", "cc_test")
load("@rules_pkg//:pkg.bzl", "pkg_tar")

DLINEAR_NAME = "dlinear"
DLINEAR_VERSION = "0.0.1"

# The CXX_FLAGS will be enabled for all C++ rules in the project
# building with any compiler.
CXX_FLAGS = [
    "-std=c++20",
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

# Default defines for all C++ rules in the project.
DLINEAR_DEFINES = []

def _get_copts(rule_copts, cc_test = False):
    """Alter the provided rule specific copts, adding the platform-specific ones.

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

def _get_defines(rule_defines):
    """Alter the provided rule specific defines, adding the platform-specific ones.

    Args:
        rule_defines: The defines passed to the rule.

    Returns:
        A list of defines.
    """
    return rule_defines + DLINEAR_DEFINES + select({
        "//tools:enabled_qsoptex": ["DLINEAR_ENABLED_QSOPTEX"],
        "//conditions:default": [],
    }) + select({
        "//tools:enabled_soplex": ["DLINEAR_ENABLED_SOPLEX"],
        "//conditions:default": [],
    }) + select({
        "//tools:enabled_picosat": ["DLINEAR_ENABLED_PICOSAT"],
        "//conditions:default": [],
    }) + select({
        "//tools:enabled_cadical": ["DLINEAR_ENABLED_CADICAL"],
        "//conditions:default": [],
    })

def _get_static(rule_linkstatic):
    """Alter the provided linkstatic, by considering the platform-specific one.

    The files are linked statically by default.

    Args:
        rule_linkstatic: The linkstatic passed to the rule.

    Returns:
        The linkstatic value to use
    """
    if rule_linkstatic != None:
        return rule_linkstatic
    return select({
        "//tools:static_build": True,
        "//tools:dynamic_build": False,
        "//conditions:default": True,
    })

def _get_features(rule_features):
    """Alter the provided features, adding the platform-specific ones.

    Args:
        rule_features: The features passed to the rule.

    Returns:
        A list of features.
    """
    return rule_features + select({
        "//tools:dynamic_build": [],
        "//tools:static_build": ["fully_static_link"],
        "//conditions:default": [],
    })

def dlinear_cc_library(
        name,
        hdrs = None,
        srcs = None,
        deps = None,
        copts = [],
        linkstatic = None,
        defines = [],
        implementation_deps = [],
        **kwargs):
    """Creates a rule to declare a C++ library.

    Args:
        name: The name of the library.
        hdrs: A list of header files to compile.
        srcs: A list of source files to compile.
        deps: A list of dependencies.
        implementation_deps: A list of dependencies that are only needed for the implementation.
        copts: A list of compiler options.
        linkstatic: Whether to link statically.
        defines: A list of defines to add to the library.
        **kwargs: Additional arguments to pass to cc_library.
    """
    cc_library(
        name = name,
        hdrs = hdrs,
        srcs = srcs,
        deps = deps,
        implementation_deps = implementation_deps,
        copts = _get_copts(copts),
        linkstatic = _get_static(linkstatic),
        defines = _get_defines(defines),
        **kwargs
    )

def dlinear_cc_binary(
        name,
        srcs = None,
        deps = None,
        copts = [],
        linkstatic = None,
        defines = [],
        features = [],
        **kwargs):
    """Creates a rule to declare a C++ binary.

    Args:
        name: The name of the binary.
        srcs: A list of source files to compile.
        deps: A list of dependencies.
        copts: A list of compiler options.
        linkstatic: Whether to link statically.
        defines: A list of defines to add to the binary.
        features: A list of features to add to the binary.
        **kwargs: Additional arguments to pass to cc_binary.
    """
    cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _get_copts(copts),
        linkstatic = _get_static(linkstatic),
        defines = _get_defines(defines),
        features = _get_features(features),
        **kwargs
    )

def dlinear_cc_test(
        name,
        srcs = None,
        copts = [],
        tags = [],
        defines = [],
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
        defines: A list of defines to add to the test.
        **kwargs: Additional arguments to pass to cc_test.
    """
    if srcs == None:
        srcs = ["".join([word.capitalize() for word in name.split("_")]) + ".cpp"]
    cc_test(
        name = name,
        srcs = srcs,
        copts = _get_copts(copts, cc_test = True),
        linkstatic = True,
        tags = tags + ["dlinear", "".join([word.lower() for word in name.split("_")][1:])],
        defines = _get_defines(defines),
        **kwargs
    )

def dlinear_cc_googletest(
        name,
        srcs = None,
        deps = None,
        size = "small",
        tags = [],
        use_default_main = True,
        defines = [],
        **kwargs):
    """Creates a rule to declare a C++ unit test using googletest.

    Always adds a deps= entry for googletest main
    (@googletest//:gtest_main).

    By default, sets size="small" because that indicates a unit test.
    By default, sets use_default_main=True to use GTest's main, via @googletest//:gtest_main.
    Otherwise, it will depend on @googletest//:gtest.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .cpp.
    For example, dlinear_cc_test(name = "test_foo_bar") will look for TestFooBar.cpp.

    Args:
        name: The name of the test.
        srcs: A list of source files to compile.
        deps: A list of dependencies.
        size: The size of the test.
        tags: A list of tags to add to the test. Allows for test filtering.
        use_default_main: Whether to use googletest's main.
        defines: A list of defines to add to the test.
        **kwargs: Additional arguments to pass to dlinear_cc_test.
    """
    if deps == None:
        deps = []
    if type(deps) == "select":
        if use_default_main:
            deps += select({"//conditions:default": ["@googletest//:gtest_main"]})
        else:
            deps += select({"//conditions:default": ["@googletest//:gtest"]})
    elif use_default_main:
        deps.append("@googletest//:gtest_main")
    else:
        deps.append("@googletest//:gtest")
    dlinear_cc_test(
        name = name,
        srcs = srcs,
        deps = deps,
        size = size,
        tags = tags + ["googletest"],
        defines = _get_defines(defines),
        **kwargs
    )

def dlinear_srcs(name, srcs = None, hdrs = None, deps = [], subfolder = "", visibility = ["//visibility:public"]):
    """Returns three different lists of source files based on the name.

    Args:
        name: The name of the target. The generated targets will be called "srcs", "hdrs", "all_srcs" and "hdrs_tar".
        srcs: A list of source files include in the filegroup. If None, common c++ source files extensions will be used.
        hdrs: A list of header files to include in the filegroup. If None, common c++ header files extensions will be used.
        deps: A list of dependencies. Used for the all_srcs filegroup.
        subfolder: The subfolder to package the headers in. Can be empty.
        visibility: A list of visibility labels to apply to the filegroups.
    """
    srcs_name, hdrs_name, all_srcs_name, hdrs_tar_name = "srcs", "hdrs", "all_srcs", "hdrs_tar"
    if srcs == None:
        srcs = native.glob(["*.cpp", "*.cc", "*.cxx", "*.c"])
    if hdrs == None:
        hdrs = native.glob(["*.h", "*.hpp"])
    srcs_deps = ["%s:%s" % (dep.split(":")[0], all_srcs_name) for dep in deps]
    tar_deps = ["%s:%s" % (dep.split(":")[0], hdrs_tar_name) for dep in deps]
    native.filegroup(
        name = srcs_name,
        srcs = srcs + hdrs,
        visibility = visibility,
        tags = ["no-cpplint"],
    )
    native.filegroup(
        name = hdrs_name,
        srcs = hdrs,
        visibility = visibility,
        tags = ["no-cpplint"],
    )
    native.filegroup(
        name = all_srcs_name,
        srcs = srcs + hdrs + srcs_deps,
        visibility = visibility,
        tags = ["no-cpplint"],
    )
    pkg_tar(
        name = hdrs_tar_name,
        srcs = [":%s" % hdrs_name],
        extension = "tar.gz",
        package_dir = subfolder,
        deps = tar_deps,
        visibility = visibility,
    )
