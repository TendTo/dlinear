"""Macro with some preconfigurations for testing with pytest."""

load("@pypi//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_test")

def pytest_test(name, srcs, deps = [], args = [], **kwargs):
    """Call pytest from a py_test rule, taking care of the common arguments and dependencies.

    Args:
        name: The name of the rule.
        srcs: The source files to test.
        deps: The dependencies of the rule.
        args: The arguments to pass to pytest.
        **kwargs: Additional arguments to pass to py_test.
    """
    py_test(
        name = name,
        srcs = ["//tools:pytest_main.py"] + srcs,
        main = "//tools:pytest_main.py",
        args = ["--capture=no"] + args + ["$(location :%s)" % x for x in srcs],
        python_version = "PY3",
        srcs_version = "PY3",
        deps = deps + [requirement("pytest")],
        **kwargs
    )

def pydlinear_py_test(name, srcs = None, deps = [], args = [], data = [], size = "small", tags = [], **kwargs):
    """Call pytest from a py_test rule, taking care of the common arguments and dependencies.

    By default, sets size="small" because that indicates a unit test.
    If a list of srcs is not provided, it will be inferred from the name, by capitalizing each _-separated word and appending .py.
    For example, pydlinear_py_test(name = "test_foo_bar") will look for TestFooBar.py.

    Args:
        name: The name of the rule.
        srcs: The source files to test.
        deps: The dependencies of the rule.
        args: The arguments to pass to pytest.
        data: The data dependencies of the rule.
        size: The size of the test.
        tags: The tags to apply to the test. Ease of use for filtering tests.
        **kwargs: Additional arguments to pass to py_test.
    """
    if srcs == None:
        srcs = ["".join([word.capitalize() for word in name.split("_")]) + ".py"]
    pytest_test(
        name = name,
        srcs = srcs,
        args = args,
        deps = deps + ["//pydlinear"],
        data = data,
        size = size,
        tags = tags + ["pydlinear"],
        **kwargs
    )
