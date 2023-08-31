load("@rules_python//python:defs.bzl", "py_test")
load("@pip//:requirements.bzl", "requirement")

def pytest_test(name, srcs, deps = [], args = [], data = [], **kwargs):
    """Call pytest from a py_test rule, taking care of the common arguments and dependencies.

    Args:
        name: The name of the rule.
        srcs: The source files to test.
        deps: The dependencies of the rule.
        args: The arguments to pass to pytest.
        data: The data dependencies of the rule.
        kwargs: Additional arguments to pass to py_test.
    """
    py_test(
        name = name,
        srcs = ["//tools:pytest_main.py"] + srcs,
        main = "//tools:pytest_main.py",
        args = ["--capture=no"] + args + ["$(location :%s)" % x for x in srcs],
        python_version = "PY3",
        srcs_version = "PY3",
        deps = deps + [requirement("pytest")],
        data = data,
        **kwargs
    )
