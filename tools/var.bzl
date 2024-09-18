"""Provides a set of variables to the template engine."""

load("//tools:dlinear.bzl", "DLINEAR_AUTHOR", "DLINEAR_AUTHOR_EMAIL", "DLINEAR_DESCRIPTION", "DLINEAR_HOMEPAGE", "DLINEAR_LICENSE", "DLINEAR_NAME", "DLINEAR_SOURCE", "DLINEAR_TRACKER", "DLINEAR_VERSION")

def _make_var_substitution_impl(ctx):
    vars = dict(ctx.attr.variables)

    # Python
    py_runtime = ctx.toolchains[ctx.attr._python_toolchain].py3_runtime
    major = py_runtime.interpreter_version_info.major
    minor = py_runtime.interpreter_version_info.minor
    implementation = py_runtime.implementation_name
    if implementation == "cpython":
        tag = "cp" + str(major) + str(minor)
        vars["PYTHON_ABI_TAG"] = tag
        vars["PYTHON_TAG"] = tag
    else:
        fail("This rule only supports CPython.")

    # dlinear
    vars["DLINEAR_NAME"] = DLINEAR_NAME
    vars["DLINEAR_VERSION"] = DLINEAR_VERSION
    vars["DLINEAR_AUTHOR"] = DLINEAR_AUTHOR
    vars["DLINEAR_AUTHOR_EMAIL"] = DLINEAR_AUTHOR_EMAIL
    vars["DLINEAR_DESCRIPTION"] = DLINEAR_DESCRIPTION
    vars["DLINEAR_HOMEPAGE"] = DLINEAR_HOMEPAGE
    vars["DLINEAR_LICENSE"] = DLINEAR_LICENSE
    vars["DLINEAR_SOURCE"] = DLINEAR_SOURCE
    vars["DLINEAR_TRACKER"] = DLINEAR_TRACKER

    return [platform_common.TemplateVariableInfo(vars)]

make_var_substitution = rule(
    implementation = _make_var_substitution_impl,
    attrs = {
        "variables": attr.string_dict(),
        "_python_toolchain": attr.string(default = "@rules_python//python:toolchain_type"),
    },
    doc = """Provides a set of variables to the template engine.
Variables are passed as a dictionary of strings.
The keys are the variable names, and the values are the variable values.

It also comes with a set of default variables that are always available:
- DLINEAR_NAME: The name of the dlinear library.
- DLINEAR_VERSION: The version of the dlinear library.
- DLINEAR_AUTHOR: The author of the dlinear library.
- DLINEAR_AUTHOR_EMAIL: The author email of the dlinear library.
- DLINEAR_DESCRIPTION: The description of the dlinear library.
- DLINEAR_HOMEPAGE: The homepage of the dlinear library.
- DLINEAR_LICENSE: The license of the dlinear library.
- PYTHON_ABI_TAG: The Python ABI tag (e.g., cp36, cp311).
- PYTHON_TAG: The Python tag (e.g., cp36, cp311).

Example:
```python
make_var_substitution(
    variables = {
        "MY_VARIABLE": "my_value",
    },
)
```

This will make the variable `MY_VARIABLE` available to the template engine.
""",
    toolchains = [
        "@rules_python//python:toolchain_type",
    ],
)
