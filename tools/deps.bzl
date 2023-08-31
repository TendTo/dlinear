"""Load all dependencies for the project.
"""

load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")
load("//tools/lexyacc:lexyacc.bzl", "register_toolchain")
load("@pybind11_bazel//:python_configure.bzl", "python_configure")
load("@com_github_nelhage_rules_boost//:boost/boost.bzl", "boost_deps")
load("@rules_python//python:repositories.bzl", "py_repositories")
load("@rules_python//python:pip.bzl", "pip_parse")

# Create a central repo that knows about the dependencies needed from
# requirements_lock.txt.

def load_dependencies():
    rules_foreign_cc_dependencies()
    register_toolchain("linux")
    python_configure(
        name = "local_config_python",
        python_version = "3",
    )
    boost_deps()
    py_repositories()
    pip_parse(
        name = "pip",
        requirements_lock = "//tools:requirements.txt",
    )
