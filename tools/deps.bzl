"""Load all dependencies for the project."""

load("//tools/lexyacc:lexyacc.bzl", "register_toolchain")

# Create a central repo that knows about the dependencies needed from
# requirements_lock.txt.

def load_dependencies(name):
    """Load all dependencies for the project.

    Args:
        name: Unused.
    """
    register_toolchain("linux")
