import os
import sys
import shutil
import subprocess
from warnings import warn
from setuptools import setup
from setuptools.errors import LibError
from setuptools.command.build import build as _build
from setuptools.command.sdist import sdist as _sdist
from setuptools.command.develop import develop as _develop
from setuptools.command.bdist_egg import bdist_egg as _bdist_egg

VERSION = "4.21.06.2".replace(".0", ".")
ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR = os.path.join(ROOT_DIR)
MODULE_NAME = "pydlinear"
SO_NAME = "_{}.so".format(MODULE_NAME)


def _copy_so():
    # copy the _pydlinear.so file to the pydlinear folder
    shutil.copy(
        os.path.join(SRC_DIR, "bazel-bin", MODULE_NAME, SO_NAME),
        os.path.join(ROOT_DIR, MODULE_NAME),
    )
    os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, SO_NAME), 436)
    # copy the libqsopt_ex.so.2 file to the pydlinear folder
    shutil.copy(
        os.path.join(SRC_DIR, "bazel-bin", "external", "qsopt_ex", "libqsopt_ex", "lib", "libqsopt_ex.so.2"),
        os.path.join(ROOT_DIR, MODULE_NAME),
    )
    os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, "libqsopt_ex.so.2"), 436)


def _build_dlinear():
    """Build dlinear using bazel.
    If the build fails, check if the .so exists and prompt the user to continue.

    Returns:
        bool: True if the build failed but the user wants to continue, False otherwise.
        If true is returned, the copy step should be skipped.
    """
    new_env = os.environ.copy()
    new_env["PYTHON_BIN_PATH"] = sys.executable
    res = subprocess.call(
        [
            "bazel",
            "build",
            "//{name}:_{name}.so".format(name=MODULE_NAME),
            "--python_path={}".format(sys.executable),
            "--config",
            "pydlinear",
        ],
        env=new_env,
    )
    if res != 0:
        if SO_NAME in os.listdir(os.path.join(ROOT_DIR, MODULE_NAME)):
            warn("Bazel build failed, but found existing .so. Result may be outdated")
            return
        raise LibError(
            """Unable to build dlinear.
            Please visit https://pypi.org/project/dlinear and follow the instructions to install the prerequisites.
            Current folder: {}
            """.format(
                os.getcwd()
            )
        )
    _copy_so()


class build(_build):
    def run(self):
        self.execute(_build_dlinear, (), msg="Building dlinear")
        super().run()


class develop(_develop):
    def run(self):
        self.execute(_build_dlinear, (), msg="Building dlinear")
        super().run()


class bdist_egg(_bdist_egg):
    def run(self):
        self.run_command("build")
        super().run()


class sdist(_sdist):
    def run(self):
        self.run_command("build")
        super().run()


setup(
    cmdclass={"build": build, "develop": develop, "bdist_egg": bdist_egg, "sdist": sdist},
    package_data={MODULE_NAME: [SO_NAME, "libqsopt_ex.so.2", "_{}.pyi".format(MODULE_NAME), "py.typed"]},
)
