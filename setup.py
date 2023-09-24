import os
import shutil
import subprocess
from warnings import warn
from setuptools import setup
from setuptools.errors import LibError
from setuptools.command.build import build as _build
from setuptools.command.sdist import sdist as _sdist
from setuptools.command.develop import develop as _develop
from setuptools.command.bdist_egg import bdist_egg as _bdist_egg

ROOT_DIR = os.path.abspath(os.path.dirname(__file__))
SRC_DIR = os.path.join(ROOT_DIR)
MODULE_NAME = "pydlinear"
SO_NAME = "_{}.so".format(MODULE_NAME)
LIBRARIES = (
    "libexternal_Sboost_Slibatomic_Usse.so",
    "libexternal_Sboost_Slibatomic.so",
    "libexternal_Sboost_Slibchrono.so",
    "libexternal_Sboost_Slibcontainer.so",
    "libexternal_Sboost_Slibexception.so",
    "libexternal_Sboost_Slibregex.so",
    "libexternal_Sboost_Slibsystem.so",
    "libexternal_Spicosat_Slibpicosat.so",
)


def _copy_so():
    # copy the _pydlinear.so file to the pydlinear folder
    shutil.copyfile(
        os.path.join(SRC_DIR, "bazel-bin", MODULE_NAME, SO_NAME),
        os.path.join(ROOT_DIR, MODULE_NAME, SO_NAME),
    )
    os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, SO_NAME), 436)
    # copy the libqsopt_ex.so.2 file to the pydlinear folder
    shutil.copyfile(
        os.path.join(SRC_DIR, "bazel-bin", "external", "qsopt_ex", "libqsopt_ex", "lib", "libqsopt_ex.so.2"),
        os.path.join(ROOT_DIR, MODULE_NAME, "libqsopt_ex.so.2"),
    )
    os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, "libqsopt_ex.so.2"), 436)
    # copy the libsoplexshared.so.6.0 file to the pydlinear folder
    shutil.copyfile(
        os.path.join(SRC_DIR, "bazel-bin", "external", "soplex", "libsoplex", "lib", "libsoplexshared.so.6.0"),
        os.path.join(ROOT_DIR, MODULE_NAME, "libsoplexshared.so.6.0"),
    )
    os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, "libsoplexshared.so.6.0"), 436)
    # copy all the shared libraries to the pydlinear folder
    for library in LIBRARIES:
        shutil.copyfile(
            os.path.join(SRC_DIR, "bazel-bin", "_solib_k8", library),
            os.path.join(ROOT_DIR, MODULE_NAME, library),
        )
        os.chmod(os.path.join(ROOT_DIR, MODULE_NAME, library), 436)


def _build_dlinear():
    """Build dlinear using bazel.
    If the build fails, check if the .so exists and prompt the user to continue.

    Returns:
        bool: True if the build failed but the user wants to continue, False otherwise.
        If true is returned, the copy step should be skipped.
    """
    res = subprocess.call(
        [
            "bazel",
            "build",
            "//{name}:_{name}.so".format(name=MODULE_NAME),
            "--config",
            "pydlinear",
        ],
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
    package_data={
        MODULE_NAME: [SO_NAME, "libqsopt_ex.so.2", "libsoplexshared.so.6.0", "__init__.pyi", "py.typed", *LIBRARIES]
    },
)
