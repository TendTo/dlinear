"""Install script for setuptools."""

import os
import shutil
import sysconfig
import subprocess
import glob

import setuptools
from setuptools.command import build_ext
import setuptools.errors

PACKAGE_NAME = "pydlinear"


class GlobalVariables:
    def __init__(self):
        self.DLINEAR_VERSION = ""
        self.DLINEAR_DESCRIPTION = ""
        self.DLINEAR_AUTHOR = ""
        self.DLINEAR_AUTHOR_EMAIL = ""
        self.DLINEAR_HOMEPAGE = ""
        self.DLINEAR_LICENSE = ""

        with open("tools/dlinear.bzl", encoding="utf-8") as f:
            lines = f.readlines()
        reading_global_variables = False
        for line in lines:
            if line.strip() == ("# GLOBAL VARIABLES"):
                reading_global_variables = True
                continue
            if line.strip() == ("# END GLOBAL VARIABLES"):
                break
            if reading_global_variables:
                key, value = line.strip().split(" = ")
                setattr(self, key.strip(), value.strip().strip('"'))


class BazelExtension(setuptools.Extension):
    """A C/C++ extension that is defined as a Bazel BUILD target."""

    def __init__(self, ext_name, bazel_target):
        self.bazel_target = bazel_target
        folders = ("dlinear", "pydlinear", "tools", "third_party")
        files = []
        for folder in folders:
            files += glob.glob(f"{folder}/**/*", recursive=True)
        files += ["BUILD.bazel", "MODULE.bazel", ".bazelrc", ".bazelignore", ".bazelversion"]
        src_files = list(filter(lambda x: not x.endswith(".py"), files))
        setuptools.Extension.__init__(self, ext_name, sources=src_files)


def get_bazel_target_args(command):
    if command == "build":
        return ["bazel", "build", "--config=pydlinear", "--python_version=" + sysconfig.get_python_version()]
    if command == "cquery":
        return [
            "bazel",
            "cquery",
            "--output=files",
            "--config=pydlinear",
            "--python_version=" + sysconfig.get_python_version(),
        ]


class BuildBazelExtension(build_ext.build_ext):
    """A command that runs Bazel to build a C/C++ extension."""

    def run(self):
        for ext in self.extensions:
            self.bazel_build(ext)
        build_ext.build_ext.run(self)

    def bazel_build(self, ext):
        if shutil.which("bazel") is None:
            raise setuptools.errors.CompileError(
                "Bazel not found (https://bazel.build/). It is required to install this package from source."
            )

        bazel_argv = [*get_bazel_target_args("build"), ext.bazel_target]
        self.spawn(bazel_argv)
        path = subprocess.check_output([*get_bazel_target_args("cquery"), ext.bazel_target]).decode("utf-8").strip()

        ext_dest_path = self.get_ext_fullpath(ext.name)
        ext_dest_dir = os.path.dirname(ext_dest_path)
        os.makedirs(ext_dest_dir, exist_ok=True)
        shutil.copyfile(path, ext_dest_path)

        # Add python stubs for type checking
        bazel_argv = [*get_bazel_target_args("build"), "//pydlinear:stubgen"]
        self.spawn(bazel_argv)
        paths = (
            subprocess.check_output([*get_bazel_target_args("cquery"), "//pydlinear:stubgen"])
            .decode("utf-8")
            .strip()
            .split("\n")
        )
        for path in paths:
            file = os.path.basename(path)
            ext_dest_dir = os.path.dirname(self.get_ext_fullpath(ext.name))
            os.makedirs(ext_dest_dir, exist_ok=True)
            shutil.copyfile(path, os.path.join(ext_dest_dir, file))


config_vars = GlobalVariables()
setuptools.setup(
    name=PACKAGE_NAME,
    version=config_vars.DLINEAR_VERSION,
    description=config_vars.DLINEAR_DESCRIPTION,
    author=config_vars.DLINEAR_AUTHOR,
    author_email=config_vars.DLINEAR_AUTHOR_EMAIL,
    url=config_vars.DLINEAR_HOMEPAGE,
    license=config_vars.DLINEAR_LICENSE,
    keywords=["smt", "delta-complete", "qf_lra", "neural network"],
    entry_points={"console_scripts": ["pydlinear=pydlinear.__main__:main"]},
    classifiers=[
        "Development Status :: 1 - Planning",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: BSD License",
        "Operating System :: POSIX :: Linux",
        "Programming Language :: C++",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.6",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Topic :: Software Development :: Libraries :: Python Modules",
    ],
    long_description=open("README.md", encoding="utf-8").read(),
    long_description_content_type="text/markdown",
    ext_modules=[BazelExtension("pydlinear._pydlinear", "//pydlinear:_pydlinear")],
    cmdclass={"build_ext": BuildBazelExtension},
    packages=[PACKAGE_NAME],
    install_requires=["setuptools"],
)
