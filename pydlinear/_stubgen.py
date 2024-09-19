import sys
import os
from pybind11_stubgen import main as stubgen_main


def generate_stub_files(out_dir: "str") -> list[str]:
    # The first two are the .pyi files generated by pybind11_stubgen
    # They have a structure like 'bazel-out/k8-fastbuild/bin/pydlinear/_pydlinear.pyi'
    # We need the path up to 'bin' to generate the stubs
    old_argv = sys.argv
    sys.argv = [sys.argv[0], "pydlinear", "-o", out_dir]
    stubgen_main()
    sys.argv = old_argv


def generate_pytyped_file(out_file: "str"):
    with open(out_file, "wb") as f:
        f.write(b"")


def main():
    assert len(sys.argv) == 4, "Usage: python -m pydlinear._stubgen <output_file> <output_file> <output_file>"

    generate_stub_files(os.path.dirname(os.path.dirname(sys.argv[1])))
    generate_pytyped_file(sys.argv[3])

    assert os.path.exists(sys.argv[1]), f"Output file {sys.argv[1]} not found"
    assert os.path.exists(sys.argv[2]), f"Output file {sys.argv[2]} not found"
    assert os.path.exists(sys.argv[3]), f"Output file {sys.argv[3]} not found"


if __name__ == "__main__":
    main()