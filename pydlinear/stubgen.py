import sys
import os
from pybind11_stubgen import main as stubgen_main


def main():
    assert len(sys.argv) == 3, "Usage: python -m pydlinear.stubgen <output_file> <output_file>"
    # output file is something like 'bazel-out/k8-fastbuild/bin/pydlinear/_pydlinear.pyi'
    # We need the path up to 'bin' to generate the stubs
    out_dir = os.path.dirname(os.path.dirname(sys.argv[1]))
    old_argv = sys.argv
    sys.argv = [sys.argv[0], "pydlinear", "-o", out_dir]
    stubgen_main()
    sys.argv = old_argv

if __name__ == "__main__":
    main()
