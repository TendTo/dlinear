#!/bin/bash

# Clean bazel cache
bazel clean --expunge
rm -rf ~/.cache/dlinear_bazel*
