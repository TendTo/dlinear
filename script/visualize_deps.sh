#!/bin/bash
bazel query --noimplicit_deps --notool_deps 'deps(//dlinear) -@zlib//:copy_public_headers except kind("source file", deps(//dlinear)) -@platforms//...:* -@boost//...:* -//tools:* -@bazel_tools//tools/cpp:*' --output graph > graph.in && dot -Tpng < graph.in > graph.png && rm graph.in
