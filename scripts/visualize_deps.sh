#!/bin/bash
bazel query --noimplicit_deps 'deps(//dlinear)' --output graph > graph.in && dot -Tpng < graph.in > graph.png && rm graph.in
