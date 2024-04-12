#!/bin/bash
docker build -t dlinear .
docker run -it --rm -v "$(pwd):/app" dlinear "$@"
