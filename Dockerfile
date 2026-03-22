# syntax=docker/dockerfile:1.19

# -------- Builder stage --------
FROM ubuntu:24.04 AS builder

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    cmake \
    ninja-build \
    git \
    curl \
    pkg-config \
    python3 \
    zstd \
    libgmp-dev \
    python3-venv \
    libtool \
    libz-dev \
    libboost-all-dev \
    libmpfr-dev \
    libbz2-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src

# Fetch and unpack SMT-LIB QF_LRA benchmark archive
RUN mkdir -p /opt/benchmarks \
    && curl -L "https://zenodo.org/records/16740866/files/QF_LRA.tar.zst?download=1" \
    -o /tmp/QF_LRA.tar.zst \
    && tar --zstd -xf /tmp/QF_LRA.tar.zst -C /opt/benchmarks \
    && rm -f /tmp/QF_LRA.tar.zst

RUN git clone https://github.com/TendTo/qsopt-ex.git --depth 1 \
    && cd /src/qsopt-ex \
    && ./bootstrap \
    && mkdir build && cd build \
    && ../configure --disable-debug CFLAGS='-O3' \
    && make -j"$(nproc)" \
    && make install

RUN git clone https://github.com/scipopt/soplex.git --depth 1 \
    && cd /src/soplex \
    && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DGMP=ON -DMPFR=ON -DBOOST=ON -DZLIB=OFF \
    && cd build \
    && make -j"$(nproc)" libsoplex \
    && make install

RUN sed -i -re 's/\.so([^.])/\.a\1/g' /usr/local/lib/cmake/soplex/soplex-targets.cmake \
    && sed -i -re 's/\.so([^.])/\.a\1/g' /usr/local/lib/cmake/soplex/soplex-targets-release.cmake

WORKDIR /src/cvc5

COPY --exclude=benchmarks . /src/cvc5

## Configure and build cvc5 as a static binary.
## Keeping tests/docs/bindings off to keep build time and image size reasonable.
RUN cmake -S . -B build -G Ninja \
    -DCMAKE_BUILD_TYPE=Production \
    -DBUILD_SHARED_LIBS=OFF \
    -DSTATIC_BINARY=ON \
    -DENABLE_UNIT_TESTING=OFF \
    -DBUILD_DOCS=OFF \
    -DBUILD_BINDINGS_PYTHON=OFF \
    -DBUILD_BINDINGS_JAVA=OFF \
    -DUSE_SOPLEX:BOOL=ON \
    -DUSE_GLPK:BOOL=ON \
    -DENABLE_AUTO_DOWNLOAD=ON \
    -DENABLE_GPL:BOOL=ON \
    -DUSE_QSOPTEX:BOOL=ON \
    && cmake --build build --target cvc5-bin -j"$(nproc)"

ENTRYPOINT ["/bin/bash"]

# -------- Runtime stage --------
FROM ubuntu:24.04 AS runtime

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    zstd \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /work

# Copy the cvc5 binary and benchmarks into runtime image
COPY --from=builder /src/cvc5/build/bin/cvc5 /usr/local/bin/cvc5
COPY --from=builder /opt/benchmarks /benchmarks

# Default command: print version to confirm binary is runnable
ENTRYPOINT ["/usr/local/bin/cvc5"]
CMD ["--version"]
