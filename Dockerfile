FROM ubuntu:22.04 as build

LABEL author="Ernesto Casablanca"
LABEL workspace="dlinear"

WORKDIR /app

RUN apt-get update && \
    export DEBIAN_FRONTEND=noninteractive && \
    apt-get install -y curl && \
    apt-get upgrade -y && \
    apt-get autoremove -y && \
    apt-get clean -y

ARG BAZELISK_VERSION=v1.19.0
ARG BAZELISK_DOWNLOAD_SHA=dev-mode
RUN curl -fSsL -o /usr/local/bin/bazel https://github.com/bazelbuild/bazelisk/releases/download/${BAZELISK_VERSION}/bazelisk-linux-amd64 \
    && ([ "${BAZELISK_DOWNLOAD_SHA}" = "dev-mode" ] || echo "${BAZELISK_DOWNLOAD_SHA} */usr/local/bin/bazelisk" | sha256sum --check - ) \
    && chmod 0755 /usr/local/bin/bazel


ARG APT_PACKAGES="git python3 build-essential automake libtool"
RUN export DEBIAN_FRONTEND=noninteractive && \
    apt-get install -y --no-install-recommends ${APT_PACKAGES} && \
    apt-get autoremove -y && \
    apt-get clean -y

COPY . .

RUN bazel build //dlinear --//tools:enable_static_build=True

FROM alpine:3.19.0

WORKDIR /app

COPY --from=build /app/bazel-bin/dlinear /sbin

ENTRYPOINT ["dlinear"]
