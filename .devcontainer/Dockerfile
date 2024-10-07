# You can pick any Debian/Ubuntu-based image. 😊
FROM ubuntu:22.04

LABEL author="Ernesto Casablanca"
LABEL workspace="dlinear"

# Options for setup script
ARG USERNAME="vscode"
ARG ADDITIONAL_PACKAGES="git python3 build-essential automake libtool"

# Install needed packages and setup non-root user. Use a separate RUN statement to add your own dependencies.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get install -y apt-utils curl \
    && apt-get upgrade -y && apt-get autoremove -y && apt-get clean -y

# [Optional] Uncomment this section to install additional OS packages.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends ${ADDITIONAL_PACKAGES}

# Install Bazel
ARG BAZELISK_VERSION=v1.22.0
ARG BAZELISK_DOWNLOAD_SHA=a110a613ac57081482348b9fa1719ede1fc9bb45a010f82f15eaeb1e9b657e29
RUN curl -fSsL -o /usr/local/bin/bazel https://github.com/bazelbuild/bazelisk/releases/download/${BAZELISK_VERSION}/bazelisk-linux-amd64 \
    && ([ "${BAZELISK_DOWNLOAD_SHA}" = "dev-mode" ] || echo "${BAZELISK_DOWNLOAD_SHA} /usr/local/bin/bazel" | sha256sum --check - ) \
    && chmod 0755 /usr/local/bin/bazel

ARG BUILDIFIER_VERSION=v7.3.1
ARG BUILDIFIER_DOWNLOAD_SHA=5474cc5128a74e806783d54081f581662c4be8ae65022f557e9281ed5dc88009
RUN curl -fSsL -o /usr/local/bin/buildifier https://github.com/bazelbuild/buildtools/releases/download/${BUILDIFIER_VERSION}/buildifier-linux-amd64 \
    && ([ "${BUILDIFIER_DOWNLOAD_SHA}" = "dev-mode" ] || echo "${BUILDIFIER_DOWNLOAD_SHA} /usr/local/bin/buildifier" | sha256sum --check - ) \
    && chmod 0755 /usr/local/bin/buildifier

RUN useradd -rm -d /home/${USERNAME} -s /bin/bash -g root -G sudo -u 1001 ${USERNAME} && passwd -d ${USERNAME} 

USER ${USERNAME}
