#!/usr/bin/env bash
set -euo pipefail

readonly RUN_NAME=${1:-}
readonly SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly IMAGE_TAG="qest-formats-ae:2026"
readonly IMAGE_TAR="${SCRIPT_DIR}/qest-formats-ae-image.tar.gz"
if [[ -z "${RUN_NAME}" ]]; then
    readonly RESULTS_DIR="${SCRIPT_DIR}/results"
else
    readonly RESULTS_DIR="${SCRIPT_DIR}/results-${RUN_NAME}"
fi
readonly INSTANCES_DIR="${SCRIPT_DIR}/instances"

if ! docker image inspect "${IMAGE_TAG}" >/dev/null 2>&1 && [[ -f "${IMAGE_TAR}" ]]; then
  echo "[artifact] Loading docker image from ${IMAGE_TAR}"
  docker load -i "${IMAGE_TAR}" >/dev/null
fi

echo "[artifact] Launching the Jupyter notebook to visualize the results"
docker run -p 8888:8888 --rm -v "${RESULTS_DIR}:/work/results:rw" -v "${INSTANCES_DIR}:/work/instances" "${IMAGE_TAG}"
