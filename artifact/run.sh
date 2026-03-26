#!/usr/bin/env bash
set -euo pipefail

readonly RUN_NAME=${1:-smoke}
readonly LOCAL_LIMIT=${2:-6}
readonly SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly IMAGE_TAG="qest-formats-ae:2026"
readonly IMAGE_TAR="${SCRIPT_DIR}/qest-formats-ae-image.tar.gz"
readonly RESULTS_DIR="${SCRIPT_DIR}/results-${RUN_NAME}"
readonly INSTANCES_DIR="${SCRIPT_DIR}/instances"

mkdir -p "${RESULTS_DIR}"
mkdir -p "${INSTANCES_DIR}"

# Run the ${RUN_NAME} test as the host user so the bind-mounted results directory is writable.
readonly HOST_UID="$(id -u)"
readonly HOST_GID="$(id -g)"

if ! docker image inspect "${IMAGE_TAG}" >/dev/null 2>&1 && [[ -f "${IMAGE_TAR}" ]]; then
  echo "[artifact] Loading docker image from ${IMAGE_TAR}"
  docker load -i "${IMAGE_TAR}" >/dev/null
fi

echo "[artifact] Running ${RUN_NAME} test"
docker run --rm \
  --user "${HOST_UID}:${HOST_GID}" \
  -v "${RESULTS_DIR}:/results:rw" \
  -v "${INSTANCES_DIR}:/instances" \
  --entrypoint ./run_impl.sh \
  "${IMAGE_TAG}" "${RUN_NAME}" "${LOCAL_LIMIT}"

echo "[artifact] Launching the Jupyter notebook to visualize the results"
docker run -p 8888:8888 --rm -v "${RESULTS_DIR}:/work/results:rw" -v "${INSTANCES_DIR}:/work/instances" "${IMAGE_TAG}"
