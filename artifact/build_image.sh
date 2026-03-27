#!/usr/bin/env bash
set -euo pipefail

# Build and export the docker image used for artifact evaluation.

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd)"

IMAGE_TAG="qest-formats-ae:2026"
OUT_TAR_GZ="${SCRIPT_DIR}/qest-formats-ae-image.tar.gz"

cd "$REPO_ROOT"

echo "[artifact] Building docker image: ${IMAGE_TAG}"
docker build -f Dockerfile -t "${IMAGE_TAG}" .

echo "[artifact] Saving image to: ${OUT_TAR_GZ}"
# -1: fast gzip; good enough for artifacts, avoids very long compression time.
docker save "${IMAGE_TAG}" | gzip -1 > "${OUT_TAR_GZ}"

# echo "[artifact] Writing SHA-256"
sha256sum "${OUT_TAR_GZ}" > "${OUT_TAR_GZ}.sha256"

echo "[artifact] Done"
