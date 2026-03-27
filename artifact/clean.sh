#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

echo "[artifact] Cleaning up previous results from ${SCRIPT_DIR}"
rm -rf ${SCRIPT_DIR}/results-*
