#!/usr/bin/env bash
set -euo pipefail

echo "[artifact] Running binary."
cvc5 $@
echo "[artifact] End."
