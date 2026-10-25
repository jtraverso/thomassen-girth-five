#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenExceptionalBridgeChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.exceptional-bridge.json
# These are reductions and selected extension cases, not full original 2.1.
