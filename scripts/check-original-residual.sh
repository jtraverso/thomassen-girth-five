#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenOriginalResidualChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.original-residual.json
# This verifies source (9) and residual/face operations from source (10).
# It does not close the original strong induction or the full Theorem 2.1.
