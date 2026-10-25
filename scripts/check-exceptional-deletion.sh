#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenExceptionalDeletionChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.exceptional-deletion.json
# This verifies the deletion and equal-list normalization, not full Theorem 2.1.
