#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenOriginalPaperChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.original-paper.json
# The full original Theorem 2.1 is a separate, currently pending target.
# Do not interpret this gate as proving its exceptional separated-edge case.
