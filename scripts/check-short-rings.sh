#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenShortRingChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.short-rings.json
# The exterior colouring remains an explicit induction input, not an axiom.
