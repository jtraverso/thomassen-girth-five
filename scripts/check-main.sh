#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build Challenge ThomassenMainChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.json
