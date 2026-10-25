#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenOriginalFullChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.original-full.json
