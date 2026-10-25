#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenRegistryChallenge
lake build Solution ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.registry.json
