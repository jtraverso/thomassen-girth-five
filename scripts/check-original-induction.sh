#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build ThomassenOriginalInductionChallenge ThomassenOriginalTransportChallenge
lake build ThomassenSolution ThomassenAudit --wfail
lake comparator --config comparator.original-induction.json
lake comparator --config comparator.original-transport.json
# Strict original-invariant reductions are conditional on smaller instances.
# These checks do not close that induction or assert full original 2.1.
