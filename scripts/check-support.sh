#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-proof-sources.py
lake build Challenge
lake build --wfail
lake build ThomassenAudit --wfail
python3 scripts/check-assembly.py
lake build ThomassenChallenge
lake comparator --config comparator.support.json
lake build ThomassenGeometryChallenge
lake comparator --config comparator.geometry.json
lake build ThomassenInducedChallenge
lake comparator --config comparator.induced.json
lake build ThomassenInstanceChallenge
lake comparator --config comparator.instances.json
lake build ThomassenConnectedChallenge
lake comparator --config comparator.connected.json
lake build ThomassenCycleChallenge
lake comparator --config comparator.cycles.json
lake build ThomassenChordChallenge
lake comparator --config comparator.chords.json
lake build ThomassenFiveChallenge
lake comparator --config comparator.five.json
lake build ThomassenEdgeCutChallenge
lake comparator --config comparator.edge-cuts.json
lake build ThomassenInteriorCutChallenge
lake comparator --config comparator.interior-cuts.json
lake build ThomassenPathCutChallenge
lake comparator --config comparator.path-cuts.json
lake build ThomassenAugmentedChallenge
lake comparator --config comparator.augmented.json
lake build ThomassenFanChallenge
lake comparator --config comparator.fans.json
lake build ThomassenEdgeStarChallenge
lake comparator --config comparator.edge-stars.json
lake build ThomassenMixedChordChallenge
lake comparator --config comparator.mixed-chords.json
lake build ThomassenBoundaryChordChallenge
lake comparator --config comparator.boundary-chords.json
lake build ThomassenInteriorTwoPathChallenge
lake comparator --config comparator.interior-two-paths.json
lake build ThomassenEndpointDeletionChallenge
lake comparator --config comparator.endpoint-deletion.json
lake build ThomassenSubarcReductionChallenge
lake comparator --config comparator.subarc-reductions.json
lake build ThomassenPrescribedTwoPathChallenge
lake comparator --config comparator.prescribed-two-paths.json
lake build ThomassenBoundaryDeletionChallenge
lake comparator --config comparator.boundary-deletion.json
lake build ThomassenAlternatingListsChallenge
lake comparator --config comparator.alternating-lists.json
lake build ThomassenConnectedPrescriptionChallenge
lake comparator --config comparator.connected-prescriptions.json
lake build ThomassenTwoBoundaryChallenge
lake comparator --config comparator.two-boundary.json
lake build ThomassenPrescribedNeighboursChallenge
lake comparator --config comparator.prescribed-neighbours.json
lake build ThomassenMixedTwoPathChallenge
lake comparator --config comparator.mixed-two-paths.json
lake build ThomassenThreePathChallenge
lake comparator --config comparator.three-paths.json
lake build ThomassenGoodFourthPathChallenge
lake comparator --config comparator.good-fourth-path.json
lake build ThomassenSixPathDeletionChallenge
lake comparator --config comparator.six-path-deletion.json
lake build ThomassenStartingStatesChallenge
lake comparator --config comparator.starting-states.json
lake comparator --config comparator.planar-base.json

lake build ThomassenFiveVertexClosureChallenge
lake comparator --config comparator.five-vertex-closure.json

lake build ThomassenSixVertexProgressChallenge
lake comparator --config comparator.six-vertex-progress.json

lake build ThomassenSixVertexClosureChallenge
lake comparator --config comparator.six-vertex-closure.json
