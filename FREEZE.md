# Freeze audit

The requested proof scope is complete: finite planar girth-five
3-choosability, both alternatives of original Theorem 2.1, Corollary 2.2,
and the four additional results mapped to their papers in README.md.

## Public contract

Submit the repository-relative configuration **`comparator.registry.json`**.
It selects 15 theorem statements and 10 explicit definitions as one entry.
`ThomassenRegistryChallenge` is a standalone 16,403-byte, 404-line contract,
below the official 100 KiB hard cap. It imports only Mathlib, compiles without
candidate project output on `LEAN_PATH`, and reproduces no selected solution
proof bodies. Its source map identifies the definitions and source attributions.
Thirteen statement types are retained directly. Two componentwise statements
use `AmbientComponentOuterBoundary`: the same actual ambient face orbit in each
nontrivial component. `Thomassen.ambientComponentOuterBoundary_iff` proves this
certificate equivalent to the original induced-plane-map certificate, with no
extra hypothesis. RegistryBoundary.lean derives both public wrappers from their
unchanged original results. The contract uses ordinary checked definitions and
proofs; no elaborator cache manipulation is needed.

The original main/full-original/corollary/byproduct contracts and configurations
are retained unchanged; their baseline hashes are recorded separately.

The combined comparator has passed both the Lean and NanoDa kernels with only
`propext`, `Classical.choice` and `Quot.sound`. It introduces no external
extension, induction, removal or colouring hypothesis. In particular, the
smaller-instance premise is discharged by strong induction in OriginalClosure.
Intentional proof placeholders occur in independent challenge files only.

## Evidence

| Audit | Evidence |
|---|---|
| 15 public statements and 10 definitions; Lean and NanoDa acceptance | `verification/freeze-compact-comparator.log` |
| Strict Solution, ThomassenSolution and axiom audit | `verification/freeze-compact-strict-audit.log`; `ThomassenAudit.lean` |
| Contract compiles without candidate build output | `verification/freeze-compact-isolation.log` |
| 207 Thomassen solution modules without forbidden constructs | `verification/source-audit.json` |
| All 326 Lean sources, module headers, line limits, no source symlinks or prebuilt output | `verification/freeze-source-audit.json` |
| 74 pinned reused files retain their audited hashes | `verification/source-reuse.json`; freeze source audit |
| Original independent contracts retained byte for byte | `verification/freeze-baseline-hashes.json` |
| Metadata schema v0.4 | `verification/freeze-metadata-audit.json` |
| Paper/result attribution, source scope, reuse and AI assistance | `README.md`, `THIRD_PARTY.md`, `formalization.yaml` |

These are mechanical checks and an agent's source-alignment assessment;
independent human mathematical review and original-author endorsement are not
claimed. The sources use the existing registered plane-map and list-colouring
definitions. The infinite result states planarity of every finite induced
subgraph explicitly; the seven-cycle result concerns an outer cycle.

## Reproduction and remote checks

Use Lean `v4.35.0-rc3` with the checked-in pinned `lake-manifest.json`:

```sh
scripts/check-registry.sh
python3 scripts/audit-freeze.py
```

The source-reuse and original-contract checks are reproducible from this
checkout without fetching the prior local Git history. The registry contract
can be regenerated with `python3 scripts/prepare-registry-contract.py`.

GitHub CI compiles the solution strictly and builds the independent challenge.
The Palomar preflight workflow invokes the official verifier at
`c02bbeaed888df45c4e28c4e99dba540ad21552a` in `full` mode, with the
`palomar-standard-v1` execution profile. It binds the exact remote commit and
`comparator.registry.json`. Its report and digest must be recorded against that
same remote commit before intake. Preflight is predictive verification and
does not itself submit, review or register an entry.

Publication and Palomar intake receipts are maintained outside the immutable
source commit, so recording their URLs cannot silently move the frozen source.
If a code or contract correction is needed, create and verify a new source
commit; retain the earlier evidence with its original meaning.

## Remote preflight history and packaging corrections

The first public source commit, `28cab414b949ad4d07f373fb54807a089395a75a`,
passed strict GitHub CI, but official preflight
[40211686315](https://github.com/jtraverso/thomassen-girth-five/actions/runs/40211686315)
rejected the protected contract's local `Challenge` import. A standalone flattened
contract in `4540bc3cd2892f5fb1052c8c4fd44384daf6306a` passed strict CI and the
isolated smoke check, but official preflight
[40213978009](https://github.com/jtraverso/thomassen-girth-five/actions/runs/40213978009)
rejected its 435,588-byte size against the 100 KiB cap.

The compact contract addresses both errors. Its generator, isolated smoke check
and freeze audit enforce the size cap. The original 206 solution modules are
retained, with an added equivalence-and-wrapper module and updated aggregators;
all original independent contracts remain unchanged. Lean and NanoDa accept the
compact combined contract. The corrected immutable commit needs its own official
preflight; neither earlier failed run is presented as an acceptance.
