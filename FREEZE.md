# Freeze audit

The requested proof scope is complete: finite planar girth-five
3-choosability, both alternatives of original Theorem 2.1, Corollary 2.2,
and the four additional results mapped to their papers in README.md.

## Public contract

Submit the repository-relative configuration **`comparator.registry.json`**.
It selects 15 theorem statements and 10 explicit definitions as one entry.
`ThomassenRegistryChallenge` reproduces the independently checked public
statements and boundary definition together with their earlier infrastructure.
It imports only trusted Mathlib/core elaboration modules, and compiles with
no candidate project output on `LEAN_PATH`. It reproduces none of the 15 selected
solution proof bodies. `verification/registry-contract-source-map.json` records
the original source modules and their retained notices. The generator clears
Lean’s module-local auxiliary-proof cache between reproduced files, retaining
the original generated proof names. This changes no declaration, type, proof
or kernel setting.
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
| 15 public statements and 10 definitions; Lean and NanoDa acceptance | `verification/freeze-registry-standalone-comparator.log` |
| Strict Solution, ThomassenSolution and axiom audit | `verification/freeze-standalone-strict-audit.log`; `ThomassenAudit.lean` |
| Contract compiles without candidate build output | `verification/freeze-standalone-isolation.log` |
| 206 Thomassen solution modules without forbidden constructs | `verification/source-audit.json` |
| All 325 Lean sources, module headers, line limits, no source symlinks or prebuilt output | `verification/freeze-source-audit.json` |
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

## First remote preflight and packaging correction

The first public source commit, `28cab414b949ad4d07f373fb54807a089395a75a`,
passed strict GitHub CI, but its official preflight
[40211686315](https://github.com/jtraverso/thomassen-girth-five/actions/runs/40211686315)
rejected the protected contract’s local `Challenge` import. This was a packaging
limitation missed by the ordinary local build. The corrected contract is
self-contained, retains all 15 original statements and 10 compared definitions,
and passes both the isolated-dependency smoke check and Lean/NanoDa comparison.
All 206 solution modules and the original individual contracts remain unchanged.
The corrected immutable commit needs its own official preflight; the earlier
failed run is retained with its original meaning.
