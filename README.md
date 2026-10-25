# Thomassen: planar graphs of girth at least five are 3-choosable

Lean formalization of C. Thomassen, *3-List-Coloring Planar Graphs of Girth 5*,
JCT B **64** (1995), 101–107,
[doi:10.1006/jctb.1995.1027](https://doi.org/10.1006/jctb.1995.1027).
The finite 3-choosability theorem, **both alternatives of the full original
Theorem 2.1**, and **Corollary 2.2** are proved and kernel checked.
The four additional results listed below are also proved.

```lean
theorem PlanarChoosability.choosableWith_three_of_isPlanar
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (hplanar : PlanarChoosability.IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : PlanarChoosability.ChoosableWith G C 3
```

The exact public original statement is `Thomassen.original_theorem_2_1` in
[OriginalTheorem.lean](Thomassen/OriginalTheorem.lean). It allows an independent
outer short set or a single exceptional short edge with the original
distinguished endpoint's no-two-path condition. It extends any two distinct
allowed colours on the prescribed outer edge. Colours have an arbitrary type,
and the graph may be disconnected. `ComponentOuterBoundary` supplies an actual
selected face in every nontrivial exterior component; isolated vertices need
no dart. No extension, deletion or colouring hypothesis remains in the result.

`Thomassen.original_corollary_2_2` in
[OriginalCorollary.lean](Thomassen/OriginalCorollary.lean) exposes the original
outer-five-cycle extension. The paper's two numbered results are therefore
covered; this does not assert a declaration for every intermediate sentence.

## Proof and reuse

The central 3-choosability proof follows the unsigned short-boundary route
from Jin–Kang–Steffen, Appendix Theorem 5.1, and Cranston, §11.4. Its
six-vertex boundary-extension induction is closed in
[BoundaryExtension.lean](Thomassen/BoundaryExtension.lean).
The full original Theorem 2.1 additionally follows Thomassen's original
exceptional-edge reductions, especially source steps (9) and (10), printed
pp. 104–105:

- [OriginalFirstObstruction.lean](Thomassen/OriginalFirstObstruction.lean) and
  [OriginalSecondObstruction.lean](Thomassen/OriginalSecondObstruction.lean)
  resolve both residual two-path obstructions. The actual second five-face
  forces degree two at q₂ if the first endpoint were newly exposed.
- [OriginalFinalShortSets.lean](Thomassen/OriginalFinalShortSets.lean),
  [OriginalFinalCutGeometry.lean](Thomassen/OriginalFinalCutGeometry.lean) and
  [OriginalFinalCut.lean](Thomassen/OriginalFinalCut.lean) verify both final
  cut choices, the augmented short sets, strict size decreases and restoration
  of temporary two-list colours. Interior and boundary intermediate vertices
  are both handled.
- [OriginalExceptionalFrame.lean](Thomassen/OriginalExceptionalFrame.lean)
  composes the entire framed exceptional case.
  [OriginalClosure.lean](Thomassen/OriginalClosure.lean) prunes marks to actual
  two-lists, orients the distinguished endpoint by rebasing or mirroring,
  and closes strong induction. The global export fills all other components
  with the existing unconditional component theorem.

The proof reuses registered `planar-list-colouring` and `grotzsch-ore`
infrastructure for lists, graph restrictions, plane maps, face regions and
colouring glue, together with the previously verified short-path and ring
extensions in this package. All **74** files tracked by the pinned source-reuse
audit retain their recorded hashes. The old short-leaf cut API is retained as
a specialization of the generalized released-leaf cut.
Pinned revisions, licences, attribution and exact source-reading scopes are in
[THIRD_PARTY.md](THIRD_PARTY.md) and [SOURCE_REVIEW.md](SOURCE_REVIEW.md).

## Registry submission and freeze

The submission uses **`comparator.registry.json`**: one entry selecting 15
public theorem statements and 10 explicit definitions. Its independent contract,
[ThomassenRegistryChallenge.lean](ThomassenRegistryChallenge.lean), reproduces
those statements from the original main, full-2.1, Corollary-2.2 and byproduct
contracts. Earlier infrastructure is reproduced with source notices, so the
contract imports only trusted Mathlib/core elaboration modules and compiles
without any candidate project build output. It does not reproduce any of the
15 selected solution proof bodies. The original
contracts and configurations remain byte-for-byte unchanged.

The standalone combined configuration passes both Lean and NanoDa. A separate
smoke check compiles it with the candidate project removed from `LEAN_PATH`. The freeze source audit
checks all 325 Lean files, 74 reused hashes, pinned dependencies, source headers,
source limits, absence of prebuilt output and preservation of the earlier
contracts. Metadata is validated against the official v0.4 schema.
The first remote preflight detected a local-import packaging issue; the
standalone contract and smoke check correct it while retaining the original
individual contracts and all solution proof bodies.
See [FREEZE.md](FREEZE.md) and [freeze-status.json](verification/freeze-status.json).

```sh
scripts/check-registry.sh
python3 scripts/audit-freeze.py
```

The GitHub workflows run strict Lean CI and the official reusable full Palomar
mechanical preflight, pinned to
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, using
`palomar-standard-v1`. Preflight verifies an immutable commit; it does not submit
or register an entry. Actual publication and submission receipts are tracked
separately so local verification is not presented as a registry action.

## Reproduce the checks

Lean: `v4.35.0-rc3`. Mathlib:
`c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
scripts/check-main.sh
scripts/check-original-full.sh
scripts/check-byproducts.sh
```

The full-original gate checks the unchanged independent statement in
[ThomassenOriginalFullChallenge.lean](ThomassenOriginalFullChallenge.lean),
which imports only the pre-existing outer-boundary infrastructure.
`comparator.original-full.json` is an identical canonical alias for the
previously pending `comparator.original-full-pending.json`; the latter now
passes without changing its statement, definitions or permitted axioms.
The original central `comparator.json`, including its nine definition contracts,
is also unchanged. Both gates enable Lean and NanoDa.

Current evidence:
[original-full-status.json](verification/original-full-status.json),
[original-full-comparator.log](verification/original-full-comparator.log), and
[main-after-original-full-comparator.log](verification/main-after-original-full-comparator.log).
The solution source audit covers **206 modules**, with no `sorry`, `admit`,
custom axioms or `native_decide`. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Independent challenge files intentionally contain
placeholders; they are not imported by the solution.

Earlier support gates remain available in `scripts/`. Earlier failed logs and
incomplete statuses are historical checkpoints, superseded by the full-original
status above. Their original evidence is retained in [PROGRESS.md](PROGRESS.md)
and [CLOSURE_PLAN.md](CLOSURE_PLAN.md).

## Authorship and scope of review

Author and maintainer: Juan Pablo Traverso Gianini. OpenAI Codex produced new
Lean proof code under the author's direction, reusing the libraries above.
No sub-agents or external theorem-proving service were used. Statement alignment
was self-assessed; kernel checks are mechanical verification and do not imply
independent human review or a mathematical novelty claim.

Apache-2.0. See [LICENSE](LICENSE) and retained source notices.
Publication and Palomar submission are tracked separately from local proof
completion. Copied `upstream-planar/` metadata belongs to the prerequisite project.

## Additional results and paper provenance for Palomar

The four requested extensions below are proved in this package. The source
column identifies the exact result covered; it does not assert formalization
of every theorem in any of the cited papers.

| # | Verified result | Paper / exact source | Lean declaration |
|---:|---|---|---|
| 1 | A proper precolouring of a boundary path of at most five edges extends, with independent exterior two-lists avoiding the prescribed vertices. Proper chords in the prescribed path are allowed; exterior components are handled separately. | Z. Dvořák and K. Kawarabayashi, *Choosability of planar graphs of girth 5* (2011), [arXiv:1109.2976](https://arxiv.org/abs/1109.2976), **Theorem 1**, attributed there to Thomassen. This exposes and adapts the already proved short-extension infrastructure; it does not prove their stronger Theorem 3 or critical-graph bounds. | `Thomassen.dvorak_kawarabayashi_theorem_1_global` |
| 2 | Infinite finite-list 3-colourability whenever every finite induced subgraph is planar of girth at least five. The vertex set and total colour type may be infinite. | Derived from Thomassen's finite theorem and **Rado's selection principle**, already proved in Mathlib. R. Rado, *Axiomatic Treatment of Rank in Infinite Sets*, Canadian J. Math. **1** (1949), 337–343, [doi:10.4153/CJM-1949-031-1](https://doi.org/10.4153/CJM-1949-031-1). Historical finite-subgraph reference: N. G. de Bruijn and P. Erdős, *A colour problem for infinite graphs and a problem in the theory of relations*, Proc. KNAW A **54** (1951), 371–373. This is a finite-list consequence using the existing compactness proof, not a new formalization of both classical papers in full. | `Thomassen.infinite_three_list_colourable`; `Thomassen.infinite_three_list_colourable_of_egirth` |
| 3 | Any proper allowed colouring of **any five- or six-cycle** extends, including separating cycles and graphs with other connected components. | C. Thomassen, *3-List-Coloring Planar Graphs of Girth 5* (1995), abstract and **Corollary 2.2** for five-cycles. The six-cycle version is a derived consequence of the proved short-boundary extension (the unsigned route recorded in Jin–Kang–Steffen, [arXiv:1502.04561](https://arxiv.org/abs/1502.04561), Appendix Theorem 5.1), with two-side separation and gluing. The six-cycle statement is not labelled as an original numbered 1995 result. | `Thomassen.extend_any_short_cycle` |
| 4 | Every proper allowed colouring of an **outer seven-cycle** extends in a finite plane graph of girth at least five. Arbitrary colour types and lists of size at least three are allowed. | N. Asghar, *Grötzsch's Theorem*, University of Waterloo MMath research essay (2012), [source PDF](https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf), **Lemma 3.2.3, seven-cycle specialization**. The essay credits the Chapter 3 proof to unpublished work of C. Nunes da Silva, R. B. Richter and D. Younger, inspired by Thomassen. This package does not claim the whole essay or its outer-four-cycle exception. | `Thomassen.extend_outer_seven_cycle` |

The implementation of #4 uses the proved six-vertex extension: an odd
seven-cycle has a vertex with differently coloured neighbours. Release that
vertex to a three-element auxiliary list consisting of its original colour
and those two neighbour colours, and retain the other six prescribed vertices.
Their colours force the released vertex back to its original colour. Every
output colour is checked against the original lists. This is a proof of the
known result, with no mathematical novelty claim.

The compactness implementation in #2 imports
`Finset.rado_selection_subtype` from the module
`Mathlib.Combinatorics.Compactness`; its Mathlib source is by Bhavik Mehta
(2025). The finite graph theorem, plane-map restrictions, cycle separation,
connected prescriptions and colouring glue are reused from the existing package.

Reproduce the additional-result checks with `scripts/check-byproducts.sh`.
The independent challenge imports none of their five proof modules and adds
no definition hole. The paper provenance above is the source mapping for a
later Palomar README or submission.

`Thomassen.extend_exterior_across_short_ring` also fills an actual ring of at
most seven vertices while retaining a supplied exterior colouring exactly.
It is reused in the full original induction to eliminate separating short
cycles. See `scripts/check-short-rings.sh`.
