# Full original Theorem 2.1 closed — 2026-10-25

`Thomassen.original_theorem_2_1` is now proved for both original alternatives,
arbitrary colour types and lists, arbitrary allowed colours on the fixed edge,
and all exterior components. The original independent target and its comparator
configuration were retained unchanged. Lean and NanoDa both accept the solution.
Corollary 2.2, the central 3-choosability theorem and requested byproducts 1–4
are also complete. No mathematical obligations remain in this requested scope.

The endpoint analysis in source (10) is complete: a newly exposed endpoint of
the first residual two-path would yield an actual second five-face forcing
q₂ to have degree two despite its three-list. An old endpoint forces the next
three original boundary positions and degree two at both old exceptional
vertices. Girth five and those degree conclusions force the other obstruction
to end in the old short set. The final cut is proved for both an interior and
an outer intermediate vertex. Its two start choices keep the fixed edge and
old exception in the first piece, while the augmented short set in the other
piece has precisely the original required shape. Temporary two-lists are
forced back to the first piece's colours by the prescribed central edge.

The old strict-induction premise is fully discharged by
`original_instances_extend_at_card`. Pruning changes marks only, mirroring
changes the embedding only, and both preserve the exact requested output.
The global theorem uses the actual componentwise face certificate and the
previously proved free-component assembly. No normalization, cut certificate,
residual invalidity or extension hypothesis is left in its public statement.

The original scan correction remains: the degree-two vertex on printed p. 105
is q₂, not the OCR's q₁. The proof uses the actual second-face corner equations.
The original independent branch is reused rather than reproducing source
steps (11)–(13). The source reductions for the exceptional branch are newly
proved using the previously checked geometry and list infrastructure.

Reproduction: `scripts/check-original-full.sh` and `scripts/check-main.sh`.
Exact evidence: `verification/original-full-status.json`. Strict source/axiom
builds pass; all 206 solution modules have no forbidden constructs and all
74 reused source hashes are unchanged. Publication and registry submission
remain separate actions. No independent human review is claimed.

## Historical checkpoints (superseded by the full closure above)

# Original scan reviewed; predecessor and residual obstruction verified — 2026-10-25

The full original Theorem 2.1 is **not proved**. The original page images at
printed pp. 104–105 were checked directly, rather than relying on the OCR.
On p. 105 the degree-two contradiction concerns **q₂**, not q₁; the OCR had
misread that subscript. This corrects the reading of the proof, not a claim
that a previously kernel-checked theorem had a wrong proof.

The predecessor assertion in source (9) is now proved for any oriented native
facial cycle with the exceptional edge at positions 1,2. The proof colours and
deletes the exceptional pair, proves residual short-set independence, colours
every residual component with a strict decrease, and restores both old fixed
colours. No connected-remainder assumption is made. Pruning marks to actual
two-lists supplies the predecessor cardinality used in the next source step.

The actual triple deletion in source (10) is also proved: choose the first
colour outside the predecessor's two-list, verify allowed proper colours on
the deleted path, preserve every old short list, and prove all residual lists
have size at least two. If the remaining marked set satisfied the original
short-set condition, componentwise strict induction would extend it and restore
the deleted path. Hence that residual condition fails. The geometric proof
classifies and makes unique the new short edge, including the possibility that
its first endpoint lies on the old boundary. A proved certificate supplies a
two-path obstruction from each endpoint in the actual remaining vertex type,
and degree two at the old middle vertex. The second-face support proves actual
corners and saturation independent of the originally selected exterior face.

Nineteen new theorem contracts and one independently reproduced definition pass
Lean and NanoDa. All 198 solution modules pass the source audit, strict solution
and axiom builds pass, and the 74 pinned reused source hashes are unchanged.
**The two-obstruction analysis and final cut in source (10) are still missing.**
The new first-obstruction certificate and second-face operations do not exclude
all of those configurations. Strong induction and the exact global export
`Thomassen.original_theorem_2_1` remain unproved. Prior endpoint normalization
notes below are historical: the new triple deletion preserves arbitrary fixed
colours using the already proved short-bridge exclusion.

Current verification and exact remaining obligations:
`verification/original-residual-status.json`; reproduction:
`scripts/check-original-residual.sh`. Earlier checkpoints below are historical.

# Original exceptional-edge induction reductions — 2026-10-25

The full original Theorem 2.1 is **not proved**. The current work now has a
separate `OriginalBoundaryInstance` carrying exactly the independent-or-single
exceptional-edge short-set condition. It has no extension field. Its output,
`Extends`, is a separate proposition. The invariant is inherited by actual
induced restrictions and graph embeddings; removing marks from the short set
preserves it. Pruning marks down to actual two-lists changes no lists or output.

Thirty new independent contracts verify strict-induction reductions: disconnected
components, vertices of cardinality at most two, every cutvertex, actual edge
cuts and native facial chords, separating cycles of at most six vertices,
interior two-paths from a short vertex to the exterior boundary, and interior
three-paths between short vertices. They also verify restoration at a low-degree
nonfixed vertex and the actual five-face corner/uniqueness consequences needed
for the triple deletion. The actual cuts construct selected faces on both sides.
Five additional contracts and one independently reproduced pruning definition
verify short-set transport and normalization. Both gates pass Lean and NanoDa.
The strict solution/axiom build passes; 190 solution modules have no forbidden
constructs and all 74 pinned reused source hashes are unchanged.

**The induction itself remains open.** The cut results explicitly assume the
original invariant only on strictly smaller vertex types. They are not proofs
of its unrestricted extension. The remaining source route needs general fixed
endpoint normalization, the predecessor/double-deletion reduction in step (9),
and the residual obstruction and final cut for the triple deletion in step (10),
followed by closing strong induction and exporting the exact global statement.
Existing incident and short-bridge cases already handle some small-position
subcases. Neither an input invariant nor the strict induction hypotheses are
counted as a solution declaration for `Thomassen.original_theorem_2_1`.

Reproduction: `scripts/check-original-induction.sh`. Exact scope and results:
`verification/original-induction-status.json`. The central three-choosability
result, Corollary 2.2 and requested byproducts 1–4 remain proved. Earlier
checkpoint paragraphs below retain their historical scope.

# Further original-2.1 reductions — 2026-10-25

The full original Theorem 2.1 is **not proved**. Eight additional declarations
close all orientations of joined exceptional edges, a two-edge bridge with its
middle vertex on the selected face, and the assembly of all free components.
The bridge works at either exceptional endpoint and needs no two-path
exclusion. It reuses the completed connected-prescription theorem: a connected
four-vertex core only needs to cover every short-list edge, with independent
short leaves attached at unique parents. The older stronger core API is retained.

Every global counterexample is now proved to give a counterexample in the
component containing the prescribed edge; both exceptional endpoints lie in
that component. It has identical two-element endpoint lists and no joining
edge or two-edge bridge whose middle vertex lies on the selected face.
**This is a necessary condition, not a contradiction.** Nonexistence of that
remaining connected configuration is the still-missing proof. The original
1995 proof, reductions (3)–(10), uses actual boundary cuts and a three-vertex
deletion to exclude it. Those reductions cannot be inferred from the existing
independent-set extension merely by enlarging a list.

Current implementations: `Thomassen/ExceptionalBoundaryBridge.lean` and
`Thomassen/OriginalExceptionalComponents.lean`. Independent contract config:
`comparator.exceptional-bridge.json`. The unchanged full target remains in
`comparator.original-full-pending.json`; no solution declaration is supplied
for `Thomassen.original_theorem_2_1`. Earlier checkpoints below retain their
historical scope.

# Requested extensions 1–4 implemented — 2026-10-25

All four requested extensions are now proved locally: the source-aligned short
boundary-path theorem, the infinite finite-list compactness consequence, the
arbitrary five/six-cycle extension and the outer-seven-cycle specialization.
The new source-to-declaration table in README.md is ready for future Palomar
metadata. Twelve independent contracts pass Lean and NanoDa; no new definition
hole is introduced. The original full 1995 Theorem 2.1 remains pending at the
separated identical-two-list exceptional edge. Its central three-choosability
theorem and original Corollary 2.2 remain complete. The source audit now covers
177 solution modules without forbidden constructs.

For that pending induction, ShortRingGluing also supplies actual ring filling
while preserving a given exterior colouring, with arbitrary original lists on
the precoloured ring and three-lists only in the uncoloured interior. This is
an induction operation, not a proof of existence of the required exterior
colouring. Earlier analysis-only notes for items 1–4 below are historical;
items 5–6 and the Alon–Füredi counting candidate remain analysis only.

# Original-paper extension — 2026-10-25

The requested broader paper scope is **in progress**. The central finite
3-choosability theorem and complete BoundaryExtension remain proved.
Corollary 2.2 is now explicit and proved. Theorem 2.1(i), including disconnected
exterior components, is proved. The incident and joined-edge subcases of (ii)
are proved; the general separated exceptional edge remains open.
The independently written full target includes the original no-two-path
condition, but has no matching solution declaration. The passed eleven-theorem
original-paper gate must not be read as proof of the full Theorem 2.1.
Current scope and checks: `verification/original-paper-status.json`.

# Original proof and alternative sources

Reviewed on 2026-10-24. **The main Lean theorem is still unproved.** This review
records the initial proof review; it is not a verification certificate. The broader
search and current reuse decision are documented in `CLOSURE_PLAN.md`.

## Sources and exact scope

| Source | Relevant result | Use in this development |
|---|---|---|
| Thomassen, *3-List-Coloring Planar Graphs of Girth 5* (1995), pp. 101–107, [DOI](https://doi.org/10.1006/jctb.1995.1027) | Arbitrary-list extension, Theorem 2.1; 3-choosability follows. | Original mathematical reference; all seven pages read directly from the uploaded PDF. |
| Nabiha Asghar, *Grötzsch's Theorem* (Waterloo, 2012), [essay](https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf), Chapter 3, printed pp. 37–52 | Theorem 3.2.1 is an arbitrary-list theorem, despite the essay's ordinary-colouring title. | Earlier provisional induction choice, now a cross-check. The chapter credits unpublished work of C. Nunes da Silva, R. B. Richter and D. Younger, inspired by Thomassen. |
| Z. Dvořák, *A simplified discharging proof of Grötzsch theorem*, [arXiv:1311.7636](https://arxiv.org/pdf/1311.7636) | Ordinary three-colourability of triangle-free planar graphs. | Useful structural reference; it does not supply our arbitrary-list extension. |
| Z. Dvořák, K. Kawarabayashi and R. Thomas, *Three-coloring triangle-free planar graphs in linear time*, [2008 preprint](https://kam.mff.cuni.cz/kamserie/clanky/2008/s887.pdf) | Ordinary three-colourability and a linear-time algorithm. | Its safe identifications require a separate argument for arbitrary lists. The introduction and initial structural reductions were reviewed, not all algorithmic details. |

The uploaded ZIP contains a valid scanned copy of the 1995 article. Its SHA-256 is
`688954ec7962f1b34c98df40d6c6a65e0d0e242fac2c34dc931d7f79554f10f7`.
The two earlier `.pdf` attachments were publisher security pages. The 2003
article has not thereby become an inspected original PDF. Full article scans
remain outside this source repository.

## What Thomassen's original proof actually does

Theorem 2.1, p. 102, considers a plane graph of girth at least five. A set `A`
of vertices incident with the outer face has lists of size at least two; all
other vertices have lists of size at least three. Either:

1. `A` is independent; or
2. the induced graph on `A` has exactly one edge `xy`, with a distinguished
   endpoint `x` having no simple two-edge path to another vertex of `A`.

Any prescribed proper list colouring of an outer-face edge `uw` extends.
The proof proceeds by a smallest counterexample and vertex deletion, rather
than vertex identification or a discharging argument.

Its numbered reductions have the following roles:

- (1)–(3): deal with small graphs, cutvertices and boundary chords.
- (4)–(5): exclude short interior paths by colouring one side, adjusting lists
  on the separator, and forcing agreement on the other side.
- (6): exclude separating five-cycles. Corollary 2.2 supplies extension from a
  fully coloured boundary five-cycle, using the same induction on a smaller
  graph; it must not be invoked circularly for the whole graph.
- (7)–(10): normalize the prescribed edge and eliminate the exceptional edge
  inside `A`. The exceptional state is needed in the induction even though a
  minimal counterexample eventually has independent `A`.
- (11)–(13): force a local boundary pattern; delete two or three coloured
  boundary vertices, or split along a short path, then invoke the induction
  and glue the colourings.

Thus proving that newly shortened lists are independent after deleting an edge
does not close the proof: old short lists can be adjacent to new ones. Both the
exceptional state and the geometry of the resulting pieces need justification.

## Earlier provisional choice of expanded induction

Asghar's Theorem 3.2.1 has consecutive singleton-list vertices `S`, two-list
boundary vertices `T`, no `S`–`T` edges, and three-lists elsewhere. Its simultaneous
states are: independent `T` with `|S| ≤ 5`; one `T`-edge with `|S| ≤ 3`; or a fully
precoloured outer cycle of length four through seven. Other cycles have length
at least five. Lemma 3.2.2 handles the blocks after deletion. Lemmas 3.2.3, 3.2.5
and 3.2.8 prove the three states. These chapter sections were read through the
completion of Theorem 3.2.1.

That proposed route retains these three states together. It does not assume that
every deletion preserves independence of `T`. Lists larger than three will
first be shrunk; empty and disconnected graphs require explicit treatment.

## Reuse and remaining implementation

The existing residual-list cardinality estimates and colouring glue remain
useful unchanged. `Thomassen/ThreeVertexDeletion.lean` now addresses the local
three-vertex deletion: loss of at most one colour and the simple three-edge
path forced by an adjacency between newly short lists. These assertions concern
vertices whose original lists have at least three colours, not old two-lists.

The registered Brooks package has a block-cut tree and block intersection
theorems. Their interfaces have been inspected, but no source from that package
has yet been imported. They can support the graph decomposition, while the
list and prescribed-colour conditions still need separate proofs.

The generic region separation and face-preservation arguments are now proved in
`Thomassen/RegionSeparation.lean`. The new `Thomassen/FaceBoundary.lean` proves that
face orbits do not repeat vertices under deletion connectivity, using the existing
Euler-defect machinery. Remaining geometric work includes instantiating those
results for each cycle-and-path cut and proving its exact boundary and induction
conditions. An `IsK5Boundary` certificate alone is not a substitute for these
outer-face facts. The block and list-state induction itself is also unfinished.

`BoundaryInstance` and its conditional assembly now again provide the selected
short-proof route, as explained in `CLOSURE_PLAN.md`. Its `BoundaryExtension`
property remains unproved. Asghar remains a cross-check; no replacement
three-state induction has been implemented. No axiom or conditional assembly
will count as closing the main theorem.


## 2026-10-25: final-deletion reading cross-checked against the short proof

The appendix of Jin–Kang–Steffen, arXiv:1502.04561, was reread through the
final boundary-list cases. In the short-fourth-list branch the original
prescription is retained while the first three **free** vertices are coloured
and deleted. An interior three-path adds its two interior vertices to that
deletion; it is unique by the absence of separating cycles of length at most six.
The new Lean development proves this uniqueness using actual face-permutation
preservation, and closes the entire branch for at most five prescribed vertices.

In the six-vertex mixed exceptions, the additional interior exceptional vertex
is coloured and **retained as a newly prescribed vertex** while two old endpoint
vertices are deleted. Treating this vertex as another deleted vertex was an
incorrect earlier reading and is not the route to implement. The five-vertex
replacement prescription can use the newly completed five-vertex strict case,
but its complete admissibility and residual-colouring proof is still pending.


## Six-vertex good-fourth exceptional deletion implemented

The retained-witness reading is now implemented for the good-fourth branch:
`SixVertexExceptionalGoodFourth` colours and retains the interior exceptional
vertex while deleting the two old endpoint vertices and the first two free
vertices. It derives every residual-list, prescription, component-face and
strict-cardinality condition. Its success does not discharge the distinct
short-fourth-list branch of the published proof.


## Final proof completion — 2026-10-25

The full short-proof boundary-extension induction and unconditional finite
3-choosability target are now proved. The final six-vertex short-fourth case
uses the previously verified connected branching prescriptions: independent
new short vertices attached to internal old prescribed vertices become pendant
branches with simple paths of at most five edges. The forced five-face is
coloured compatibly; girth excludes simultaneous prescribed neighbours at its
two adjacent interior vertices. This implementation keeps the original path
rather than needing the source proof's old-endpoint release in that branch.
All actual residual and component-face conditions are proved locally. Earlier
notes identifying this branch as open are historical checkpoints.

## 2026-10-25: low-effort byproducts — analysis only

No proposed byproduct was implemented in this step. The new Lean work in
`SingleBoundaryDeletion`, `ExceptionalDeletionLists`, `ExceptionalDistinctLists`
and `ExceptionalListNormalization` belongs to the existing Theorem 2.1 task.
Effort estimates include statement adapters, definition alignment and independent
contracts; they are relative estimates, not measured implementation times.

| Order | Candidate and exact scope | Reuse and missing work | Remaining effort / value |
|---:|---|---|---|
| 1 | Expose the short precolouring-extension statement attributed to Thomassen in Dvořák–Kawarabayashi (2011), Theorem 1. | The proved BoundaryExtension covers the induced-path invariant. ConnectedPrescription.colourable also allows proper chords in the prescribed connected set, whose at most six vertices bound every simple path. Write the exact source adapter and contract. | Very low; makes a strong reusable theorem discoverable. Source alignment and packaging, rather than a new underlying proof. |
| 2 | Infinite 3-list-colourability when every finite induced subgraph is planar of girth at least five. Each vertex has a finite list of at least three colours; the total colour type and vertex set need not be finite. | Use the proved finite theorem and Mathlib.Combinatorics.Compactness, Finset.rado_selection_subtype (line 91), with dependent finite types beta(v) = {c // c in L(v)}. Agreement on each two-vertex set proves properness. | Low; substantial scope extension using an already formalized compactness principle. No claim to implement an infinite plane-map definition or a new proof of Rado/de Bruijn–Erdős. |
| 3 | Extend a proper allowed colouring of any five- or six-cycle, including separating cycles, with three-lists elsewhere. | The current public corollary concerns an outer five-cycle, and extend_outer_short_cycle also covers an outer six-cycle. short_native_cycle_separation and glue_induced_colourings provide the two-side route for any such cycle; handle its component and three-colour the other components. | Low; useful for reducing separating cycles and for future critical-graph work. The outer versions are already proved and must not be counted again. |
| 4 | Outer seven-cycle list-precolouring extension, the girth-five specialization of Asghar (2012), Lemma 3.2.3. | Five- and six-cycle cases are available. A two-edge interior boundary path splits the seven-cycle into smaller rings; without such a path, delete two adjacent coloured boundary vertices and retain five singleton lists. Existing cuts, component faces and residual glue apply. The admissibility proof still has to be written. | Low–medium; a genuine extra ring size, not a direct alias of the six-vertex invariant. |
| 5 | Switching invariance and transfer to signed graphs with an explicit switching-to-positive certificate. | Jin–Kang–Steffen (2015), Proposition 1.1. Given vertex signs, transport lists by the bijections c -> epsilon(v)*c. The unsigned finite theorem then gives the 3-list result for this subclass. A minimal signed-colouring interface and transport lemmas are still needed. | Low–medium; reusable entry point to signed colouring. The full signed girth-five theorem, or the equivalence between cycle balance and a switching certificate, is a separate task. |
| 6 | Heredity of list-criticality across an S-component, Dvořák–Kawarabayashi Lemma 7, initially for induced separator pieces. | The colouring glue and exact no-crossing interfaces already exist. Criticality relative to a precoloured subgraph must be defined faithfully, distinguishing ordinary and strong criticality and edge-subgraph from induced-subgraph versions. | Low–medium after the definition audit; reusable structural infrastructure. Not the quantitative classification or linear bound from the paper. |

Ordinary three-colourability, monotonicity to larger lists and the finite
independence bound alpha(G) >= |V(G)|/3 are even cheaper consequences. They are
useful API corollaries, with little additional mathematical coverage, and should
be grouped into the same delivery rather than counted as separate papers.

The full signed theorem, correspondence colouring, weak two-degeneracy,
linear-time colouring algorithms, surface extensions and critical-graph size
bounds require additional arguments. They are
not justified as low-effort consequences of the current existence proof.
Dvořák's triangle-free precoloured-six-cycle result also permits four-cycles and
has its own validity condition; our girth-five cycle result does not establish
that stronger statement.

Reinspection sources:
- Dvořák–Kawarabayashi, arXiv:1109.2976, Theorem 1 and Lemma 7:
  https://arxiv.org/pdf/1109.2976 . Only the relevant statements and local
  criticality argument were reinspected in this step, not all 44 pages.
- Asghar, Theorem 3.2.1 and Lemmas 3.2.3/3.2.8:
  https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf .
  These were compared with the earlier source review; their full three-state
  induction is not an existing Lean dependency.
- Jin–Kang–Steffen, Proposition 1.1 and paper scope:
  https://arxiv.org/pdf/1502.04561 .
- Dvořák, arXiv:1311.7636, valid short-cycle precolouring setup:
  https://arxiv.org/pdf/1311.7636 .
- The current Mathlib source for Rado's dependent finite selection lemma was
  read locally. This is library reuse rather than another pending paper proof.
- A search result for a 2003 Thomassen PDF at KIT redirected to an unrelated
  department page on opening. It was not counted as a newly read original PDF.

### Quantitative candidate with shared algebraic infrastructure

Cranston, section 8.5 (Theorem 8.26 and Exercise 8.5), explicitly records the
Alon–Füredi route: once one allowed colouring exists, a polynomial grid bound
and planar edge bounds give at least `3^(n/6)` colourings from three-lists for
girth-five planar graphs, and at least `5^(n/4)` from five-lists for all planar
graphs. Both existence inputs are already in the author's program.
The shared new dependency is the quantitative nonvanishing-on-a-grid bound;
the existing Combinatorial Nullstellensatz is an existence theorem.

The GitHub plugin was used read-only to inspect
`jtraverso/alon-tarsi-choosability/README.md`, which identifies the graph
polynomial, colour injections into integers and Nullstellensatz infrastructure.
Targeted searches in the author's repositories and `LeanPool/lean-pool`, plus
local Mathlib searches, did not identify the required quantitative grid bound.
Füredi stability results found in Lean Pool concern Turán stability and do not
supply it. Search results do not establish exhaustive absence.

Estimate: **medium**, with potentially high reuse across the three-list and
five-list counting deliveries. It should be evaluated before porting a separate
long combinatorial counting proof; it is not yet justified as a trivial corollary.
No Alon–Füredi theorem or counting byproduct was implemented here.
Source: https://graphcoloringmethods.com/GraphColoringMethods.pdf , section 8.5;
only that section's bound, its proof outline and attribution notes were added
to the source review in this step. A 2022 paper search result could not be
opened (HTTP 403), so its full text was not treated as inspected evidence.
