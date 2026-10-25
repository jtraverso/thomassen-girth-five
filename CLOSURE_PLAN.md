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

# Exceptional-edge narrowing — 2026-10-25

The original Theorem 2.1 is **still not proved in full**. The new deletion
handles an endpoint colour absent from the other endpoint's list and preserves
actual faces in every remaining component, without assuming a simple old face
orbit. If a separated connected counterexample remains, its two exceptional
endpoint lists must be the same two-element set. This necessary condition is
proved; the nonexistence of that equal-list counterexample is not.
Eight new independent contracts pass Lean and NanoDa. All 171 solution modules
pass the source audit; the unchanged central main contract passes again.
Byproducts were analysed in SOURCE_REVIEW.md; none was implemented.

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

# Completion status — 2026-10-25

The complete six-vertex case, full `BoundaryExtension`, and unconditional
`PlanarChoosability.choosableWith_three_of_isPlanar` are now proved.
The original main comparator remains unchanged and accepts the proof with
NanoDa and the Lean default kernel. The root theorem has no extension or
removal hypothesis, covers arbitrary colour types and finite vertex types,
and uses extended girth to include forests and edgeless graphs.

The exact current proof is in `Thomassen/BoundaryExtension.lean`; the six-vertex
case is in `Thomassen/SixVertexPathClosure.lean`. Current verification is recorded
in `verification/main-comparator-complete.log` and
`verification/six-vertex-closure-comparator.log`. Earlier failed gates and
incomplete statuses below are historical checkpoints, not the current result.

# Broader proof search and closure obligations

Historical source comparison and checkpoint ledger (2026-10-24 to 2026-10-25).
The final six-vertex case and unconditional theorem are now proved. Earlier
open-obligation statements below describe their respective checkpoints.

## Sources screened

An exposition of a proof is not counted as an independent proof. A stronger
theorem is not treated as an available Lean dependency. This search makes no
claim to exhaust all publications.

| Source | Inspected scope | Assessment for the remaining formalization |
|---|---|---|
| Thomassen (1995), [original](https://doi.org/10.1006/jctb.1995.1027) | All seven uploaded pages. | Correct original extension argument, including the exceptional short-list edge documented in `SOURCE_REVIEW.md`. |
| Short-proof family: Jin–Kang–Steffen (2015), [Appendix, Theorem 5.1](https://arxiv.org/pdf/1502.04561), and Daniel W. Cranston, *Graph Coloring Methods* (2024), [§11.4, Theorem 11.13, printed pp. 322–328](https://graphcoloringmethods.com/GraphColoringMethods.pdf) | Relevant proofs through their final cases. The original 2003 publisher PDF remains uninspected. | Best match to our six-vertex invariant. Cranston expands the separator bookkeeping and the five-precoloured-vertex case. These are accounts of a common proof family. |
| Asghar (2012), [Chapter 3, Theorem 3.2.1](https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf) | Chapter through that theorem's proof. | Useful block-extension cross-check. Its three simultaneous states are not implemented here; adopting them requires a replacement invariant. Preserve the attribution recorded in `THIRD_PARTY.md`. |
| Dvořák–Lidický–Škrekovski (2010), [Theorem 3](https://kam.mff.cuni.cz/~bernard/pub/fc367.pdf), [DOI](https://doi.org/10.1137/080743020) | Main and technical statements, not every proof case. | Extends to certain graphs with four-cycles. Uses at most four precoloured vertices and allows a two-list vertex one neighbour in that path. Extra four-cycle cases increase the porting work. |
| Dvořák–Kawarabayashi (2011), [Theorems 1 and 3](https://arxiv.org/pdf/1109.2976) | Extension statements and proof setup. | Theorem 1 checks the intended induced precolouring conditions. The stronger theorem adds boundary configurations rather than removing the separation work. |
| Han–Wang–Wu–Zhou–Zhu (2023), [published Theorem 5 and Corollary 6](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i4p18/pdf/), DOI 10.37236/11749 | Sections 1–3, compared with [arXiv v1](https://arxiv.org/pdf/2303.07901); not the surface theorem. | Weak two-degeneracy implies our target through a modified greedy algorithm. The proof still needs blocks, chords and short paths, plus a legal-operation calculus. Use the published version: it specifies the adjusted function after removal of the prescribed path and expands the configuration figures. |
| Postle–Smith-Roberge (2022), [Theorems 1.7 and 1.13](https://arxiv.org/pdf/2108.03315), DOI 10.19086/aic.2022.8 | Statements, exceptional canvases and proof architecture; not all 38 pages. | Local girth choosability implies our target. Exceptional canvases and generalized wheels introduce further obligations. |
| Davies–Smith-Roberge (2025), [Theorems 1.11 and 2.8](https://arxiv.org/pdf/2504.21821) | Definitions, main theorem, canvas setup and main deduction; not the full 35-page proof. | Extends to local weak degeneracy and correspondence colouring. No reduction in our remaining effort has been established. |
| Dvořák–Postle, [correspondence colouring paper, §1.3](https://arxiv.org/pdf/1508.03437) | Discussion of the girth-five consequence and its proof route. | The authors obtain that consequence by adapting Thomassen. It does not give an independent shorter girth-five argument. |
| Bonamy–Delcourt–Dvořák–Kardoš–Postle, [*Islands in planar graphs*, Princeton seminar (2020)](https://www.math.princeton.edu/events/islands-planar-graphs-2020-03-05t200000) | Primary announcement and author attribution. | Announces discharging and Alon–Tarsi. A complete proof text was not located in this search, so the announcement cannot be a proved dependency. |

The earlier [Dvořák (2013)](https://arxiv.org/pdf/1311.7636) and
[Dvořák–Kawarabayashi–Thomas (2008)](https://kam.mff.cuni.cz/kamserie/clanky/2008/s887.pdf)
ordinary-colouring proofs remain structural references: identification needs
separate justification for arbitrary lists. Results restricting intersections
of neighbouring lists also do not cover every three-list assignment.

## Decision based on reuse

Retain the existing short-proof invariant and use Cranston's expanded exposition,
with the original and Asghar as cross-checks. This supersedes the provisional
choice to replace the invariant with Asghar's three simultaneous states. It is
an assessment of the existing code and missing dependencies, not a mathematical
ranking of the theorems.

The existing invariant, elementary consequences and exact target reduction can
be reused. A weak degeneracy port would additionally need its colouring
implication and deletion calculus. All inspected complete candidates still need
substantial embedding and boundary arguments.

## Gap addressed by actual code

`restrict G S` retains the original vertex type. Isolating vertices outside `S`
does not decrease `Nat.card V`; a vertex-count induction needs `G.induce S` on
the smaller subtype instead.

`Thomassen/InducedEmbedding.lean` now transports the actual darts, rotation,
Euler-defect certificate and face orbits to that subtype. It proves strict
cardinality decrease, girth inheritance and a bridge back to the existing `Col`
predicate used by `col_glue`. The explicit fallback in that bridge avoids adding
a nonempty-colour-type assumption to the target.

`Thomassen/InducedInstance.lean` also transports the prescribed walk, its edge
set and the complete instance to whole components. It proves the disconnected
case of the stronger extension induction, using only strictly smaller instances.
Vertices outside the component of the chosen face have three-lists. The isolated
complement case is handled directly, without requiring an outer dart there.

A union of whole components retains the original selected face. For an arbitrary
cut, the transported face is a face of the restricted map: relating it to the old
boundary still needs its own geometric proof. Arbitrary deletion is not asserted
to preserve the original face.

The subsequent `FaceRestriction.lean` now supplies that relation for a connected
retained subgraph: all its old face incidences project to one new face. The proof
uses the registered gap theorems to follow a face through chords and excursions
outside the subgraph. It asserts inclusion of face vertices, not equality of
faces. A connected boundary deletion also exposes every remaining neighbour of
the deleted set, if the remainder is connected.

`ConnectedInstance.lean` transports a specified exact prescribed intersection,
colours any proper induced set retaining the complete original prescription by
strict induction on its components, and restores low-degree unprescribed
vertices using the registered `col_of_erase`. `CutPrecolor.lean` constructs the
actual prescribed intersections for a cut through a prescribed vertex, including
the cycle case, and proves the full induction reduction at such a cutvertex.
The later `InteriorCutReduction.lean` also settles cutvertices outside the
selected face. Only unprescribed cutvertices on that face remain.

`CycleSeparation.lean` now constructs the two actual sides of a chordless cycle
from its two face orbits. It proves coverage, exact intersection, no crossing
edges, connectivity and the exact native face boundary of each induced side.
The old selected face lies on one side. `CycleWalk.lean` connects the indexed
cycle to the original native walk, including exact vertices and edges, proves
that girth-five cycles of at most six vertices are chordless, and obtains the
oriented strict cut when both open regions contain vertices.

`ShortCycleReduction.lean` completes the corresponding induction case. It
colours the side containing the old face, prescribes those colours on the whole
cycle in the other side, verifies every changed-list condition and glues. The
`NativeCycleSeparates` condition records actual vertices in both open face
regions. It is not an extension assumption. This case does not handle a facial
precoloured cycle with an empty region.

`ChordSeparation.lean` now constructs the actual boundary-arc/chord cut from
local equations of the original face, with no chordlessness assumption on the
whole graph. It removes the internal old arc from the exterior piece, proves
that no edge is lost and that the remaining separator consists of exactly the
two chord endpoints. Both native induced pieces are connected and strictly
smaller. `PrescribedChordReduction.lean` completes induction and gluing when
both endpoints are prescribed and every other prescribed vertex is retained in
the exterior piece. `EdgeCutPrecolor.lean` and `EdgeCutReduction.lean` now remove
that placement restriction. Paths split into their two branches at the actual
prescribed edge; a cycle lies in a side or meets it exactly at the two endpoints.
Each induced prescription preserves the original vertices, edges and bound of
six. The two strictly smaller instances retain their original lists and their
colourings agree at both singleton endpoints. Unprescribed ends remain open.

`InteriorCutReduction.lean` completes strict induction at cutvertices outside
the selected face. Face connectivity puts all original boundary vertices in one
cut side; the other side has three-lists everywhere. Colour the first side, then
prescribe its cut-vertex colour on an actual incident induced face of the other
side, invoke strict induction, and glue. This avoids any empty-colour-type
assumption. `cutvertex_constraints` proves that a remaining cutvertex in a
smallest counterexample must be unprescribed and on the selected face.

`FiveCycle.lean` and `FacialFiveReduction.lean` prove deletion and restoration
for the prescribed facial five-cycle. They also give the common deletion step
for cycles of at most six vertices without a shared exterior neighbour of the
chosen vertex and another prescribed vertex. `FacialSixReduction.lean` removes
that restriction: two consecutive opposite pairs with exterior common neighbours
would give a rooted K4 minor, and adding the registered face apex gives a
forbidden K5 minor. Thus another prescribed vertex can be deleted. If a boundary
vertex deletion disconnects the graph, the existing prescribed-cutvertex
reduction applies instead. The full facial six-cycle theorem consequently has
no extra shared-neighbour exclusion. Girth reduces all prescribed facial cycles
of at most six vertices to these two cases.

`FaceMerge.lean` proves that original faces incident with a connected omitted
set merge into one actual face of the connected retained graph, even when other
components are omitted too. `ArcPathSeparation.lean` extends the old-arc cut to a
connected path separator. It allows extra cycle chords with an old-arc endpoint.
Its exterior skeleton retains the cycle and all exterior components, with those
extra chords removed. The opposite cycle face is actual in that skeleton.
Deleting the arc merges that face with the selected original face. Since every
removed chord meets the deleted arc, the final induced graph equals the original
induced exterior piece. This proves separator exposure without assuming global
chordlessness or that arbitrary face restrictions preserve an old face exactly.

`CycleIntervals.lean` constructs connected intervals in the actual cycle graph,
proves their exact partition and uses girth five to exclude extra edges along a
separator of at most three edges. `NativeArcPathCut.lean` identifies that separator
with the actual suffix of the native closed walk. Both induced pieces are
strictly smaller, cover all original edges, and intersect in precisely that
native path. The inside boundary is the cycle, while the exterior embedding has
a selected face containing the whole separator and the remaining old boundary.
The old-arc face-corner equations remain explicit inputs; their occurrence in
all the remaining minimal-counterexample configurations is not assumed proved.

`ShortPathColouring.lean` completes the corresponding list-extension case when
the old prescription avoids the trimmed arc and every short arc list avoids the
separator. The smaller exterior graph is coloured first, then its separator
colours prescribe a native path of at most four vertices in the interior piece.
The proof checks every singleton list, original list bound, short-list edge and
agreement before gluing. The three-list-arc case follows automatically. Arcs with
short vertices adjacent to the separator still need the additional precolouring
and exceptional configurations of the paper.

`AugmentedPathColouring.lean` removes the earlier blanket exclusion of short
neighbours for two explicit cases. It independently colours extra short vertices
that each have at most one neighbour in the already coloured piece. The original
short-edge invariant proves their independence. It then verifies a new prescribed
native path with at most six vertices and every changed-list condition. For a
one/two-edge separator with an extra short vertex at each end, girth excludes all
internal chords and the old invariant excludes the endpoint chord. For a separator
of up to three edges with one extra vertex and a short opposite endpoint, the
same argument excludes the possible five-cycle chord. No compatible-colour or
chordlessness assumption is supplied in these two corollaries.
`NativeAugmentedPathCuts.lean` applies them to the actual face cuts. Capturing all
remaining old short neighbours and keeping the original prescription outside the
trimmed arc remain explicit case conditions; their universal availability is not
proved.

`CycleMapWalk.lean` converts an indexed cycle to a native simple cycle preserving
every vertex in order, by mapping the existing Mathlib cycle. `FaceOrbitCycle.lean`
constructs the actual indexed and native cycle of a selected face from its
permutation period. The previous face-injectivity theorem and registered
face-length lemmas supply simplicity and length at least three. It proves the
exact face vertex set, all original corner equations and equality of the root
dart. For a connected graph with at least three vertices, deletion connectivity
already implies the needed minimum degree two. This completes that boundary
normalization conditional on deletion connectivity. The subsequent fan induction
below removes the unprescribed boundary-cutvertex obstruction. Selection of the
remaining short-path cuts is still required.

The completed fan induction now supersedes the earlier cutvertex gap.
`BoundaryChordCut.lean` constructs a chord cycle from an actual boundary prefix,
proves all its old corners, finds a face vertex outside it and invokes the
verified strict separation. `FacialChordNormalization.lean` rotates the boundary
and obtains this cut at any nonconsecutive pair. Chords between two prescribed
vertices are consequently eliminated without supplying a separate arc witness.

`RootStar.lean` prescribes the root and every old short-list neighbour. Any allowed
root colour has compatible independent neighbour colours. If at most two such
neighbours remain, the star is a native path of at most three vertices and every
changed-list condition is proved. `RootStarCuts.lean` handles all cutvertices in
this auxiliary problem; `RootStarFan.lean` splits actual short-neighbour chords.
`RootStarExtension.lean` assembles these steps by a separate strong induction.
Its numerical bound `N` is explicit: the main extension hypothesis is applied
only to graphs of cardinality strictly less than `N`, and the auxiliary recursion
is on strictly smaller pieces. It does not assume fan extension or the main
result for the original graph.

`BoundaryCutReduction.lean` colours the side with the original prescription,
then applies that complete auxiliary induction to the smaller empty-prescription
side with its attachment colour fixed. There is no bound on the number of short
neighbours in that side. Together with the previously checked prescribed and
interior cases, this closes **all cutvertices**. It also closes cardinalities at
most two and proves that a smallest counterexample is connected, has at least
three vertices, has connected vertex deletions and has an actual native simple
facial boundary with the exact original corner equations.

`PrescribedCycleNormalization.lean` proves that a simple cycle contained in the
edges of another cycle has the same vertex set. Since prescribed chords are
eliminated, any prescribed cycle in a smallest counterexample must be exactly
the outer cycle. The previously completed facial five/six-cycle proof now closes
the **full prescribed-cycle case**, without an assumed facial placement.

The subsequent two-endpoint fan proof closes a further chord work unit.
`EdgeStar.lean` specifies the actual original-list colouring fixing both edge
ends and all old short neighbours. A native induced path on at most four vertices
supplies its base case. `EdgeStarCuts.lean`, `EdgeStarCutvertex.lean`,
`EdgeStarSpoke.lean` and `EdgeStarBoundary.lean` use the already checked one-root
fan and the actual arbitrary-position chord cuts. `EdgeStarExtension.lean`
assembles a complete second strong induction. No two-endpoint fan-extension
hypothesis is supplied; the main induction is invoked only below its explicit
strict bound.

`EdgeStarChoice.lean` extends any two allowed distinct endpoint colours to the
old short neighbours: girth excludes a neighbour shared by the ends, and the
original short-edge invariant excludes edges between the additional vertices.
`ReleasedEdge.lean` handles original singleton separator lists. When the separator
is not fully prescribed, one original endpoint list already has at least three
colours; the proof uses that finite palette to enlarge both endpoint lists. The
new piece has an empty prescription and retains every other original list.
After the fan theorem fixes the actual separator colours, the proof restores
both original endpoint lists. If both ends are prescribed, the previous complete
prescribed-edge-cut reduction is used instead.

`UnprescribedEdgeCut.lean` consequently closes cuts retaining the old prescription
in one side, with arbitrarily many short neighbours at the separator.
`UnprescribedBoundaryChord.lean` proves that a prescription avoiding both cut
ends lies on one side, and closes **all actual boundary chords with two
unprescribed ends**, without a supplied minimality or capture condition.
`EndpointChordCut.lean` proves the corresponding native-path placement at a
prescribed endpoint and closes that mixed chord case. A remaining chord must
meet an internal prescribed vertex and split the original path; this case is
still open. Short-path separators of two/three edges and the final deletion
cases are not asserted to follow from the two-endpoint fan theorem.

The mixed-chord reductions now go beyond prescribed endpoints.
`MixedPathPrecolor.lean` restricts the original native path at a mixed cut,
with exact retained vertices, exact edges and the original six-vertex bound.
`ReleasedLeaf.lean` turns a single private prescribed neighbour into a two-list
containing its original colour and its prescribed attachment's colour. The
separator roots receive three-lists, making a valid empty instance with every
short-edge invariant checked. Fixing the attachment colour then forces the
private neighbour's original colour. `MixedLeafCut.lean` applies the complete
edge-star induction, restores all original lists, and glues along the actual
separator. It neither discards a private singleton constraint nor assumes a fan
extension theorem.

`ShortPrescriptionChord.lean` splits the actual original path at the prescribed
separator end. If either branch has at most one edge, the reduction is complete,
even for prescriptions on five or six vertices. In particular **all boundary
chords for prescribed paths on at most four vertices are closed**. A remaining
mixed chord can occur only at branch lengths **(2,2), (2,3), or (3,2)**. This
classification is proved under the same strict main induction, rather than
inferred from an informal diagram. Those three central cases remain open.

`PrescribedPathOrder.lean` proves that a simple path using cycle edges cannot
reverse direction, because that would repeat its preceding vertex. In a
smallest counterexample the absence of prescribed chords makes the actual
prescribed native path follow one contiguous facial arc. The theorem records
every native vertex in order, for one of the two orientations. **The prescribed
outer-path alignment obligation is closed.** The bound on the unprescribed
complement, spliced-path corner equations, and the remaining short-path capture
arguments are separate obligations and remain open.

## 2026-10-25: complete boundary-chord step

The anchored-fan induction now supersedes the remaining central mixed-chord gap
recorded above. The unconditional main theorem is still unproved.

`AnchoredFan.lean` proves compatibility of a fixed root fan with the entire
original prescription and validates the bounded native-path base, preserving
every original singleton colour. `AnchoredFanCuts.lean` transports exact retained
prescriptions and verifies smaller cardinalities. `AnchoredFanSpokes.lean`
handles spokes whether they avoid, meet or split the prescription, as well as
cuts along prescribed edges. Empty spoke pieces reuse the already verified
two-endpoint fan theorem; no new fan-extension assumption is supplied.
`AnchoredFanCutvertex.lean` closes all cutvertices in this auxiliary problem.

`AnchoredFanBase.lean` and `AnchoredFanBoundary.lean` prove the actual normalized
facial case. Relevant chords are cut, so a prescribed path on at most three
vertices attaches to the root at an endpoint. Otherwise its middle would have
three distinct neighbours in the actual cycle graph. The root, old prescription
and possible additional short neighbour form a native induced path on at most
five vertices. `AnchoredFanExtension.lean` assembles a complete separate strong
induction. Every auxiliary call strictly decreases its own graph cardinality;
every call to the main boundary induction remains below the explicit bound `N`.

`AnchoredFanChoice.lean` chooses compatible star colours without releasing old
singletons. Girth implies that an external vertex has at most one neighbour on
a prescribed path of at most two edges. Thus the other cut piece's actual root
colour, proper at the shared prescribed vertex, avoids every prescribed
neighbour in the short piece.

`CentralChordCut.lean` colours that other piece, applies the complete anchored
fan to the short piece, and glues while retaining all original lists and
singleton colours. A prescribed path on at most six vertices has two branches
whose edge lengths sum to at most five; one branch therefore has at most two
edges. This closes **all three central cases (2,2), (2,3), (3,2)** without a
supplied minimal-cut or short-neighbour capture hypothesis.

`BoundaryChordReduction.lean` consequently closes **every actual boundary
chord**, for empty, path and cycle prescriptions. It strengthens the
minimal-counterexample normalization to an actual native facial cycle that is
chordless in the whole graph, with the original face vertices and corner
identities. The two/three-edge interior-path separators and final deletion cases
remain separate obligations.

## 2026-10-25: actual spliced-face cuts and prescription-free two-path arcs

`FacialPathSplice.lean` constructs the actual native cycle obtained by following
an old facial prefix and returning along an interior path. It proves simplicity,
length, exact separator suffix and exact old-arc support, and finds a vertex of
the old complementary arc outside the new cycle. Every internal face corner is
proved by equality of the actual old/new darts. The root dart is unchanged.

`InteriorFacePathCut.lean` now obtains the strict two induced pieces for an
actual one/two/three-edge interior closing path. Its inputs are the original full
facial cycle and the fact that the path's internal vertices are off that face.
There is no supplied spliced-corner or extra disjointness hypothesis. Coverage,
exact separator intersection, connectivity, strict vertex decrease, actual inside
face and separator exposure on the exterior face are all checked. The trimmed
arc is identified with the original native face interval.

`OptionalShortEnds.lean` handles zero, one or two original short-list neighbours
at the endpoints of a separator of at most two edges. With one extra neighbour
the augmented path has at most three edges, so it needs no short-list assumption
at the opposite endpoint. With two extra neighbours the previously checked
induced-path and compatible-colour arguments are reused. Longer lists stay
unprescribed.

`InteriorTwoPathSelection.lean` selects the first other incidence of the interior
vertex with the specified old facial arc. Girth forces its distance to be at
least three. This excludes every incidence of that interior vertex with the
trimmed open arc. Chordlessness of the original face captures the endpoint
incidences at just the two adjacent boundary vertices.
`InteriorTwoPathReduction.lean` closes the resulting **prescription-free facial
arc case** of a two-edge interior path. Minimality, spliced corners and short-list
capture are proved inside the reduction, rather than supplied as conditions.
A remaining two-path cut must meet the original prescription on that chosen arc.

This does not close cuts dividing the prescription, all three-edge separators,
the short outer-complement cases, or final deletions. In particular the full
Claims 5.1.5 and 5.1.6 and the unconditional theorem remain unproved.

## 2026-10-25: prescribed endpoint deletion with exact residual lists

`PrescribedEndpointDeletion.lean` proves the exact native prescription after
deleting the initial vertex of a prescribed path, including a singleton path,
whose remaining prescription is empty. Both retained vertices and edges are
checked on the actual smaller subtype.

The deletion theorem checks every residual-list condition. Old two-lists are
unchanged because the original invariant forbids their adjacency to the deleted
prescribed vertex. Other unprescribed lists lose at most one colour; newly
shortened lists are independent by girth. Neighbours of the deleted vertex and
old boundary vertices are exposed on an actual selected face of the induced
remainder. If deletion disconnects the graph, the completed prescribed-cutvertex
reduction applies. Cardinalities at most two are handled by the checked base.
The final colouring restores the original endpoint colour and all original lists.

Two geometric exclusions remain explicit in that deletion case: a newly
shortened neighbour must not meet the remaining prescription, and it must not
meet an old unprescribed two-list. These exclusions are not proved globally.
For a prescribed path on at most three vertices, the first exclusion follows
from girth automatically. Therefore the entire case with such a short prescribed
path and three-lists everywhere else is closed under the strict main induction.

A final obstruction lemma produces explicit vertices witnessing one of the two
remaining geometric conflicts in a smallest counterexample. This identifies what
must still be excluded or treated exceptionally; it does not assume away those
vertices. This checkpoint does not establish the full final-deletion argument or
the unconditional boundary-extension theorem.

## 2026-10-25: arbitrary subarcs, three-path reductions and endpoint conflicts

`FacialCycleRebase.lean` moves the initial native vertex along the same actual
facial cycle while retaining every vertex in order, every face corner and the
original face-permutation orbit. It also proves chordlessness for every such
native representative in a smallest counterexample.
`InteriorTwoPathSubarc.lean` identifies the old and rebased intervals exactly,
and applies the completed two-path reduction on any specified old facial subarc.
Consequently an interior vertex has at most one neighbour on a closed facial
arc whose open part avoids the original prescription.

`InteriorThreePathReduction.lean` uses that neighbour uniqueness to exclude
incidences of either interior vertex with the trimmed arc. With a short list at
the initial boundary endpoint, the original short-edge invariant excludes its
additional short neighbours. Only the other endpoint's adjacent old face vertex
can require precolouring. The proof handles both list-size alternatives there,
checks every changed list and glues on the actual three-edge separator. The
**prescription-free three-path case with a short initial endpoint is closed**,
including arbitrary old subarcs. No capture or spliced-corner hypothesis is
supplied. Cuts dividing the prescription remain separate cases.

`PrescribedEndpointTwoPath.lean` proves which old arc avoids the prescription
from the exact direction of its original native path. This excludes an interior
two-path from a prescribed endpoint to any distinct boundary vertex outside the
open prescribed path: unprescribed boundary vertices and the other prescribed
endpoint are both covered. A remaining interior common prescribed neighbour at
that endpoint must occur at native position **three or four**, and must be an
internal prescribed vertex. This classification leaves the corresponding
five/six-cycle cases open; it is not their proof.

`EndpointResidualConflicts.lean` therefore confines old-two-list conflicts to
the original boundary. In a chordless boundary with the first forward neighbour
prescribed and a three-list at the second backward neighbour, that old-list
conflict is excluded completely. Boundary shared-prescription conflicts would
force that three-list vertex to be prescribed. The remaining interior conflict
is impossible for prescribed paths on at most four vertices, by the position
classification. Thus **the first endpoint-deletion branch is closed for up to
four prescribed vertices with that concrete boundary/list pattern**, without
supplying either earlier geometric exclusion. For longer prescriptions, the
shared-prescription exclusion remains explicit in the deletion theorem.

Remaining work still includes short outer complements, cuts dividing the
prescription, other three-path cases, the classified five/six-vertex endpoint
configurations and final multi-vertex deletions. The unconditional main theorem
remains unproved.

## Closure ledger

| Work unit | Checked inputs | Still required |
|---|---|---|
| Normalize instances | Disconnected reduction; small-cardinality and low-degree cases; strict induction on proper induced sets; complete cutvertex reduction including unbounded short-neighbour fans; actual simple chordless native facial boundary in a smallest counterexample; original prescribed native path follows one contiguous facial arc. | Close the prescribed path's remaining short-outer-complement cases and residual-list conditions for multi-vertex deletions. Connected deletions can now be handled component by component without assuming their whole remainder connected. Its native facial-arc alignment is now proved. |
| Construct actual cuts | Concrete chordless-cycle separation; strict native short-cycle cuts; actual boundary-arc/chord cut allowing extra chords; actual native arc/path cuts of one to three edges, with exact intersection, strict decrease and exposure of the whole separator; native full-face cycles and actual chord cuts at arbitrary boundary positions; native face/path splices with proved old corners and unchanged root dart; actual strict cuts from one/two/three-edge interior closing paths. | Select the cuts dividing the prescription and remaining three-edge cases; native rebasing and exact subarc transport now cover the completed two-path and initial-short-endpoint three-path arc cases. |
| Invoke induction and glue | Complete cutvertex and separating-short-cycle reductions; chord reduction with prescribed endpoints and arbitrary placement of the remaining prescription; short-path reduction with the old prescription outside the arc and its short lists avoiding the separator (including the three-list-arc case); enlarged prescriptions on short paths; complete two-endpoint fans with arbitrary old short neighbours; edge cuts with one-sided prescriptions; complete anchored-fan induction retaining up to three old prescribed vertices; all mixed edge cuts and all actual boundary chords, including every central prescribed-path split; complete two-edge interior-path reduction when its chosen facial arc avoids the prescription, with internal selection and capture; arbitrary subarcs; three-edge prescription-free arcs with an initial short endpoint; endpoint-to-noninternal-boundary two-path exclusion. | Close two-edge cuts dividing the prescription away from its original endpoints and remaining three-edge interior-path cuts; handle the remaining exceptional six-vertex final deletions. |
| Finish the deletion cases | Residual cardinalities, edge-neighbour independence, three-vertex path witness; geometric exposure after connected boundary deletion with connected remainder. Separating short cycles are eliminated under strict induction. The full prescribed-cycle case is complete: prescribed chords reduce it to the checked facial five/six-cycle cases, including the exceptional shared-neighbour configuration. Prescribed-path endpoint deletion is proved with exact residual lists when its two explicit geometric conflicts are absent; for paths on at most three vertices and three-lists elsewhere no geometric exclusion remains. The concrete good-second-boundary-list deletion branch is closed for prescribed paths on up to four vertices, and old-two-list endpoint conflicts are localized and excluded under that boundary pattern. | The positions-three/four prefix cases and full good-second-list branch are now closed below. Resolve short outer-complement witnesses and the other short-boundary-list cases; handle old two-lists together with newly shortened lists and every remaining final deletion/precolouring exception, using the new component-wise connected-deletion theorem for disconnected remainders. The prescribed-edge short-second/good-fourth-list case, the alternating-list case, and all actual native facial cases with the first boundary edge prescribed are closed below. |
| Prove extension | The completed normalization and all reductions above. | An unconditional extension proof. The extension property cannot be supplied as an assumption. |
| Close the target | Existing conditional assembly and exact native main contract. | Define the unconditional `PlanarChoosability.choosableWith_three_of_isPlanar`, pass its independent comparison, then perform publication checks. |

The supporting-lemma count does not measure the portion of this ledger closed.
The actual main comparator remains the completion criterion.

## 2026-10-25: prescribed-prefix two-path cuts and the full first deletion branch

`CompatiblePrescription.lean` implements replacement prescriptions on a proper
induced piece. It retains its old prescribed vertices, checks compatible colours,
the native edge set, actual new face, every changed list and every short edge,
then invokes only the strict main induction. It supplies a reusable constructor,
not an extension assumption.

`PrescribedInteriorTwoPath.lean` resolves the interior positions-three/four cases
identified above when the prescription follows the forward facial order. The
actual cut has an inner prescribed cycle of five/six vertices and an exterior
replacement path on at most five vertices. An interior common neighbour has only
the two specified prescribed neighbours and no old unprescribed short neighbour.
Its three-list therefore supplies a compatible colour. Both pieces retain all
original singleton colours, satisfy the exact instance invariants and glue on
the original two-path. All cuts, incidences and strict cardinal decreases are
proved internally; no capture or replacement-colourability assumption is supplied.

The first forward boundary vertex being prescribed forces the whole original
native path to follow that direction. Consequently **no interior two-path joins
that prescribed endpoint to any other old boundary vertex**, including internal
prescribed vertices, in a smallest counterexample with that boundary pattern.

Combining this with the previously checked old-short-list conflict exclusion
closes **the good-second-backward-list endpoint-deletion branch for every
prescribed path on at most six vertices**. No shared-neighbour or old-short-list
exclusion is left as a hypothesis of that branch. A remaining counterexample
with the first forward boundary vertex prescribed must have a list of size at
most two at the second backward boundary vertex.

This does not settle all cuts dividing the prescription: cuts with no endpoint
of the original prescribed path and other three-path configurations remain.
Short outer complements and the remaining short-list and exceptional final
multi-vertex deletions still need proof. Unconditional boundary extension and
the actual main theorem remain absent.

## 2026-10-25: disconnected remainders and the short-second-list branch

`ComponentBoundaryDeletion.lean` flattens retained components and constructs their
actual new face after deleting a connected set containing the old facial root.
For a component retaining old face vertices, its last retained native index
supplies a forward old facial dart entering the deleted set. For a component
meeting no old face vertex, an interface edge supplies the new face. The checked
connected-omission face-merger theorem exposes all its neighbours of the deleted
set. **Connectivity of the entire remainder is not required.**

`ConnectedBoundaryDeletion.lean` restricts an exact retained prescription to each
component: its native path/cycle is either entirely retained there or absent.
It checks every residual singleton, two-list and short-edge condition on that
component, invokes strict induction, colours isolated vertices directly and
restores original colours by residual gluing. The general deletion theorem
keeps those local residual conditions explicit; it does not assume any extension
property or colourability of the retained graph.

`ShortBoundaryDeletion.lean` proves a complete new deletion case. With just the
first boundary edge prescribed, an interior vertex cannot have two distinct old
boundary neighbours. Native rebasing proves the old complementary arc free of
the prescription. If the second backward boundary vertex has a short list and
the fourth has at least three colours, delete the original prescribed endpoint
and the next two backward boundary vertices. The proof chooses compatible
colours, retains the exact singleton at the other prescribed endpoint, and
checks every residual list and short edge internally. Old/new conflicts use the
two-path exclusion; new/new conflicts use the completed short-endpoint
three-path cut. **This short-second/good-fourth-list branch is closed for a
prescribed edge, including arbitrary disconnected remainders.**

For a prescribed edge and an actual outer face on six vertices, the fourth
backward vertex is adjacent to the other prescribed endpoint and therefore has
at least three colours. Together with the earlier good-second-list branch this
closes that entire six-vertex outer-face case.

`ShortFaceCompletion.lean` upgrades any compatible colouring of an actual
outer cycle on at most six vertices to the checked full-cycle extension case.
For an edge prescribed on a five-vertex outer face, colour the middle
unprescribed vertex first. Its two neighbours have three-lists, so each can
avoid that colour and the adjacent prescribed colour. This closes the entire
**five-vertex outer-face case with a prescribed edge** as well. These assertions
concern the size of the outer face, not six prescribed vertices.

A remaining prescribed-edge counterexample with a short second backward list
and at least six boundary vertices must also have a short fourth backward list.
That alternating-list case was open at this checkpoint and is closed in the next
section. Other remaining obligations include
short outer complements for longer prescriptions, other prescription-splitting
two-path cuts, remaining three-path configurations, longer-prescription
short-list and exceptional final deletions, and unconditional boundary extension.
The actual main theorem is still absent.

## 2026-10-25: alternating boundary lists closed

`AlternatingBoundaryLists.lean` closes the alternating short-second/short-fourth
configuration. In fact, its main construction needs only the short fourth list
and at least seven boundary vertices. Write the consecutive backward vertices
as `a, b, d, e, w, g`, with the original prescribed edge joining `a` to its
forward neighbour `t`.

1. The original short-edge invariant gives three-lists at `b`, `e` and `g`.
   Choose a colour for `e` outside the old two-list at `w`, a colour for `d`
   different from it, and a colour for `b` different from the colours at `d`
   and the already prescribed `a`.
2. Prescribe the actual native path `e-d-b-a-t`, on five vertices. Every old
   singleton colour is retained. Add the colour prescribed at `e` to the old
   list at `w`, making that list have size three. This is the only enlargement.
3. Check every instance condition, including all new prescribed edges and
   avoidance of other old short lists. Rebase the actual old facial cycle at
   `e`, preserving its entire native support and face orbit. Its second backward
   neighbour is `g`, which has at least three colours.
4. Apply the previously verified good-second-boundary-list branch to this
   five-vertex prescription. Its only induction calls are on strictly smaller
   graphs. The colour added at `w` cannot occur there, because its adjacent
   vertex `e` has that same prescribed colour. Thus the resulting colouring
   respects every original list.

**The alternating prescribed-edge case is closed.** The six-vertex boundary
alternative is excluded directly by the original short-edge invariant. Combining
the new result with the checked good-fourth-list deletion closes **the entire
short-second-list branch with a prescribed edge**. Combining that with the
good-second-list branch and the five-vertex face gives
`colourable_of_prescribed_edge_native_face`: the full strict-induction case
for an actual native face whose first forward edge is prescribed.

No capture, list-colourability or extension hypothesis was added. The only
recursive hypothesis is the existing strict main induction. Remaining main-
theorem obligations concern longer prescriptions, their short outer complements,
other prescription-splitting cuts and exceptional final deletions, followed by
unconditional boundary extension and the actual main theorem. The alternating
configuration is no longer on that list.

## 2026-10-25: connected branching prescriptions and a one-vertex complement

The full prescribed-edge induction case now derives arbitrary-face placement
and either orientation using a proved mirror embedding. Mirroring also removes
orientation asymmetry in the free-arc three-path reduction with one short end.

The complete auxiliary theorem `connectedPrescription_extension_of_smaller`
extends connected prescriptions with no simple path longer than five edges,
only below its strict main bound. Clique retractions preserve the connected
prescription at its actual cuts. All cutvertices and prescribed boundary chords
are handled; the base constructs a native short path/cycle. A four-vertex
branching core proves the required bound even for arbitrarily many pendant
vertices. This auxiliary result is proved, not assumed as a replacement for
`BoundaryExtension`.

Its residual version handles all retained components after a boundary deletion.
The complete case with one unprescribed outer vertex now proves every residual
condition and invokes that auxiliary theorem. The original six-vertex path on
an outer seven-cycle is included, with no extra capture hypothesis. Thus the
one-vertex complement is no longer pending.

Two-vertex complements, prescription-splitting short paths, remaining
three-path configurations and exceptional final deletions are still pending.
The unconditional main declaration is absent, and the root comparator continues
to select it and fail. The 34 passing support contracts do not close that target.

## 2026-10-25: two-vertex complements and the full short-complement normalization

The two-vertex outer complement is now closed, including a six-vertex original
prescription on an eight-vertex outer face. Its complementary edge, unique
prescribed neighbours and compatible deleted colours are derived. Existing
edge-deletion girth lemmas supply independent new short neighbours; the verified
bound on neighbours of an eight-cycle supplies unique old attachments. Girth
excludes attachments at the original path endpoints. The proved branching
prescription induction then handles every remaining component.

The arbitrary-face corollary derives normalization, rebasing and orientation
internally. The zero-vertex complement is also excluded, since an endpoint of
an induced path on a cycle has a neighbour in its complement. Together with
the prior single-vertex result, all complements of size at most two are closed.
A remaining counterexample consequently has at least three free outer vertices,
and its native cycles satisfy `r.length + 4 ≤ p.length` for the original path.
This completes the short-complement step of the selected proof route.

The remaining obligations are prescription-splitting two/three-path cuts and
the exceptional final deletions, followed by unconditional boundary extension
and the actual main theorem. These obligations are mathematical proof work;
the passing 11-contract comparator is not a closure certificate for the main.

## 2026-10-25: interior two-paths with two prescribed ends closed

The remaining central configuration with two internal prescribed endpoints is
now closed: a six-vertex native path with a common interior neighbour at
positions 1 and 4 (numbered from zero). Its actual strict cut has an interior
five-cycle and an exterior five-vertex path. A new compatible-path-star lemma
retains all original singleton colours while independently colouring any old
short neighbours of the new internal vertex. It invokes the already proved
connected-prescription induction only below the strict main bound.

Native normalization is derived in either orientation of the original actual
face, using the checked mirror map. The endpoint exclusions now apply to the
arbitrary original face too; reversal retains the actual prescribed vertices,
edges and all lists. Girth excludes neighbour-index gaps one/two, so any
remaining pair of prescribed neighbours is exactly that central case. The
result `interior_prescribed_neighbour_unique` therefore eliminates all
interior two-paths with both endpoints prescribed under strict induction.

The unresolved two-path cuts now have one internal prescribed endpoint and
one unprescribed endpoint. Remaining three-path cuts and exceptional final
deletions are also open. Unconditional boundary extension and the actual main
statement remain unproved; the eight passing support contracts do not replace
the failing root main gate.


## 2026-10-25: the mixed two-path step is reduced to its published exceptions

The actual mixed prescribed/free two-path cut is now proved, with every face,
strict piece, old singleton, short-list attachment and separator colour checked.
The first piece retains a connected portion of the old prescription with its
original lists; the second fixes a path on at most five vertices and all short
leaves adjoining its two new adjacent vertices. Girth gives unique attachment
and a four-vertex branching core gives the auxiliary simple-path bound. The
proved connected-prescription induction is used strictly below the main bound.

Arbitrary-face normalization and reversal give both orientations and both ends.
An unprescribed boundary vertex cannot be adjacent to both prescribed ends.
Consequently every mixed two-path with two to five prescribed vertices is
eliminated. With six vertices, the only remaining possibilities are, with
zero-based native indices:

* `r[2]--u--b`, where `b` is adjacent to `r[0]`;
* `r[3]--u--b`, where `b` is adjacent to `r[5]`.

These are the selected proof's two exceptional configurations; their removal is
part of the final exceptional deletion work, not part of the proved cut step.
The two-path classification step (Appendix 5.1.5 for nontrivial prescribed paths)
therefore no longer needs a general mixed-cut proof. Uniqueness on the whole
unprescribed facial complement also proves at most two total boundary neighbours
of an interior vertex for prescriptions on at least three vertices.

Next mathematical obligations are the remaining interior three-path reductions
and final deletions, handling the above exceptions concretely. Unconditional
boundary extension and the actual main theorem remain absent. The 16 passing
support contracts do not replace the unchanged failing root main comparator.


## 2026-10-25: structural three-path exclusions proved; final deletion remains

The three-path step for nontrivial prescribed paths is now proved whenever the
free endpoint has an old short list, or the other endpoint is one of the two
prescribed endpoints. This includes arbitrary original faces, both directions,
and cuts splitting the prescription. For a mixed cut, select an end containing
at most three old prescribed vertices; the replacement path has at most six
vertices. Its two ends have old short lists, and its two new interior vertices
are adjacent. All additional old short neighbours become independent leaves;
the previously checked connected-prescription induction applies only below the
strict main bound. Actual face exposure, allowed colours and gluing are proved.

The residual deletion with a short second backward list and a three-list at the
fourth backward vertex is additionally proved for prescriptions on two to five
vertices. Boundary-neighbour uniqueness excludes new residual conflicts, while
the entire original prescribed tail is retained with its singleton colours.
The residual set is checked through the existing connected-prescription and
actual component-face machinery, without a connected-remainder assumption.

The remaining final cases are substantive:

* Short fourth backward list with a longer prescription. The interior
  three-path between the first and third free vertices can have two unrestricted
  free three-list endpoints; that configuration is retained, not excluded by
  the new structural theorem. Its coloured deletion and any vertices meeting
  two deleted vertices need a concrete admissibility proof.
* Six prescribed vertices. The good-fourth branch still needs its exceptional
  mixed two-path handled by colouring/deleting the additional interior vertex
  and prescribed end segment. The complementary six-vertex exceptional final
  deletion also remains unproved.
* Complete the strong extension induction and its starting states, then apply
  the already checked conditional assembly to the actual main declaration.

The 13 three-path contracts plus two deletion contracts pass Comparator, Lean
and NanoDa, with no definition holes. The root main comparator remains unchanged
and fails because the unconditional declaration is absent. These supporting
results do not establish unconditional boundary extension.


## 2026-10-25: residual counterexamples have four to six prescribed vertices

The three-vertex prescribed-path case is fully closed under strict main
induction. Its short-fourth-list branch fixes a compatible native boundary path
on six vertices and restores the sole enlarged short list through adjacency.
The six-vertex outer face is coloured compatibly; the seven-vertex alternating
alternative violates the old short-edge invariant. Actual face normalization,
mirroring and all remaining boundary-list branches are proved.

The good-fourth deletion is extended to all six prescribed vertices when its
backward exceptional two-path is absent. A proved classification gives the exact
remaining six-vertex configuration if that branch is a counterexample. For the
exceptional five-cycle, short separating-cycle induction and actual facial
corners force the first two prescribed vertices to have only their cycle
neighbours. This local geometry is established, but the residual colouring after
the exceptional deletion is not yet proved.

Current-cardinality small-star extension now follows from the complete edge and
three-vertex cases, retaining only strict calls to the main induction. It closes
the empty prescription (including the all-three-lists branch after thinning one
actual boundary list), and the singleton prescription by adding the fixed
neighbour's colour and forcing restoration through properness. Thus all starting
states are closed. Together with the previous full cycle reduction, a new exact
counterexample theorem leaves only a native path on four to six vertices.

Remaining work is the short-fourth-list deletion for those longer paths, the two
six-vertex exceptional deletions, then assembling unconditional boundary
extension and the actual main theorem. The unrestricted free three-list endpoint
configuration remains part of the final deletion; it is not claimed excluded.
The 19 new passing contracts and 131 hole-free solution modules do not replace
the unchanged failing root main comparator.


## 2026-10-25 — Four- and five-vertex prescribed-path cases closed

`FiveVertexPathClosure` closes every nontrivial prescribed native path on at
most five vertices under only the strict main induction hypothesis. It covers
the original arbitrary selected face and both orientations. Consequently
`remaining_counterexample_has_six_prescribed_vertices` proves that all remaining
counterexamples prescribe exactly six vertices. Empty and singleton states,
edges, smaller paths and all permitted cycle prescriptions were already closed.

The proof first deletes only the three free boundary vertices when no interior
three-path joins the first and third. If that path exists, the inner side of
its five-cycle is empty by the separating-short-cycle reduction. A chordless
empty side preserves its actual original face permutation. Any second short
closing path across the same old facial prefix has the same support and length;
this proves uniqueness of the three-path and excludes the four-edge detours.
The middle free boundary vertex has exactly its two cyclic neighbours.

Interior attachments outside that forced five-face are independent. An
attachment cannot also meet an old free short list or an old prescribed endpoint.
Translating the existing five-cycle neighbour lemma shows that deleting the
coloured cycle removes at most one colour from each outside vertex. Explicit
compatible colours preserve every old short list. All remaining new short
neighbours of the old prescription are coloured as independent pendant vertices,
without bounding their number. The previous connected-prescription and actual
component-face machinery extends them using only strictly smaller instances.

The twelve new modules introduce 22 theorem contracts and no new definitions.
The independent challenge imports only `Thomassen.LongPrescriptionReduction`,
not any new proof module. Strict solution and axiom-audit builds pass, with only
propext, Classical.choice and Quot.sound; the source audit covers 143 solution
modules without proof holes, custom axioms or native_decide.

Remaining: the six-vertex final deletions, including the two mixed exceptional
configurations, then the full strong induction and unconditional main assembly.
The root main comparator remains fixed on the actual main theorem. No publication
or Palomar submission is made for this incomplete main result.

### Next concrete six-vertex reductions

1. Generalize the free-path/five-face residual argument to a six-vertex
   prescription when the two concrete mixed exceptions are absent. Newly short
   leaves lie off the old face, so the proved interior prescribed-neighbour
   uniqueness supplies their unique parent even for a five-edge prescribed path.
2. In the backward mixed exception, colour the interior exceptional vertex and
   **retain it as prescribed**. Delete the two old endpoint vertices of the
   exceptional facial prefix together with the free vertices selected for the
   final deletion. Its exact endpoint neighbourhoods are already proved. The
   surviving four old prescribed vertices plus the retained interior vertex
   form a five-vertex replacement path, whose closure is now available.
3. Handle the complementary mixed exception in the short-fourth case with only
   three free outer vertices; the published proof instead releases the opposite
   two old endpoint vertices. Derive the actual faces, exact residual lists,
   proper replacement prescription and strict cardinality before invoking it.

These are proof obligations, not assumptions added to BoundaryInstance or to
the actual main theorem. The two exceptions remain unresolved.

The 22 contracts pass independent statement comparison, NanoDa and the Lean
default kernel (`verification/five-vertex-closure-comparator.log`). Strict
solution/axiom builds and the 143-module source audit also pass. The unchanged
root comparator still fails on the absent unconditional main declaration
(`verification/main-gate-after-five-vertex-closure.log`); it is not replaced by
the supporting-case contract.


## 2026-10-25 — Six-vertex good-fourth branch and nonexceptional branch closed

The complete six-vertex case remains **unproved**. The progress below closes
two substantive branches and isolates precisely what is still missing.

`SixVertexExceptionalGoodFourth` closes the backward mixed exception when the
fourth backward boundary list has at least three colours. Write the original
prescription as `r₀,...,r₅` and the first two backward free vertices as `b,d`.
For the interior witness `u` adjacent to `b,r₂`, delete `r₀,r₁,b,d` and retain
`u` as a newly fixed vertex. The replacement prescription is the four old tail
vertices `r₂,...,r₅` plus `u`. The previously proved short-cycle saturation makes
`r₀,r₁` degree-two vertices with their exact neighbours. Outside the retained
tail, the residual lists equal those from deleting only the edge `bd`, so the
registered edge residual bounds and independence theorem apply. Old free short
lists stay unchanged; all new singleton-list conflicts are captured and coloured
compatibly. Actual remaining components and exposed faces use the previous
connected-deletion machinery. No list-size upper bound is imposed on `u`.

`ConnectedResidualPinning` generalizes that machinery to allow fixed residual
vertices with more than two colours. Its explicit short-edge premise accounts
for their new singleton lists, rather than assuming they were already short.
`SixVertexGoodFourthClosure` combines the new exceptional proof with the old
nonexceptional reduction. Hence **every** good-fourth-list case for a six-vertex
prescription is now closed, including the mixed exception.

The five previous free-deletion and residual-prescription proofs are generalized
to six prescribed vertices under the concrete property that every interior
vertex has at most one old boundary neighbour. Unique parents for new short
leaves now come from the proved interior prescribed-neighbour theorem, rather
than the earlier at-most-five-vertex index bound. This handles both deletion of
three free vertices with no interior three-path, and deletion of the entire
forced inner five-face when that path exists. The native-face assembly closes
the entire six-vertex case under this incidence property.

`SixVertexRemainingExceptions` uses the old exact boundary-pair classification
to remove that incidence property from the residual classification: any remaining
counterexample has short second and fourth backward lists and an interior
witness adjacent either to `r₂` and the first backward free vertex, or to `r₃`
and the first forward free vertex after `r₅`. Both configurations may coexist;
no exclusivity is claimed. Their final **short-fourth-list** deletions are still
unproved. The good-fourth exceptional case is no longer pending.

The 12 new theorem contracts have a separate challenge importing only the
preceding `FiveVertexPathClosure` stage and none of these ten new proof modules.
Strict solution and axiom-audit builds pass. The source audit covers 153 solution
modules with no proof holes, custom axioms or native_decide. The actual main
comparator remains fixed on its unconditional target. No publication or Palomar
submission is made for the incomplete main theorem.

All 12 contracts pass independent statement comparison, NanoDa and the Lean
default kernel (`verification/six-vertex-progress-comparator.log`). The challenge
imports none of the ten new proof modules. The strict solution/axiom build and
153-module source audit pass. The root comparator remains unchanged and still
fails on the absent unconditional main declaration; the complete six-vertex
case is not claimed solved by these supporting checks.


## 2026-10-25 — Complete six-vertex case and unconditional main theorem

`SixVertexAlternatingFreeDeletion` eliminates the short-fourth-list case when
no interior three-path joins the first and third free vertices. It retains the
entire old prescription, permits newly short vertices attached to its internal
vertices, and fixes them as independent pendant branches using the already
proved unique-parent residual extension. No mixed-incidence exclusion is assumed.

For the remaining three-path, `SixVertexFiveFaceAttachments` excludes edges from
new interior attachments to old free short lists and to either original prescribed
endpoint. It uses the free-boundary two-path and endpoint three-path reductions,
allowing the mixed internal-prescription attachments. `SixVertexFiveFaceDeletion`
then derives all residual list bounds, independent short leaves, their unique old
parents and actual smaller component faces.

`SixVertexFiveFaceColouring` supplies explicit colours for the entire forced
five-face. Its two interior vertices can meet the old prescription only at the
second and third internal prescribed vertices, respectively. They cannot both
have those neighbours: the two old prescribed vertices are adjacent and would
form a four-cycle. Colour the constrained interior vertex first, then the other;
each has at least three colours. Together with the boundary colour choices this
preserves every original singleton and short list. The mixed exceptions are
therefore included, without deleting old prescribed endpoint segments.

`SixVertexPathClosure` assembles both alternatives and transports them to the
original arbitrary face and either orientation. The theorem takes only the
strict smaller-cardinality main induction hypothesis. It has no mixed-exception,
uniqueness-of-boundary-neighbours or additional extension assumption.

`boundary_instances_colourable_at_card` closes strong induction over all finite
vertex types: every hypothetical remaining counterexample has the now completed
six-vertex path. `boundary_extension` is consequently proved for every colour
type. Applying the previously checked definition-preserving assembly yields the
exact original unconditional main theorem.

The original main comparator accepts that theorem, with NanoDa and Lean default
kernel acceptance. The nine new closure contracts include the full arbitrary-face
six-vertex case, global extension and unconditional target. Their independent
challenge imports only the preceding stage and the assembly definitions, none of
the six new proof modules. The solution audit contains 159 modules without proof
holes, custom axioms or native_decide. No unresolved mathematical case remains
for the stated finite girth-five 3-choosability target. Publication and registry
submission are separate from this local proof completion.
