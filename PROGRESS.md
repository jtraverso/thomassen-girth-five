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

## Historical development ledger

# Scope and remaining proof

Status: **in progress. The main theorem and the boundary-extension theorem remain unproved.**

The 33 supporting contracts passed independent comparison (the original 26 plus
seven three-vertex deletion lemmas). The boundary invariant has 14 further
kernel-checked lemmas, plus two explicitly conditional assembly lemmas. None of
these proves a list-extension theorem.
No new repository or registry entry has been created for this unfinished result.

## Target

In namespace `PlanarChoosability`, using the exact existing definitions:

```lean
theorem choosableWith_three_of_isPlanar {V : Type*} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : ChoosableWith G C 3
```

This is a target signature, not an available theorem. The finished signature must
not add a boundary-extension assumption, a removal hypothesis, degree bounds, or
an assumption of ordinary 3-colourability. The arbitrary colour type and empty
vertex-set cases must be retained. Extended girth includes forests.

## Completed support

- `Thomassen/Girth.lean`: native girth/cycle bridge, inheritance by subgraphs,
  no triangles, uniqueness of a common neighbour, and independence of the
  remaining neighbours of an edge.
- `Thomassen/Lists.lean`: residual finite lists, cardinality loss bound, unchanged
  lists away from deleted neighbours, and gluing into the existing `Col` predicate.
- `Thomassen/Minimal.lean`: bridge from that partial-colouring predicate to native
  list colourings, vertex extension through existing `col_extend`, minimal bad
  vertex sets, their degree bound, and connectedness through existing `col_glue`.
- `Thomassen/ShortLists.lean`: deletion of a coloured edge leaves at least two
  colours from every three-list, and its newly shortened lists are independent.
- `Thomassen/Boundary.lean`: the remaining old boundary together with neighbours
  exposed by deleting an edge is still a K5-minor-free boundary; reuses two
  applications of `isK5Boundary_delete`.
- Rebuilt the existing face-apex construction, facial-cycle theorem, and region
  separation module against this local base. They supply map restriction, gap
  allocation to faces, separation of components, and chord geometry.

The original five support modules contain 26 lemmas. Their number does not measure the
fraction of the main theorem completed. Most of the paper's induction remains.
The independent comparator configuration explicitly lists its selected scope.

## Earlier short-proof route: obligations still open

Use the short precolouring-extension argument, as reproduced in Jin–Kang–Steffen,
Theorem 5.1, specializing to unsigned graphs:

1. Prove the extension property for the now-formalized `BoundaryInstance`.
   `Thomassen/Instance.lean` specifies the actual outer face orbit, a precoloured
   path or cycle of at most six vertices, singleton proper precoloured lists,
   two-list boundary and three-list interior bounds, and the exact allowed
   short-list edge set. Its structure has no extension or colourability field.
2. Establish the minimal-counterexample normalization: connectedness and
   2-connectedness for this stronger invariant. The fixed-list connectedness lemma
   above is a tool; it does not by itself prove normalization when lists change.
3. Prove the chord and short interior-path reductions, including both exceptional
   configurations when the precoloured path has six vertices. Use the imported
   regions/Jordan lemmas to justify each separation and induced outer boundary.
4. Prove that short separating cycles can be coloured outside first and then
   inside. This needs the same stronger induction, not just ordinary colouring.
5. Execute the final boundary deletion cases, track residual lists and the
   independence of size-two lists, and show that every resulting part has an
   admissible precoloured path with at most six vertices.
6. Supply the proved extension theorem to the conditional assembly in
   `Thomassen/Assembly.lean`, then add the actual unconditional theorem and perform
   independent statement comparison and the publication preflight. The assembly
   and edgeless case are now checked, but the needed extension proof is absent.

There is no proof of the extension theorem in this checkpoint, and no theorem
assuming that extension is presented as the desired result. The old five-list
proof and the ordinary Grötzsch theorem do not imply arbitrary three-list
colourability. The remaining effort is higher than adapting a theorem interface.

## Verification checkpoint (2026-10-24)

- Strict solution and axiom-audit builds passed.
- Independent supporting contracts: **26 theorem types and 11 definition bodies**
  accepted by Comparator, Lean and NanoDa. `verification/support-comparator.log`.
- The ten original theorem contracts also passed in the initial combined check
  with the first 25 new lemmas. `verification/comparator-initial-35.log`.
- Source reuse audit covers 74 Lean files: 61 byte-identical, 12 changed only in
  imports/blank lines, and one changed additionally by renaming two unused bound
  variables. `verification/source-reuse.json` contains file hashes and the method.
- The actual main gate **failed**, as required for this unfinished checkpoint:
  the three-choosability theorem is absent from the solution environment. Its
  exporter reports a missing-constant panic; this is not a network failure.
- No publication or Palomar submission has been performed for this result.

## Subsequent attempt to close the proof

Added `Thomassen/Instance.lean` and `Thomassen/Assembly.lean`. The invariant uses
native simple paths/cycles and the exact edge set of the prescribed subgraph.
The outer boundary is defined through the existing plane map's face permutation.
Proved its elementary consequences and the base case in which every vertex is
already prescribed. Proved that a successful list colouring extends all
prescribed singleton colours.

`BoundaryExtension` is a **definition of the still-open obligation**, with no
axiom or instance supplying it. The two assembly lemmas take that property as an
explicit hypothesis. They establish the reduction to the exact original
3-choosability statement, including arbitrary colour types and edgeless graphs;
they do not establish the unconditional theorem.

Strict builds and the expanded axiom audit passed. Replayed the 14 invariant
lemmas and two conditional assembly lemmas through the Lean and NanoDa kernels,
using `scripts/check-assembly.py`. This replay does not independently compare
mathematical statement definitions; its scope differs from the original support
comparator. Logs: `verification/assembly-strict-build.log` and
`verification/assembly-kernels.log`.

The main comparator was run again after importing the assembly into the solution.
It still fails with the unconditional theorem missing. The full extension
induction (connectivity reductions, chords, short interior paths, exceptional
six-vertex configurations and final deletion) has **not** been completed. This
attempt did not close the user's requested main formalization. No publication or
registry submission is justified by the conditional assembly.

## Original article and alternative proof review (2026-10-24)

The user supplied the complete original 1995 article and three alternative
references. The original seven-page scan was read directly. See `SOURCE_REVIEW.md`
for source provenance, exact scopes and attribution. The selected organization
is now the expanded simultaneous induction of Asghar's Chapter 3, Theorem 3.2.1.
The earlier six-vertex `BoundaryInstance` is retained as checked support, not
identified with the new three-family invariant or declared solved.

The newly completed local reduction is `Thomassen/ThreeVertexDeletion.lean`:

- A newly short residual list has a neighbour in the deleted set.
- After deletion of a simple two-edge path, every remaining vertex loses at
  most one colour, hence every original three-list retains at least two.
- An adjacency between newly short residual lists must connect neighbours of
  opposite endpoints of the deleted path.
- It therefore gives a native simple three-edge path between those endpoints,
  avoiding the deleted middle vertex. Excluding such paths makes newly short
  lists independent.

These seven lemmas reuse the existing residual-list estimates, triangle/four-cycle
exclusions and edge-neighbourhood lemma. They do not assert that old two-lists
remain independent of the new ones. Handling that interaction is part of the
one-exceptional-edge induction state.

Validation: strict audit build passed; independent Comparator checked all 33
supporting theorem types and 11 complete definition bodies; both Lean and NanoDa
accepted the solution. Logs: `verification/three-vertex-strict-build.log`,
`verification/three-vertex-challenge-build.log`, and
`verification/three-vertex-comparator.log`. The solution introduces no new axioms.

The next proof work is to implement the three simultaneous extension states,
use the registered block-cut tree infrastructure with the changed list conditions,
and construct the plane-map separations for chords and short interior paths.
The full main theorem is still absent. There has been no publication or Palomar
submission for this unfinished development.

## Geometric separation checkpoint

Added two proof modules, reusing the registered rotation-system infrastructure:

- `Thomassen/RegionSeparation.lean` (15 lemmas): assigns components outside a
  connected subgraph to its actual face orbits; builds two sides from the face
  regions; proves coverage, exact boundary intersection and absence of crossing
  edges; and transports face permutations and orbits under edge deletion when
  the relevant gaps contain no additional kept dart.
- `Thomassen/FaceBoundary.lean` (two lemmas): proves that two darts on one face
  with the same tail coincide if deleting that tail leaves its neighbours
  connected; derives injectivity of the tail map on every face orbit from native
  deletion preconnectedness. The proof adapts the registered cycle-facial
  rotation-splitting argument and uses Euler-defect nonnegativity.

The generic two-side construction has explicit hypotheses about the face orbits
of the cutting subgraph: the three representative faces, preservation of the
outer face, and incidence of each retained edge with a chosen side. These are
geometric assertions, not colouring assumptions. They still need proofs for the
specific cycles, chords and short paths used in the paper. The new normalization
lemma also requires deletion connectivity; it does not itself prove that a
minimal list-extension counterexample has that property.

`ThomassenGeometryChallenge.lean` imports only the shared registered geometry,
not the new Thomassen proof modules. It independently specifies the seven
selected geometric assertions and the three new definition bodies.
`comparator.geometry.json` passed Comparator, Lean and NanoDa. The unselected
helper lemmas occur in the checked proof dependencies. Strict audit builds
passed with only `propext`, `Classical.choice` and `Quot.sound` in the axiom audit.
Logs: `verification/region-separation-strict-build.log`,
`verification/region-separation-challenge-build.log`, and
`verification/region-separation-comparator.log`.

**The requested full formalization has not been closed.** Neither the three-family
Asghar induction nor the older `BoundaryExtension` property has a proof in this
checkpoint. The concrete cut instantiations, block induction with prescribed
colours and old short lists, and the final deletion cases remain. The main
theorem is absent; no publication or Palomar submission has been performed.

## Broader proof survey and smaller-instance induction

The new review is in `CLOSURE_PLAN.md`. It distinguishes complete proofs and
expositions from ordinary-colouring results and an islands announcement for which
no complete manuscript was located in this search. The existing six-vertex
`BoundaryInstance`, using Cranston's expanded exposition, is again the chosen
route. This supersedes the earlier provisional Asghar three-state organization;
no replacement three-state induction was implemented.

`Thomassen/InducedEmbedding.lean` adds 17 lemmas and three constructions. It
identifies darts of an ambient restriction with darts on the actual induced
vertex subtype, transports the rotation and Euler-defect certificate, proves
exact face-orbit transport, girth inheritance and strict vertex-count decrease,
and connects induced list colouring to the existing `Col` interface. Whole
components preserve the original face; arbitrary induced restrictions are not
claimed to do so. An explicit fallback avoids imposing a nonempty colour type.

`Thomassen/InducedInstance.lean` adds six lemmas and two constructions. It lifts
the prescribed native walk, preserving its path/cycle property, vertex bound and
edge set, then transports every boundary-instance condition to whole components.
It proves that vertices outside the chosen face's component have three-lists,
and completes the disconnected case of the extension induction using only
strictly smaller instances. The edgeless complement is coloured directly.
The connected extension case is still unproved.

Strict audit builds passed. `comparator.induced.json` compared nine theorem types
and four definition bodies against a challenge over registered prerequisites.
`comparator.instances.json` compared six theorem types and two definition bodies;
its challenge imports the previously checked instance and induced-embedding
prerequisites, but not the new instance-transport proof module. Both solutions
passed Lean and NanoDa with only the three standard permitted axioms.
Logs: `verification/induced-embedding-comparator.log`,
`verification/induced-instance-strict-build.log`, and
`verification/induced-instance-comparator.log`.

The actual main comparator still fails because the unconditional theorem is
absent. The outstanding work is now cutvertex normalization, concrete
cycle-and-path cuts and boundary transport, and all list-extension deletion
cases. **The main theorem and `BoundaryExtension` remain unproved.** The source
survey and passing support checks do not establish the main theorem. No
publication or Palomar submission has been performed.

## Connected-piece transport and prescribed cutvertices

Continued from local commit `eb86472`. The actual main theorem is still absent;
this checkpoint does not close the requested full formalization.

Three new proof modules complete the following reductions:

- `FaceRestriction.lean`: original face incidences project to a face of any
  connected retained subgraph, using the registered chord/component gap
  theorems. This allows merging faces. For a connected set deleted through an
  edge of the old face, all remaining neighbours of that set lie on the new
  face, provided the remainder is connected. These are proved geometric
  assertions, not face-preservation assumptions.
- `ConnectedInstance.lean`: construct instances on connected induced pieces
  with an exact specified prescribed intersection. Native connected components
  give strict induction on any proper induced vertex set retaining the whole
  prescribed walk, even for disconnected remainders. A vertex outside the
  prescription with fewer neighbours than colours can then be restored using
  `col_of_erase`. Induced colourings agreeing on a separator glue on the actual
  graph, with every original edge accounted for.
- `CutPrecolor.lean`: construct the exact prescribed path/cycle on a cut side
  containing a prescribed cutvertex. Paths split into prefixes and suffixes;
  a rotated cycle with its repeated final vertex removed gives the cycle case.
  A disconnected native vertex deletion supplies two proper connected sides.
  Applying strict induction to the actual instances and using the singleton
  colour of the separator completes the precoloured-cutvertex reduction.

There are 19 new public lemma contracts and five complete definitions in
`comparator.connected.json`. `ThomassenConnectedChallenge.lean` imports the
previously checked `Thomassen.InducedInstance` prerequisites, but none of these
three new proof modules. Strict audit and Comparator, Lean and NanoDa checks
passed. Only `propext`, `Classical.choice` and `Quot.sound` are used.
Logs: `verification/connected-reductions-strict-build.log`,
`verification/connected-reductions-challenge-build.log`, and
`verification/connected-reductions-comparator.log`.

The unprescribed-cutvertex case still needs its boundary fan separation. The
concrete chord and short-path cuts, the list updates and all final deletion
cases are also unfinished. Passing this comparator does not prove
`BoundaryExtension` or the unconditional main theorem. No new publication or
Palomar submission has been performed.

## Concrete short-cycle cut and complete list-extension reduction

Continued from `112dd0c`. Three new modules close the separating-short-cycle
case of the stronger induction, while the main theorem remains unproved.

`CycleSeparation.lean` defines the actual cycle subgraph and its two oriented
dart families. The rotation exchanges the two darts at every cycle vertex;
the face permutation therefore has exactly the forward and backward orbits.
The region machinery then gives connected closed sides covering the graph,
with intersection exactly the cycle and every original edge in a piece.
For a chordless cycle, empty opposite gaps give the exact selected face of
each induced side. An original face belongs wholly to one closed side.

`CycleWalk.lean` identifies this indexed cycle with an actual native closed
walk: injectivity, adjacency, support, edges and support cardinality are
proved. Triangle/four-cycle exclusion proves chordlessness for cycles with
at most six vertices. `NativeCycleSeparates` means there is a vertex in each
of the two actual open face regions. It supplies proper smaller sides and
orients the cut so the original selected face is in the first side.

`ShortCycleReduction.lean` proves
`BoundaryInstance.colourable_of_separating_short_cycle`. Strict induction
colours the first side; those colours prescribe the native cycle on the
second. The proof checks the selected face, prescribed edges, singleton
lists, original interior lists, short-list edges, membership in the original
lists and agreement before gluing. The only induction assumption is the
extension statement for strictly smaller vertex cardinalities.

Strict build and axiom audit passed. The independent module
`ThomassenCycleChallenge.lean` imports the previously checked region and
instance infrastructure, but none of these three proof modules. Comparator
checked 49 theorem contracts and five complete definitions; Lean and NanoDa
accepted the solution. Logs: `verification/short-cycle-strict-build.log`,
`verification/short-cycle-challenge-build.log`, and
`verification/short-cycle-comparator.log`.

This does not handle a prescribed facial cycle with an empty region. The
unprescribed boundary cutvertex/fan case, chord and short-path cuts with
their changed prescriptions, and the final deletion cases also remain.
The unconditional main theorem is absent and its comparator fails. No
publication or Palomar submission has been made for this incomplete result.

## Facial chord cuts and complete prescribed facial-cycle case

Continued from `1c0c8e3`. The unconditional theorem remains unproved.

`ChordSeparation.lean` proves the boundary-arc/chord geometry from the actual
local face-permutation equations. Extra chords are allowed. Removing the old
arc's internal vertices from the exterior piece leaves an exact two-endpoint
separator, with cover, all edges in a piece, connected native induced graphs,
strict vertex-count decreases and the required face transport.
`PrescribedChordReduction.lean` colours and glues both pieces when the ends are
prescribed and all other prescribed vertices are outside the removed arc.
This is an actual case reduction using strict induction, not a replacement
extension assumption. The split-prescription and unprescribed-end cases remain.

`FiveCycle.lean` supplies the local girth exclusions, exact native prescribed
path after deleting a cycle vertex, and geometric neighbour exposure.
`FacialFiveReduction.lean` verifies every residual-list condition, invokes
strict induction and restores the vertex using the existing `glue_residual`.
For a five-cycle there is no shared exterior neighbour of two cycle vertices.
For a six-cycle the only possible second cycle neighbour is the opposite vertex.

`FacialSixReduction.lean` closes that exceptional case. Two consecutive opposite
pairs with exterior common neighbours yield four explicit disjoint connected
bags meeting the chosen face. With the registered face apex they give a K5
minor. Hence if the first vertex cannot be deleted by the common residual-list
argument, the next vertex can. Deletion connectivity is established by the
alternative already proved at a prescribed cutvertex. The full six-cycle
statement has no common-neighbour exclusion. The wrapper
`colourable_of_facial_short_cycle` covers every prescribed facial cycle of at
most six vertices, under the same strict induction on smaller instances.

Verification:

- Strict solution axiom audit passed; only `propext`, `Classical.choice` and
  `Quot.sound` occur.
- `comparator.chords.json`: 12 theorem contracts and four full definitions;
  independent challenge imports neither new chord proof module. Lean and NanoDa
  accepted. Logs: `verification/prescribed-chord-strict-build.log`,
  `verification/prescribed-chord-challenge-build.log`, and
  `verification/prescribed-chord-comparator.log`.
- `comparator.five.json`: 15 theorem contracts, including the full facial
  six-cycle and short-cycle statements. The challenge imports none of the three
  new facial-cycle proof modules. Lean and NanoDa accepted. Logs:
  `verification/facial-cycle-strict-build.log`,
  `verification/facial-cycle-challenge-build.log`, and
  `verification/facial-cycle-comparator.log`.
- The actual main comparator still fails because the unconditional theorem is
  absent. Its unchanged selector and independent main statement are retained.
  Log: `verification/main-gate-after-chord-and-facial-cycles.log`.

Remaining: unprescribed boundary cutvertices/fans; the other chord cases and
short interior-path cuts with their changed prescriptions; the final
residual-list/deletion cases; and the unconditional extension induction.
No publication or Palomar submission has been made for this incomplete result.

## Split prescribed-edge cuts and interior cutvertices

Continued from `9b23144`. The unconditional theorem remains unproved.

`EdgeCutPrecolor.lean` constructs exact native prescribed intersections at a
cut whose two common vertices form a prescribed edge. A path decomposes around
that oriented edge into two branches; each retained branch lies in the side or
meets it only at its endpoint. The four resulting combinations give the actual
retained path. A rotated cycle lies wholly in the side or meets it precisely in
the two edge endpoints. In either case the induced prescription has exactly the
old vertices and edges in the piece, and still has at most six vertices.

`EdgeCutReduction.lean` uses those prescriptions on both strictly smaller
connected induced pieces. Every original list is retained. The short-list
condition proves that an edge joining prescribed vertices belongs to the
prescription, and its two singleton colours enforce agreement before gluing.
The full facial-chord corollary no longer assumes that all other prescribed
vertices lie in the exterior piece. This closes the previously pending
split-prescription case when both chord endpoints are prescribed.

`InteriorCutReduction.lean` closes the cutvertex case outside the selected
face. Its face-vertex set is connected and avoids the cutvertex, so all original
boundary vertices lie in one side. Colour that side first. The other side has
original lists of size at least three at every vertex. Prescribe the colour of
the separator on an actual incident face, obtaining an admissible singleton
path, apply strict induction and glue. The proof uses no nonempty-colour-type
assumption. Its `cutvertex_constraints` corollary isolates the remaining case:
a cutvertex of a smallest counterexample must lie on the selected face and
outside the original prescription.

Verification:

- Strict solution/axiom audit passed with only `propext`, `Classical.choice` and
  `Quot.sound`.
- `comparator.edge-cuts.json`: nine independent theorem contracts over the
  previously checked cutvertex and chord geometry. Neither new edge-cut proof
  module is imported by the challenge. Comparator, Lean and NanoDa accepted.
  Logs: `verification/edge-cut-strict-build.log`,
  `verification/edge-cut-challenge-build.log`, and
  `verification/edge-cut-comparator.log`.
- `comparator.interior-cuts.json`: four independent theorem contracts over
  previously checked cutvertex and cycle geometry. The challenge does not
  import `InteriorCutReduction`. Comparator, Lean and NanoDa accepted.
  Logs: `verification/interior-cut-strict-build.log`,
  `verification/interior-cut-challenge-build.log`, and
  `verification/interior-cut-comparator.log`.
- The unchanged main comparator still fails because the unconditional theorem
  is absent: `verification/main-gate-after-prescribed-edge-and-interior-cuts.log`.

Still open: unprescribed boundary cutvertices/fans; chords with unprescribed
endpoints; short interior-path cuts with their prescribed subgraphs and list
updates; final residual-list/deletion cases; and the unconditional extension
induction. No publication or Palomar submission has been made for this unfinished
result.

## Native short-path cuts, merged faces and list-extension case

Continued from `efe9093`. **The unconditional theorem is still unproved.**

Five new proof modules establish the following scope:

- `FaceMerge.lean`: different old faces entering a connected omitted set project
  to one new face of a connected retained graph. It also retains the original
  selected face and exposes neighbours of the omitted set. The omitted set need
  not be the entire complement of the retained vertices.
- `ArcPathSeparation.lean`: an actual facial arc can be separated by a connected
  chordless path on the remainder of the cycle. No global chordlessness is
  assumed. A skeleton keeps the exterior side and its cycle while removing
  extra cycle chords. It is proved connected, with the opposite cycle face
  preserved. Removing the old arc merges that face with the original selected
  face, and the resulting induced graph equals the original exterior piece.
  The inside piece remains the actual original induced graph. The pieces cover
  all edges and meet in exactly the separator, with both cardinalities smaller.
- `CycleIntervals.lean`: consecutive cycle intervals are connected already in
  the cycle graph itself. Their exact partition is proved, and girth excludes
  extra edges on a path with at most three edges.
- `NativeArcPathCut.lean`: the separator interval is exactly the support of the
  native suffix `p.drop n`. This gives a concrete cut with no assumed Jordan
  separation or colour extension. All separator vertices and the surviving old
  boundary lie on one actual exterior face.
- `ShortPathColouring.lean`: the complete induction and gluing for this cut
  when the prescription is outside the trimmed arc and its old short lists have
  no neighbour on the separator. Every changed-list condition is checked. The
  case where all arc lists have at least three colours is a corollary. The
  arbitrary colour type is retained.

The old-arc corner equations and the restrictions on short lists are explicit
mathematical case conditions. This checkpoint does not prove that every chord or
short interior path in a minimal counterexample satisfies them. Additional
precolouring of short neighbours, the prescribed-path exceptions, boundary fans
and the final deletion cases remain.

Strict solution and axiom-audit builds passed. The independent challenge
`ThomassenPathCutChallenge.lean` imports the previously verified face, chord and
instance prerequisites, but none of these five modules. Comparator checked 27
theorem contracts and three complete definitions; Lean and NanoDa accepted the
solution with only `propext`, `Classical.choice` and `Quot.sound`. Logs:
`verification/path-cut-strict-build.log`,
`verification/path-cut-challenge-build.log`, and
`verification/path-cut-comparator.log`.

The unchanged main comparator still fails with the unconditional theorem absent:
`verification/main-gate-after-short-path-cuts.log`. No publication or Palomar
submission has been made for this unfinished formalization.


## 2026-10-24: extra short neighbours and actual native face boundaries

The main theorem and `BoundaryExtension` remain unproved.

- `AugmentedPathColouring.lean` proves independent colour choice for added short
  vertices, then a complete enlarged-path induction with at most six prescribed
  vertices. The two concrete cases construct their native paths and prove their
  chordlessness: two added short neighbours on a separator of at most two edges;
  one added short neighbour on a separator of at most three edges whose other
  end is already short.
- `NativeAugmentedPathCuts.lean` applies both cases to the existing actual facial
  cuts. These theorems retain explicit conditions that all other short neighbours
  are captured and the old prescription avoids the trimmed arc. They do not
  assert those conditions for every needed minimal cut.
- `CycleMapWalk.lean` maps the existing Mathlib cycle to construct a native cycle
  in the exact order of an indexed cycle map.
- `FaceOrbitCycle.lean` constructs the actual native cycle of the selected face,
  including its exact vertices, root dart and all corner equations. For a
  connected graph on at least three vertices, connectivity after every vertex
  deletion suffices; the degree bound is derived. This does not close boundary
  cutvertices or the selection of spliced arcs.

Strict solution and axiom-audit builds passed. The independent augmented challenge
imports none of these four new modules and compares 22 theorem contracts and
three complete face-orbit definitions. Lean and NanoDa accepted the comparison.
Logs are `verification/augmented-strict-build.log`,
`verification/augmented-challenge-build.log`, and
`verification/augmented-comparator.log`. The solution hole audit is
`verification/augmented-hole-audit.json`.

Remaining work: boundary cutvertex fans, selection and capture for the required
minimal cuts, exceptional six-vertex prescribed paths, final deletion/residual
cases and unconditional induction. The root main comparator is still the
completion criterion; it fails because the unconditional main declaration is
absent (`verification/main-gate-after-augmented-paths.log`). No publication or
Palomar submission was made.


## 2026-10-24: complete cutvertex normalization and prescribed cycles

The unconditional main theorem remains unproved.

Nine new proof modules close the complete cutvertex work unit:

- Actual facial prefix cycles and all original corner equations yield genuine
  strict chord cuts. Rotating the indexed boundary allows arbitrary chord ends.
- A second strong induction fixes the root and every old short neighbour in
  each graph below the original strict bound. It splits cutvertices and actual
  short-neighbour chords until a path prescription with at most three vertices
  suffices. Compatible colours, every list invariant and gluing are proved.
  The fan may have arbitrarily many neighbours; no extension hypothesis for
  the fan or for the original graph is supplied.
- This auxiliary theorem completes the unprescribed boundary-cutvertex case.
  All cutvertices, disconnected instances and cardinalities at most two are
  eliminated. A smallest counterexample now has an actual native facial cycle
  with exact vertices and original corners.
- Edges between prescribed vertices must follow that cycle. An embedded simple
  cycle using only another cycle's edges has the same vertices, so the full
  prescribed-cycle case reduces to the already checked facial five/six-cycle
  proof. No facial placement is assumed in the new final cycle statement.

Strict solution and axiom-audit builds passed. `ThomassenFanChallenge` imports
none of the nine new modules. Comparator, Lean and NanoDa accepted 35 theorem
contracts and three complete definitions. Logs:
`verification/fan-strict-build.log`, `verification/fan-challenge-build.log`,
`verification/fan-comparator.log`, `verification/fan-hole-audit.json`.

Remaining: cuts with unprescribed chord/path ends, minimal short-path selection
and capture, exceptional six-vertex prescribed paths, final residual-list and
multi-vertex deletion cases, then unconditional boundary-extension induction.
The main gate remains separate and fails with the unconditional declaration
absent (`verification/main-gate-after-fan-normalization.log`). No publication or
Palomar submission was made.


## 2026-10-24: two-endpoint fans and unprescribed boundary chords

The unconditional main theorem remains unproved.

Eleven new proof modules extend the verified one-root infrastructure:

- A second strong induction fixes both ends of an edge and all their old short
  neighbours. It handles every auxiliary cutvertex and actual root spoke, with
  bases on at most four prescribed vertices. Its main-induction bound and every
  auxiliary vertex-count decrease are explicit.
- Allowed distinct endpoint colours have compatible choices on the old short
  neighbours. Original singleton endpoint lists are temporarily enlarged to
  make an empty-prescription piece; fixed separator colours then restore all
  original lists before gluing.
- Every edge cut with the original prescription retained in one side is closed,
  allowing singleton separator ends and arbitrarily many old short neighbours.
- The native prescription avoids a two-unprescribed-end separator wholly on one
  side. Thus every actual boundary chord with two unprescribed ends is closed.
  A chord incident with a prescribed-path endpoint is closed too. The mixed
  internal-vertex case that splits the original path remains open.

Strict solution and axiom-audit builds passed. The independent challenge imports
none of these eleven modules. Comparator, Lean and NanoDa accepted 25 theorem
contracts and two complete definitions. Logs:
`verification/edge-star-strict-build.log`,
`verification/edge-star-challenge-build.log`,
`verification/edge-star-comparator.log`,
`verification/edge-star-hole-audit.json`.

Remaining: mixed internal-prescription chords; native prescribed outer-path
alignment and short-complement cases; minimal short-path selection/capture and
six-vertex prescribed-path exceptions; final residual-list and multi-vertex
removal cases; unconditional induction and the main theorem. The main gate
still fails because the unconditional declaration is absent:
`verification/main-gate-after-edge-star-reductions.log`. No publication or
Palomar submission was made.


## 2026-10-24 — Mixed prescribed-leaf cuts and native facial-path order

The unconditional main theorem remains unproved.

Five new proof modules reuse the checked two-endpoint fan and facial chord APIs:

- Exact restriction of the native prescribed path on either side of a mixed
  separator, retaining its actual vertices, edges and six-vertex bound.
- Empty-instance construction releasing one private prescribed neighbour to a
  two-list. The fixed separator colour forces that neighbour's original colour;
  all original lists are restored before the induced colourings are glued.
- Complete mixed-cut reduction whenever one prescribed branch has at most one
  edge. This closes every actual boundary chord for paths on at most four
  vertices, and the noncentral mixed chords for longer prescriptions too.
- An exact classification of remaining central branch lengths as (2,2), (2,3)
  or (3,2). These cases are still open.
- Native path order on an indexed cycle, and the resulting contiguous facial-arc
  placement of the original prescribed path in a smallest counterexample.

Strict solution and axiom-audit builds passed. The independent challenge imports
none of these five proof modules. Comparator, Lean and NanoDa accepted all 14
new theorem contracts. An executable-source audit found no proof holes, added
axioms or `native_decide` in 61 solution modules. Logs:
`verification/mixed-chord-strict-build.log`,
`verification/mixed-chord-challenge-build.log`,
`verification/mixed-chord-comparator.log`,
`verification/mixed-chord-hole-audit.json`.

Remaining: the three central mixed-chord cases; short unprescribed boundary
complements; minimal short-path selection, spliced corners and capture; exceptional
six-vertex prescribed paths; final residual-list and multi-vertex deletion cases;
unconditional boundary extension and the actual main theorem. The root main
comparator still fails because the unconditional declaration is absent, as
recorded in `verification/main-gate-after-mixed-chord-reductions.log`.
No publication or Palomar submission was made.


## 2026-10-25 — Complete boundary-chord reduction

The unconditional main theorem remains unproved. The entire boundary-chord
work unit, including the formerly open central splits, is now closed under the
strict main induction.

Ten new proof modules reuse the complete root/two-endpoint fan inductions,
exact induced prescriptions, actual facial cuts and native-path APIs:

- A complete anchored-fan strong induction fixes a boundary root and its old
  short neighbours while retaining up to three original prescribed vertices
  adjacent to the root. It handles all spokes, prescribed-edge cuts and
  cutvertices. Every auxiliary call decreases its own cardinality, and every
  main-induction call remains below the explicit strict bound `N`.
- The normalized face base is a native induced path on at most five vertices.
  Original singleton lists and fixed fan colours remain compatible and are
  preserved. No anchored-fan extension hypothesis is supplied at the top.
- An external vertex has at most one neighbour on a prescribed path of at most
  two edges. The other cut piece supplies its actual separator colour, avoiding
  the original prescribed singleton in the short piece.
- At any mixed cut, one branch of a six-vertex prescribed path has at most two
  edges. This closes all three central cases (2,2), (2,3), (3,2).
- Every actual boundary chord is now closed for every permitted original
  prescription. A smallest counterexample has an actual native facial boundary
  that is chordless in the whole graph, with original face vertices and corners.

The strict solution and axiom-audit builds passed. The independent challenge
imports none of the ten proof modules. Comparator, Lean and NanoDa accepted 26
theorem contracts and the complete auxiliary induction predicate. An executable
source audit found no proof holes, added axioms or `native_decide` in 71 solution
modules. Logs:
`verification/boundary-chord-strict-build.log`,
`verification/boundary-chord-challenge-build.log`,
`verification/boundary-chord-comparator.log`,
`verification/boundary-chord-hole-audit.json`.

Remaining: short unprescribed boundary complements; selection, spliced corners
and capture for the two/three-edge interior-path cuts; exceptional six-vertex
prescribed paths; final residual-list and multi-vertex deletion cases;
unconditional boundary extension and the actual main theorem. The root main
gate still fails because the unconditional declaration is absent:
`verification/main-gate-after-complete-boundary-chords.log`.
No publication or Palomar submission was made.


## 2026-10-25 — Native face splices and prescription-free interior two-path arcs

The unconditional main theorem remains unproved. This checkpoint closes a
specified interior-path case; it does not close the full extension induction.

Five proof modules reuse the checked native-cycle, actual face-separation,
short-list augmentation and complete boundary-chord results:

- The original facial prefix and an interior closing path form an actual native
  simple cycle. Its length, exact returning separator support, exact original
  trimmed arc, unchanged root dart, all internal face corners and a vertex on
  the old complementary arc outside the new cycle are proved.
- These facts instantiate the actual strict cut for interior closing paths of
  one to three edges. No spliced-corner or additional disjointness witness is
  supplied to the resulting cut theorem.
- Separators of at most two edges allow zero, one or two extra short endpoint
  neighbours. With only one extra neighbour there is no short-list assumption
  at the opposite endpoint. All changed-list conditions and gluing are checked.
- The first other old-boundary incidence of the interior vertex selects a
  smaller arc. Girth forces distance at least three; selection eliminates every
  other interior incidence, and chordlessness captures the endpoint incidences.
- The complete two-edge interior-path reduction for a prescription-free chosen
  facial arc has no supplied minimality, corner or capture assumption. A
  remaining two-path cut must meet the prescription on that chosen arc.

Strict solution and axiom-audit builds passed. The independent challenge imports
none of these five proof modules. Comparator, Lean and NanoDa accepted 18 theorem
contracts and the complete native splice definition. An executable-source audit
found no proof holes, added axioms or `native_decide` in 76 solution modules. Logs:
`verification/interior-two-path-strict-build.log`,
`verification/interior-two-path-challenge-build.log`,
`verification/interior-two-path-comparator.log`,
`verification/interior-two-path-hole-audit.json`.

Remaining: short unprescribed boundary complements; two-edge cuts dividing the
prescription; remaining three-edge interior-path cuts; exceptional six-vertex
prescribed paths; final residual-list and multi-vertex deletion cases;
unconditional boundary extension and the actual main theorem. These are
mathematical proof obligations, not just assembly. The root gate still fails
because the unconditional declaration is absent:
`verification/main-gate-after-interior-two-paths.log`.
No publication or Palomar submission was made.


## 2026-10-25 — Exact prescribed-endpoint deletion and residual-list obstructions

The unconditional main theorem remains unproved. This is a verified deletion
case with explicit geometric exclusions, not completion of the final induction.

`PrescribedEndpointDeletion.lean` reuses the checked induced-face exposure,
prescribed-cutvertex, residual-list cardinality, original short-edge invariant,
short-path neighbour uniqueness and colouring-restoration infrastructure:

- Deleting the initial prescribed vertex retains the exact native remaining
  path and edges; an original singleton leaves an empty prescription.
- Old unprescribed two-lists remain unchanged. Other unprescribed lists lose
  at most one colour. Newly shortened two-lists are independent by girth.
- The new two-lists and old face vertices lie on an actual selected face of
  the proper induced remainder. Small graphs and cutvertices are handled by
  the previously checked reductions; all other induction calls are strict.
- If a newly shortened neighbour has neither a remaining prescribed neighbour
  nor an old unprescribed two-list neighbour, the remaining instance satisfies
  every invariant. The final gluing restores all original lists and colours.
- Girth automatically supplies the first exclusion for prescribed paths of at
  most three vertices. With three-lists everywhere else, the whole case is
  closed under the strict main induction, with no extra geometric assumption.
- A smallest counterexample has explicit vertex witnesses for at least one of
  the two geometric conflicts. Their global exclusions/exception handling are
  still unproved; they are not assumed away in the overall proof.

Strict solution and axiom-audit builds passed. The independent challenge does
not import the new proof module. Comparator, Lean and NanoDa accepted five
theorem contracts. An executable-source audit found no proof holes, added axioms
or `native_decide` in 77 solution modules. Logs:
`verification/endpoint-deletion-strict-build.log`,
`verification/endpoint-deletion-challenge-build.log`,
`verification/endpoint-deletion-comparator.log`,
`verification/endpoint-deletion-hole-audit.json`.

Remaining mathematical obligations include short unprescribed boundary
complements, two-edge cuts dividing the prescription, remaining three-edge
interior paths, exceptional six-vertex prescriptions, resolution of the explicit
endpoint-deletion conflicts, other multi-vertex deletions, and unconditional
boundary extension. The actual main gate still fails because the unconditional
declaration is absent: `verification/main-gate-after-endpoint-deletion.log`.
No publication or Palomar submission was made.


## 2026-10-25 — Arbitrary facial subarcs and prescribed-endpoint conflicts

The unconditional main theorem remains unproved. Five new proof modules reuse
the checked native face, strict path-cut, augmented-prescription, chord and
endpoint-deletion infrastructure.

- Actual facial cycles can be rebased at every native index, retaining their
  face-permutation orbit and all original corner equations. The complete
  prescription-free two-path reduction now applies on arbitrary facial subarcs.
- Two-path reductions give uniqueness of an interior vertex's incidences with a
  prescription-free arc. This closes three-edge interior-path cuts on such arcs
  when the initial boundary endpoint has a short list; all capture conditions
  are proved internally.
- There is no interior two-path from a prescribed endpoint to an unprescribed
  boundary vertex or to the other prescribed endpoint. A remaining interior
  common neighbour reaches only internal prescribed positions three or four.
- Old unprescribed two-list conflicts at a prescribed endpoint are localized to
  the old boundary. They are absent when the first forward boundary vertex is
  prescribed and the second backward vertex has at least three colours.
- With this concrete boundary pattern the final endpoint-deletion branch is
  closed for prescribed paths on up to four vertices, without supplied conflict
  exclusions. Longer paths still have the internal positions-three/four cases.

The strict solution and axiom-audit build passed. An independent challenge
imports none of these five proof modules. Comparator and both Lean and NanoDa
kernels accepted all 20 theorem contracts. An executable-source scan found no
proof holes, custom axioms or native_decide in 82 solution modules. Logs:
`verification/subarc-reduction-strict-build.log`,
`verification/subarc-reduction-challenge-build.log`,
`verification/subarc-reduction-comparator.log`,
`verification/subarc-reduction-hole-audit.json`.

The actual main gate still fails: the unconditional declaration is absent
(`verification/main-gate-after-subarc-reductions.log`). Remaining mathematical
obligations include short unprescribed outer complements, prescription-splitting
two-path cuts, other three-path cases, internal prescribed-neighbour positions
three/four, short-boundary-list and exceptional six-vertex deletion cases, and
unconditional boundary extension. No publication or Palomar submission was made.


## 2026-10-25 — Prescribed-prefix two-path cuts and the complete first deletion branch

The unconditional main theorem remains unproved. Two new proof modules reuse
the actual facial-path cut, prescription-free two-path exclusion, original
short-edge invariant, native face-order theorem and endpoint deletion.

`CompatiblePrescription.lean` checks every changed list and edge condition for
a compatible replacement path/cycle on a proper induced piece and then invokes
strict induction. `PrescribedInteriorTwoPath.lean` applies it to both actual
sides of an interior two-path joining the initial prescribed vertex to native
position three or four of a forward prescribed path:

- The inner prescription is the actual five/six-cycle. The exterior prescription
  replaces its old prefix by the two-path, leaving at most five vertices.
- The interior vertex has only the two specified old prescribed neighbours and
  no old unprescribed short neighbour. Its three-list supplies a compatible
  colour. Both new prescriptions retain every old singleton on their side.
- All cut geometry, strict decreases, remaining short edges, old/new faces and
  agreement on the separator are proved internally.
- The first forward face vertex being prescribed fixes the orientation of the
  entire old path. No interior two-path can then join that initial prescribed
  endpoint to any other old boundary vertex in a smallest counterexample.
- With a three-list at the second backward face vertex, both former endpoint
  conflict exclusions follow. The good-second-boundary-list deletion branch
  is therefore closed for all original prescribed paths on at most six vertices.
  In a remaining counterexample with the first forward face vertex prescribed,
  the second backward vertex has a list of size at most two.

Strict solution and axiom-audit builds passed. An independent challenge imports
neither new proof module. Comparator, Lean and NanoDa accepted all seven theorem
contracts. Executable-source audit: 84 solution modules, no proof holes, added
axioms or native_decide. Logs: `verification/prescribed-two-path-strict-build.log`,
`verification/prescribed-two-path-challenge-build.log`,
`verification/prescribed-two-path-comparator.log`,
`verification/prescribed-two-path-hole-audit.json`.

Remaining mathematical obligations include short outer-boundary complements,
other two-path cuts dividing the prescription away from its original endpoints,
remaining three-path configurations, the branch with a short second backward
boundary list, exceptional final multi-vertex deletions, and unconditional
boundary extension. These are not just assembly. The actual main gate still
fails because its unconditional declaration is absent:
`verification/main-gate-after-prescribed-two-paths.log`. No publication or
Palomar submission was made.


## 2026-10-25 — Component faces, three-vertex deletion and short outer faces

The unconditional main theorem remains unproved. Four new proof modules reuse
the checked connected-omission face merger, native cycle rebasing, exact induced
prescriptions, residual gluing, two/three-path reductions and full-cycle case.

- Actual faces are constructed independently for every nontrivial component
  remaining after a connected deletion through the old facial root. Components
  retaining old face vertices use a forward old facial exit dart; components
  retaining none use an interface edge. All neighbours of the deleted set are
  exposed on that component's actual selected face.
- The general connected-boundary-deletion induction now permits disconnected
  remainders. It checks explicit residual singleton, two-list and short-edge
  conditions on each component, restricts the exact native prescription and
  colours isolated vertices directly. Every induction call is strict.
- With the first boundary edge prescribed, no interior vertex has two distinct
  old boundary neighbours in a smallest counterexample. Native rebasing proves
  the full complementary arc free of the prescription.
- If the second backward list is short and the fourth has at least three
  colours, deleting the prescribed endpoint and the next two backward vertices
  is a complete case for that prescribed edge. Compatible colours, all residual
  list bounds, old/new and new/new short-edge exclusions, the exact remaining
  singleton and restoration are proved internally. Arbitrarily disconnected
  remainders are included.
- An actual six-vertex outer face with an edge prescribed is fully handled:
  the fourth backward vertex is adjacent to the other prescribed endpoint and
  cannot be short. The complementary good-second-list branch was already closed.
- A compatible colouring of any actual outer cycle on at most six vertices
  can be promoted to the checked full-cycle extension case. On a five-vertex
  face with an edge prescribed, choose the middle unprescribed colour first;
  its two three-list neighbours avoid that colour and their prescribed
  neighbours. This closes the five-vertex outer-face case for that edge too.

Strict solution and axiom-audit builds passed. An independent challenge imports
none of the four new proof modules. Comparator, Lean and NanoDa accepted all
15 theorem contracts. An executable-source audit found no proof holes, added
axioms or native_decide in 88 solution modules. Logs:
`verification/boundary-deletion-strict-build.log`,
`verification/boundary-deletion-challenge-build.log`,
`verification/boundary-deletion-comparator.log`,
`verification/boundary-deletion-hole-audit.json`.

Remaining: the prescribed-edge alternating short-second/short-fourth-list
configuration; short outer complements for longer prescriptions; other cuts
dividing the prescription and remaining three-path configurations; longer-
prescription and exceptional final deletions; unconditional boundary extension
and the actual main theorem. The general deletion theorem's residual conditions
are explicit obligations, not an unconditional extension assumption. The actual
main gate still fails because its unconditional declaration is absent:
`verification/main-gate-after-boundary-deletion.log`. No publication or Palomar
submission was made.


## 2026-10-25 — Alternating boundary-list case closed

The requested short-second/short-fourth-list case for a prescribed boundary edge
is now proved under the existing strict main induction. The unconditional main
theorem remains unproved.

`AlternatingBoundaryLists.lean` reuses exact native rebasing, the original
short-edge invariant and the completed good-second-list branch for prescriptions
on at most six vertices. Its construction actually only needs the short fourth
list when the outer boundary has at least seven vertices:

- Choose the third backward vertex's colour outside the old fourth two-list;
  choose compatible colours at the second and first backward vertices.
- Precolour the actual native five-vertex path from the third backward vertex
  through those vertices and the original prescribed edge. All old singleton
  colours are retained.
- Add the third vertex's prescribed colour to the fourth vertex's old list.
  That is the only enlargement. Every other changed singleton, boundary and
  interior list, proper prescribed edge and short edge is checked.
- Rebase the actual old face at the new prescribed endpoint. Its second backward
  vertex has a three-list by the original short-edge invariant. Apply the
  previously checked good-second-list branch with its strict induction.
- The added colour cannot be used at the enlarged-list vertex, since its
  neighbour is prescribed that same colour. Every original list is restored.

The six-vertex alternative follows directly from the original short-edge
invariant. Combining the new result with the completed good-fourth-list deletion
closes the entire prescribed-edge short-second-list branch. Combining that with
the earlier good-second-list branch and five-vertex face gives the complete
actual native facial induction case with its first forward edge prescribed.
No capture, extension or same-size colourability assumption was added.

Strict solution and axiom-audit builds passed. The independent challenge imports
the previously checked short-face prerequisites, not the new proof module.
Comparator, Lean and NanoDa accepted all four theorem contracts. Executable-
source audit: 89 solution modules, no proof holes, custom axioms or native_decide.
Logs: `verification/alternating-lists-strict-build.log`,
`verification/alternating-lists-challenge-build.log`,
`verification/alternating-lists-comparator.log`,
`verification/alternating-lists-hole-audit.json`.

The alternating case is no longer pending. Remaining main-theorem obligations
concern longer prescribed paths, their short outer complements, other cuts
dividing those prescriptions, remaining three-path configurations and exceptional
final deletions, and unconditional boundary extension. The actual main gate
still fails because its unconditional declaration is absent:
`verification/main-gate-after-alternating-lists.log`. No publication or Palomar
submission was made.

## 2026-10-25 — Connected branching prescriptions and one-vertex complements

**The unconditional main theorem and `BoundaryExtension` remain unproved.**
The following reductions are complete under the existing strict main induction:

- Mirroring an actual plane map reverses every vertex rotation, preserves its
  Euler certificate, and retains exactly the vertices incident with the selected
  outer face. Native mirrored/rebased facial cycles retain their exact order and
  corner equations. The free-arc three-path reduction now accepts a short list
  at either boundary endpoint.
- The prescribed-edge reduction now handles arbitrary original embeddings and
  either orientation of the prescribed edge. Connectivity, facial normalization
  and placement are derived internally; the earlier native-face assumptions
  are no longer supplied by its caller.
- `ConnectedPrescription` records an actual connected prescribed induced graph
  whose every simple path has at most five edges. It permits unboundedly many
  pendant vertices, and has no extension or colourability field. A clique
  retraction proves connectedness of restrictions at prescribed separators.
  A complete separate strong induction handles cutvertices and prescribed
  facial chords, then converts the remaining maximum-degree-two prescription
  to an actual native path/cycle on at most six vertices. All uses of the main
  induction remain below the explicit bound `N`.
- A prescribed graph with at most four vertices capable of having two prescribed
  neighbours has no simple path longer than five edges. This proves the bound
  for short native paths with independent leaves attached at internal vertices.
  Three neighbours on a boundary cycle would require three cyclic gaps of at
  least three edges, so an off-cycle vertex has at most two neighbours on a
  cycle of length at most eight.
- The residual extension theorem handles a connected branching prescription
  exposed by a connected boundary deletion, separately on every retained
  component. Its residual membership, properness, short-edge and path-bound
  requirements are explicit mathematical conditions, not an extension premise.
- The complete main-induction case with exactly one unprescribed outer vertex
  is closed. This includes six prescribed vertices on a seven-vertex face.
  The proof chooses the deleted vertex's colour, derives independence and
  unique attachments of new short neighbours, colours those attached to the
  old path, and applies the proved auxiliary induction. The final corollary
  derives the actual face and its rebasing from the original arbitrary instance.

Strict solution and axiom-audit builds passed. A separate challenge imports
none of the ten new proof modules. Comparator, Lean and NanoDa accepted all
34 theorem contracts and five definition contracts. The dependency comparison
also checks the new structure and its constructor. Source audit: 99 solution
modules, no proof holes, custom axioms or native_decide. See
`verification/connected-prescription-*.log` and
`verification/connected-prescription-hole-audit.json`.

Remaining: two unprescribed outer vertices; short-path cuts dividing longer
prescriptions; remaining three-path configurations; the longer-prescription
and exceptional final deletions; unconditional boundary extension and the actual
main theorem. The actual root main gate still fails because its unconditional
declaration is absent: `verification/main-gate-after-connected-prescriptions.log`.
No publication or Palomar submission was made.

## 2026-10-25 — All outer complements on at most two vertices closed

The complete strict main-induction case with exactly two unprescribed outer
vertices is now proved, including six prescribed vertices on an eight-vertex
outer face. The unconditional main theorem remains unproved.

`TwoBoundaryGeometry.lean` proves that an outside cycle edge can meet a native
cycle path only at an endpoint. If the two complementary vertices were
nonadjacent, each would meet both path endpoints, yielding a forbidden
four-cycle. Their actual adjacency is therefore derived. Each end of this
complementary edge has exactly one old prescribed neighbour, so its three-list
admits compatible deleted colours preserving all original singleton colours.

The already checked edge-deletion girth lemmas prove independence of the new
short neighbours. The short-cycle neighbour bound gives each at most one old
prescribed neighbour, and girth excludes attachment at either path endpoint.
`PendantResidualReduction.lean` chooses all attached neighbours' colours and
invokes the proved connected-prescription induction separately on every
retained component. No connectivity of the whole remainder is assumed.
`TwoBoundaryComplement.lean` checks every concrete condition and derives
arbitrary original facial placement by normalization and rebasing.

The zero-vertex complement is also eliminated: the endpoint of an induced
prescribed path contained in a simple cycle must meet the cycle complement.
Combined with the previous one-vertex result, this closes all cases with at
most two unprescribed outer vertices. Consequently a remaining counterexample
with prescribed path `r` and actual outer cycle `p` satisfies
`r.length + 4 ≤ p.length`. This removes the short-complement obligation before
the remaining two/three-path separator cases.

Strict solution and axiom-audit builds passed. A separate challenge imports
none of the three new proof modules. Comparator, Lean and NanoDa accepted all
11 theorem contracts. Source audit: 102 solution modules, no proof holes,
custom axioms or native_decide. Logs: `verification/two-boundary-*.log` and
`verification/two-boundary-hole-audit.json`.

Still open: short-path cuts dividing longer prescriptions, remaining three-path
configurations and exceptional final deletions, unconditional boundary
extension and the actual main theorem. The two-vertex outer complement is no
longer pending. The unchanged root main comparator still fails because the
unconditional declaration is absent; see
`verification/main-gate-after-two-boundary.log`. No publication or Palomar
submission was made.

## 2026-10-25 — All interior two-paths with two prescribed ends closed

**The unconditional main theorem remains unproved.** The entire case where an
interior vertex joins two distinct vertices of the prescribed path is now
eliminated under the existing strict main induction, for arbitrary original
faces and either native prescribed-path orientation.

`CompatiblePathStar.lean` extends a compatible induced path on a strictly
smaller actual piece while fixing its new internal vertex and all old short
neighbours. These additional vertices are independently coloured leaves; their
number is unbounded. The verified connected-prescription induction is used
below the strict main bound, with every list and face condition checked.

`CentralPrescribedTwoPath.lean` closes the only possible pair of internal
prescribed endpoints: positions 1 and 4 on a six-vertex native path, with
positions numbered from zero. Rebase the actual face at position 1 and cut
along its two-edge interior path. The interior piece has a compatible
five-cycle prescription. The exterior piece has the native five-vertex path
0--1--u--4--5. Its old short neighbours are handled by the proved path-star
extension. Every retained singleton and separator colour agrees before gluing;
no old-short-neighbour capture condition is assumed.

`OrientedPrescription.lean` derives actual native facial normalization in the
direction of the prescribed path, using the proved mirror embedding when
needed. `PrescribedNeighbourUniqueness.lean` derives the arbitrary-face initial
and terminal endpoint exclusions, retaining all vertices, edges and original
lists under reversal of the native prescription. Girth separates any two
prescribed neighbours by at least three path edges. With at most six vertices,
the remaining pair is exactly the completed central case. Consequently an
interior vertex has at most one prescribed neighbour in any remaining
counterexample. This consequence retains `hbad` and the strict main induction;
it is not asserted for arbitrary graphs or arbitrary prescriptions without them.

Strict solution and axiom-audit builds passed. A separate challenge imports
none of the four new proof modules. Comparator, Lean and NanoDa accepted all
eight theorem contracts. Source audit: 106 solution modules, no proof holes,
custom axioms or native_decide. See `verification/prescribed-neighbour-*.log`
and `verification/prescribed-neighbour-hole-audit.json`.

Still open: interior two-path cuts with one prescribed internal endpoint and
one unprescribed endpoint; remaining three-path configurations and exceptional
final deletions; unconditional boundary extension and the actual main theorem.
The both-prescribed-endpoint two-path case is no longer pending. The unchanged
root main comparator still fails because the unconditional declaration is
absent: `verification/main-gate-after-prescribed-neighbours.log`. No publication
or Palomar submission was made.


## 2026-10-25 — Mixed two-path cuts reduced to the two six-vertex exceptions

**The unconditional main theorem remains unproved.** Mixed prescribed/free
interior two-path cuts are now complete for every old prescribed path with two
to five vertices. With six vertices, the only configurations surviving strict
induction are `r[2]--u--b` with `b` adjacent to the initial prescribed vertex,
and `r[3]--u--b` with `b` adjacent to the terminal prescribed vertex. Indices
start at zero. These are the two exceptions retained by the selected published
proof; neither has been claimed eliminated.

`FourEdgePendantGeometry` proves the short-path bound when independent leaves
may attach at the new terminal endpoint. `CompatibleEdgeStarPath` fixes a
compatible path with two new adjacent vertices, absorbs all old short
neighbours as independent leaves and applies the checked connected-prescription
induction only below the strict main bound. Girth proves unique attachment;
no capture condition or bound on the number of old short neighbours is assumed.

`RetainedPrescription` colours a proper induced piece retaining any connected
part of the old prescribed set, with every original list unchanged. The old
six-vertex bound proves the simple-path bound. `MixedPrescribedTwoPath` derives
the actual rebased cut and its two selected faces, retains the old prescribed
tail on the first side, fixes the compatible short prefix plus separator on
the second and glues the colours. Normalization, mirroring and reversal give
both end reductions for arbitrary original faces.

`MixedTwoPathExceptions` proves that a free vertex cannot adjoin both old path
ends and derives the two six-vertex exceptions. `MixedTwoPathClassification`
adds arbitrary-face endpoint exclusions and the index-free classification for
all mixed prescribed/free pairs (with at least two prescribed vertices).
`InteriorBoundaryNeighbours` separately proves unique unprescribed neighbours
on the full complementary arc. Together with prescribed-neighbour uniqueness,
this bounds all boundary neighbours of an interior vertex by two when the
prescribed path has at least three vertices, without a bound on facial length.

Strict solution and axiom-audit builds passed. A separate challenge imports
none of the seven new proof modules. Comparator, Lean and NanoDa accepted all
16 theorem contracts; there are no definition holes. Source audit: 113 solution
modules without proof holes, custom axioms or native_decide. Logs:
`verification/mixed-two-path-*.log`, `verification/mixed-two-path-hole-audit.json`.

Still open: remaining three-path configurations, final deletions (including the
two classified six-vertex exceptions), unconditional boundary extension and the
actual main theorem. The unchanged root main comparator still fails because
the unconditional declaration is absent; see
`verification/main-gate-after-mixed-two-paths.log`. No publication or Palomar
submission was made.


## 2026-10-25 — Structural three-path step and a longer-prescription deletion

**The unconditional main theorem is not proved.** The actual three-path cuts
with an unprescribed old short boundary endpoint are now closed for every
nontrivial prescribed path (two to six prescribed vertices). This includes
cuts dividing the original prescription, both native directions, arbitrary
original faces and paths whose other endpoint is prescribed. Three-paths from
either prescribed endpoint to a free boundary vertex are also closed without
restricting that free vertex's list size. Two free unrestricted three-list
endpoints remain a configuration of the final deletion argument.

`CompatibleShortEndedPath` handles a compatible induced path on at most six
vertices, whose two ends have old short lists and whose other new vertices lie
on one edge. All further old short neighbours form independent leaves with
unique attachment. The checked connected-prescription induction is applied
strictly below the original cardinal bound. `FiveEdgePathChordless` reduces
chordlessness to the possible longer chords; the actual mixed cut excludes them
using old short-list incompatibility and the verified endpoint two-path case.

`MixedPrescribedThreePath` constructs and glues the actual strict induced cut,
retaining the old tail unchanged on one side and fixing the compatible prefix
plus the three-edge separator on the other. The cut also handles a prescribed
endpoint (prefix length zero). `MixedThreePathClosure` derives arbitrary-face
normalization, reversal and selection of the shorter end of the old path, so
at most three original prescribed vertices enter the replacement path.
`ShortEndpointThreePath` covers both entirely free endpoint orders on the exact
complementary facial arc. `EndpointThreePath` proves the unrestricted-list
versions at both prescribed endpoints and packages the structural exclusion.

`ShortPathGoodFourthDeletion` proves full interior boundary-neighbour uniqueness
when the original prescription has two to five vertices. It then closes the
short-second/good-fourth-list deletion for **every** such prescribed path in
forward native facial order, retaining the entire old prescribed tail. The
first prescribed vertex and two backward free vertices are deleted. Every
remaining old singleton is preserved in its residual list; every new short-list
edge is excluded. The residual prescription is connected and has the proved
simple-path bound. The existing component-face and connected-prescription
extension handles disconnected remainders. No residual-colourability or
extension hypothesis is added.

The 13 three-path contracts and the two deletion contracts are compared in
separate challenges importing none of their respective new proof modules.
Strict solution builds, axiom audits, Comparator, Lean and NanoDa passed.
Source audit: 120 solution modules without proof holes, custom axioms or
native_decide. See `verification/three-path-*.log`,
`verification/good-fourth-path-*.log` and
`verification/three-path-and-deletion-hole-audit.json`.

Still open: the short-fourth-list final deletion for longer prescriptions,
the good-fourth-list branch for six prescribed vertices including its exceptional
mixed two-path, the complementary six-vertex exceptional deletion, and the
complete extension-induction assembly (including its starting states). These
are missing mathematical proofs. The actual main declaration is absent and the
unchanged root comparator fails at that declaration:
`verification/main-gate-after-three-paths.log`. No publication or Palomar
submission was made.


## 2026-10-25 — Three-vertex paths and the empty/singleton starting states closed

**The unconditional main theorem remains unproved.** The complete strict-
induction case for a prescribed path on three vertices is now closed, including
the alternating short-fourth-list branch, the six-vertex outer face, arbitrary
original facial placement and both native directions. Together with the earlier
edge case, all nontrivial prescriptions on at most three vertices are closed.

`ThreeVertexAlternatingLists` precolours the actual six-vertex boundary path
`e--d--b--a--p[1]--p[2]`, retaining all three old singleton colours. The only
enlarged list is the short fourth list, to which the prescribed colour at its
adjacent vertex `e` is added. The checked good-second-list reduction applies
at `e`; its resulting proper colouring cannot use the extra colour at that
fourth vertex, so all original lists are restored. `ThreeVertexSixFace` gives
compatible colour choices for the small outer six-cycle. The seven-vertex
alternating alternative is impossible by the original short-edge invariant.
`ThreeVertexPathClosure` assembles all branches and normalizes the original
face in either orientation.

`BoundaryPairClassification` classifies every distinct interior boundary-
neighbour pair as one of the two mixed six-vertex exceptions, in either order.
In particular a free old short vertex cannot take part in such a pair.
`SixPathGoodFourthDeletion` extends the good-fourth-list deletion to all six
permitted prescribed vertices whenever the backward exceptional pair is absent.
Its counterexample corollary proves that the remaining good-fourth branch
necessarily has a six-vertex prescription and that exact exceptional pair.
This is a case reduction, not an elimination of the exception.

`ShortArcSaturation` derives emptiness of the inner open region of a short
cycle following an old facial arc, using a genuine outside face vertex and the
already proved strict separating-short-cycle reduction. It proves that every
neighbour of an internal old arc vertex stays on that cycle. `ExceptionalFiveCycle`
applies this to the actual rebased five-cycle in the backward mixed exception:
the first two prescribed vertices have exactly their two cycle neighbours.
No empty-region or degree hypothesis is assumed.

`CurrentSmallStar` extends nontrivial stars on at most three vertices at the
current graph cardinality by the newly proved small-prescription case. Its
calls to the main induction remain strictly smaller. In a normalized smallest
counterexample with empty prescription, a root preceding an old short vertex
has at most two short neighbours, so this star closes the case. If all lists
have at least three colours, one actual boundary list is thinned to two and the
same case applies. `EmptyPrescriptionClosure` proves both branches.

`SingletonPrescriptionClosure` expands the old singleton list by a colour
allowed at a preceding facial neighbour. Fixing that neighbour to the added
colour through the same bounded star forces the old singleton vertex to keep
its original colour. All changed-list conditions are proved. The resulting
`LongPrescriptionReduction` eliminates empty, singleton, edge, three-vertex-path
and all permitted cycle prescriptions: every remaining counterexample must
prescribe a native path on **four to six vertices**.

Thirteen six-path/three-vertex contracts and six starting-state contracts pass
independent statement comparison and both Lean and NanoDa. Their challenges
import none of their respective new proof modules. Strict builds and axiom
audits pass; all permitted axioms remain propext, Classical.choice and Quot.sound.
Source audit: 131 solution modules without proof holes, custom axioms or
native_decide. See `verification/six-path-deletion-*.log`,
`verification/starting-states-*.log`, `verification/empty-prescription-strict-build.log`
and `verification/six-path-and-starting-states-hole-audit.json`.

Still open: the short-fourth-list final deletion for prescribed paths on four
to six vertices, elimination of the two six-vertex exceptional configurations,
and the resulting full extension-induction assembly. The empty/singleton
starting states and the three-vertex prescribed-path case are no longer
pending. The root main comparator is unchanged and still fails because the
unconditional declaration is absent:
`verification/main-gate-after-starting-states.log`. No publication or Palomar
submission was made.


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
