# Historical implementation and source-reuse notes

The text below records intermediate checkpoints. The main theorem is now proved;
current scope and pins are in ../THIRD_PARTY.md and ../README.md.

# Sources and reuse

## Existing formalizations

- `jtraverso/planar-list-colouring`, registered as
  **PALOMAR-2026-10-15-000005v1**, commit
  `ec1eafbc091713857eb5683a46e460902b2d47b3`.
  [Pinned source](https://github.com/jtraverso/planar-list-colouring/tree/ec1eafbc091713857eb5683a46e460902b2d47b3).
  The complete Lean library and the ten original Challenge/Solution contracts
  are retained. Aggregate Mathlib imports have been narrowed to actual
  dependencies, with additional explicit imports where necessary. Original proof
  bodies are preserved. New `col_of_erase` and `minimal_bad_connSet` apply the
  existing `col_extend` and `col_glue`; `delete_edge_boundary` applies the existing
  `isK5Boundary_delete` twice and then `isK5Boundary_anti`.
- `jtraverso/grotzsch-ore`, registered as
  **PALOMAR-2026-10-15-000005v2**, commit
  `ff6d5123c06e4c99bb6074e0a72e8be8d595eefa`.
  [Pinned source](https://github.com/jtraverso/grotzsch-ore/tree/ff6d5123c06e4c99bb6074e0a72e8be8d595eefa).
  Reused `LeanPool/K5MinorFreeChoosability/Planar/FaceApex.lean`,
  `Grotzsch/FacialCycle.lean`, and `Grotzsch/Regions.lean`. Added explicit
  `LinearCombination` and `Linarith` imports; renamed two unused lambda binders
  in `toDart_injective` to satisfy strict linting. The map restriction and region
  separation proofs are unchanged in substance. They are building blocks, not a
  list-colouring extension theorem.
  New `Thomassen/RegionSeparation.lean` applies these registered gap, component
  and chord results. New `Thomassen/FaceBoundary.lean` adapts the vertex-rotation
  splitting and Euler-defect argument from `Grotzsch/FacialCycle.lean` to prove
  face vertex injectivity under deletion connectivity.
  `Thomassen/InducedEmbedding.lean` uses the same restriction and permutation
  congruence infrastructure to construct actual smaller induced plane maps.
  `Thomassen/InducedInstance.lean` transports the original boundary invariant and
  reuses its list conditions in the disconnected induction case. No additional
  registered project has been copied for these modules.
  `Thomassen/FaceRestriction.lean` additionally uses the registered chord and
  outside-component gap theorems to follow an old face through a restriction.
  `ConnectedInstance.lean` uses Mathlib's actual connected components and their
  colouring-gluing homomorphism, plus the registered `col_of_erase` interface.
  `CutPrecolor.lean` uses native walk splitting and rotation of cycles to prove
  the prescribed-cutvertex case of the extension induction. No block-cut tree
  source has been imported or assumed.
  `CycleSeparation.lean` constructs concrete cycle sides using the same registered
  region/gap machinery. Its two cycle face orbits are proved directly from the
  rotation-system axioms. `CycleWalk.lean` uses native Mathlib walk indexing,
  support and edge identities. `ShortCycleReduction.lean` implements the
  separating-short-cycle induction step, corresponding to the short-proof
  exposition's Claim 6, with the actual list conditions checked. These modules
  do not assume a Jordan separation or an extension theorem as an axiom.
  `ChordSeparation.lean` reuses the same registered gap theorems R1/R2/R3 and
  native reachability to trim a facial arc. `PrescribedChordReduction.lean`
  uses the already verified induced-instance and gluing interfaces.
  `FiveCycle.lean`, `FacialFiveReduction.lean` and `FacialSixReduction.lean`
  reuse native walks, girth exclusions, boundary-vertex exposure, strict
  prescribed-cutvertex induction and `glue_residual`. The six-cycle obstruction
  uses the registered `CliqueMinorModel.ofConnSet`, `connSet_image_some` and
  `isK5Boundary_face`/face-apex infrastructure; no new planarity axiom or
  external extension theorem is assumed. The explicit rooted-four-bag argument
  closes this local exceptional configuration, not the full extension induction.
  `EdgeCutPrecolor.lean` reuses native Mathlib edge-subwalk decomposition,
  rotations, path/cycle support and edge identities, and the checked cutvertex
  branch lemma. `EdgeCutReduction.lean` uses the checked induced-instance and
  gluing interfaces with exact prescribed intersections. `InteriorCutReduction.lean`
  uses the already proved native cut sides, connectivity of a face's vertices,
  induced plane maps and original singleton-list gluing. No additional external
  source files or mathematical extension theorem were imported for these steps.
  `FaceMerge.lean` reuses the registered component-gap theorem R1 and the
  verified face projection. `ArcPathSeparation.lean` reuses the same region
  and first-return machinery to construct the exterior skeleton and its
  face merger; no Jordan or extension axiom is introduced. `CycleIntervals.lean`
  and `NativeArcPathCut.lean` use Mathlib indexing, modular arithmetic and walk
  suffixes to identify exact native separators. `ShortPathColouring.lean`
  uses Mathlib's native walk-chord predicate, the previously proved girth
  exclusions, induced instances and colouring glue. These proofs implement
  geometric and list-condition steps needed by the chosen short-proof family;
  they do not supply its still-missing complete induction.
- The registered Brooks/degree-choosability package at
  `jtraverso/brooks`, commit `b99e6f500256586626396de9c2d6fd4d96119d60`,
  was inspected for greedy list-colouring and extension interfaces. No code from
  that package has been copied into this checkpoint.
- Mathlib, Apache-2.0, commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`. Uses native
  `SimpleGraph.egirth`, walks, cycles, proper colourings and finite sets.
  Forests have infinite extended girth, so the condition is `5 ≤ G.egirth`.

All reused project source notices name Juan Pablo Traverso Gianini and retain
Apache-2.0 licensing. Upstream papers and other attribution remain documented in
`upstream-planar/README.md` and the copied source modules.

## Mathematical references

- C. Thomassen, *3-List-Coloring Planar Graphs of Girth 5*, Journal of Combinatorial
  Theory B 64 (1995), 101–107, doi:10.1006/jctb.1995.1027. The publisher abstract
  and bibliographic record were consulted initially. On 2026-10-24 the user supplied
  a valid scanned original in a ZIP; all seven pages, including Theorem 2.1 and
  its proof, were read directly. See `SOURCE_REVIEW.md` for provenance and the
  distinction from the earlier invalid publisher-page attachments.
  The target is the finite 3-choosability theorem, not a claim
  to reproduce every result of that paper.
- C. Thomassen, *A short list color proof of Grötzsch’s theorem*, JCT B 88 (2003),
  189–192, doi:10.1016/S0095-8956(03)00029-7. The bibliographic record was consulted.
- L. Jin, Y. Kang and E. Steffen, *Choosability in signed planar graphs*,
  arXiv:1502.04561v2, appendix Theorem 5.1, pp. 11–13,
  [consulted full text](https://arxiv.org/pdf/1502.04561).
  Its proof explicitly follows Thomassen's short proof. The unsigned specialization
  provides the boundary-extension proof roadmap. That main induction is still
  unformalized here; no signed-graph theorem is assumed.
- Z. Dvořák and K. Kawarabayashi, *Choosability of planar graphs of girth 5*,
  [arXiv:1109.2976](https://arxiv.org/pdf/1109.2976), Theorem 1, pp. 1–2.
  Consulted for the precise precoloured-path/list-size invariant. The much stronger
  theorem developed in that paper is not a completed dependency of this project.
- N. Asghar, *Grötzsch's Theorem*, Waterloo research essay (2012), Chapter 3,
  Theorem 3.2.1 and its proof, printed pp. 37–52,
  [consulted text](https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf).
  That chapter attributes its approach to unpublished work of C. Nunes da Silva,
  R. B. Richter and D. Younger. It supplies an expanded list-extension roadmap;
  the main induction remains unformalized.
- Z. Dvořák, *A simplified discharging proof of Grötzsch theorem*,
  [arXiv:1311.7636](https://arxiv.org/pdf/1311.7636), and Z. Dvořák,
  K. Kawarabayashi and R. Thomas, *Three-coloring triangle-free planar graphs in
  linear time*, [2008 preprint](https://kam.mff.cuni.cz/kamserie/clanky/2008/s887.pdf).
  Consulted for ordinary-colouring reductions; neither is used as an
  arbitrary-list extension theorem.
- D. W. Cranston, *Graph Coloring Methods* (2024),
  [§11.4, Theorem 11.13, pp. 322–328](https://graphcoloringmethods.com/GraphColoringMethods.pdf).
  The relevant section was read through its final case. It is the current
  expanded proof roadmap for the existing six-vertex invariant; the full
  induction is not yet formalized.
- M. Han, T. Wang, J. Wu, H. Zhou and X. Zhu, *Weak degeneracy of planar graphs
  and locally planar graphs*, EJC 30(4), P4.18 (2023),
  [published text](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i4p18/pdf/),
  doi:10.37236/11749. Sections 1–3 were compared with arXiv:2303.07901v1;
  the surface theorem was not reviewed. This alternative is not a proved Lean
  dependency.
- Additional primary-source screening, with exact reading scopes and links, is
  documented in `CLOSURE_PLAN.md`: Dvořák–Lidický–Škrekovski (2010),
  Postle–Smith-Roberge (2022), Davies–Smith-Roberge (2025), Dvořák–Postle's
  correspondence-colouring paper, and the 2020 islands seminar announcement.
  The announcement is not treated as a complete proof text. These sources were
  assessed as alternative routes; no proof code or full copyrighted text was
  copied from them.

The native facial-cycle construction additionally reuses Mathlib's
`cycleGraph.cycle` and periodic-point API, and the registered
`Planar.Nonplanar.face_ne_self` / `face_face_ne_self` lemmas. These are imports;
no upstream proof modules were modified. The augmented-prescription reductions
implement the additional short-neighbour step in the same short-proof roadmap,
with the remaining capture conditions stated explicitly.

The cutvertex-fan proof uses the same short-proof roadmap in the sources above:
fix the attachment colour, colour its short neighbours, and split the fan into
small prescribed paths. The implementation supplies a separate strong induction
on actual induced graphs, reusing the checked face, chord and component APIs.
The prescribed-cycle normalization reuses the previously checked facial-cycle
and prescribed-edge-cut reductions. No external prover was invoked.

The two-endpoint fan induction is an implementation strategy for the same
short-proof chord step, using the registered and previously checked one-root
fan and actual facial cuts. It avoids assuming a minimal cut in the completed
two-unprescribed-end and prescribed-path-endpoint cases. This does not close
the mixed internal-prescription or short-path cases in the cited proof.

The private-leaf list release, short-branch mixed-cut reduction and native
path-order normalization continue the same source proof route. They reuse the
verified two-endpoint fan induction, exact native path splitting and facial
chord geometry. The remaining central mixed chords, short interior paths and
final deletion cases have not been supplied by an external theorem or service.

The subsequent anchored-fan induction completes the boundary-chord step of
this proof route. It retains the old short prescription, reuses the checked
root/two-endpoint fans on separated pieces, and proves every auxiliary strict
decrease and native facial base. The central branch-length selection uses the
original six-vertex bound. Short interior-path separators and final deletions
remain unproved; no source theorem is treated as a Lean proof of those steps.

The native face/path splicing and first-incidence selection implement part of
the short-interior-path step using the verified actual-plane-map separation APIs.
The prescription-free two-path arc case is proved, including all changed-list
conditions. The proof does not invoke the full published Claim 5.1.5 or 5.1.6 as
a Lean dependency; the remaining prescription-splitting and final-deletion cases
are still open.

The prescribed-path endpoint deletion extends the earlier checked facial-cycle
deletion to an exact native path, retaining singleton prescriptions and old
short-list constraints. Its general theorem keeps the geometric exclusions
explicit, and its obstruction lemma records concrete remaining configurations.
It is not an invocation of the unformalized final source-proof cases.

The subsequent subarc reductions implement more of the same short-proof route.
Native rebasing preserves actual face darts and interval supports. The complete
two-path arc reduction controls interior incidences in the initial-short-endpoint
three-path case. Original prescribed-path orientation selects the free arc at a
prescribed endpoint. The endpoint conflict classification and good-second-list
deletion case use the checked girth, chord and residual-list proofs. Neither the
full remaining five/six-vertex cases nor final multi-vertex deletions are treated
as available external proofs.

The prescribed-prefix two-path cuts implement the endpoint part of the same
published short-path argument using the already checked actual facial cuts.
Compatible colours and both replacement prescriptions are constructed in Lean.
The full good-second-boundary-list endpoint-deletion branch, including original
paths on five/six prescribed vertices, is now proved under strict induction.
Other short-path cuts and final exceptional deletions are still open; neither
the published extension theorem nor an external prover is used as a hypothesis.

The later connected boundary deletion reuses the actual connected-omission
face-merger theorem separately on each retained component. The prescribed-edge
short-second/good-fourth-list branch checks all residual conflicts using the
proved two/three-path reductions. Completion of the five/six-vertex actual
outer-face cases reuses the checked full prescribed-cycle extension; the
five-vertex boundary colours are explicitly constructed. These are parts of
the same selected short-proof route, not an invocation of its remaining final
cases as external Lean theorems.

The alternating-list case is closed by a compatible five-vertex boundary
precolouring, assembled from the verified facial rebasing, short-edge invariant
and good-second-list induction case. Its single list enlargement is restored
using an adjacent prescribed colour. The implementation checks the whole new
instance and invokes only the existing strict induction; it does not assume
the published extension theorem or any new extension principle.

New Lean proof code was produced with OpenAI Codex under the author's direction.
No sub-agents or external theorem-proving service were used. Mechanical support
checks do not establish the still-missing main mathematical proof.

The connected-prescription auxiliary induction packages the boundary-piece
splitting used by the same short-proof route. Its clique retractions, bounded
branching core, native maximum-degree-two base and actual component-face
transport are proved locally using the previously checked infrastructure.
The one-vertex complement case explicitly chooses and restores all colours,
including the independent newly shortened neighbours attached to the old path.
The corresponding two-vertex complement and exceptional later configurations
are not treated as available external theorems. Mirror embeddings are built
from the existing permutation and plane-map definitions, preserving the full
selected face vertex set and native corner equations.

The two-vertex complement completes the short-complement reduction of the same
selected proof route. Its implementation reuses the proved edge-deletion
independence, short-cycle neighbour bound, actual component-face merger and
connected-prescription induction. The complementary edge and its compatible
colours are derived locally, and every residual invariant is checked. The
resulting lower bound on free boundary vertices is proved by exact finite-set
cardinality. No remaining prescription-splitting or exceptional configuration
is invoked as an external extension theorem.

The central two-path case follows the same selected short-proof route. Its
local formal proof constructs the actual rebased face, interior five-cycle,
exterior five-vertex path, compatible colours and strict gluing. The old-short
neighbour issue is resolved with the previously verified connected-prescription
induction, via a compatible-path-star extension proved locally. Native
orientation, terminal path reversal and the girth-based index classification
are checked rather than assumed. The mixed prescribed/unprescribed two-path
and exceptional later configurations remain explicit unfinished work.


The mixed prescribed/free two-path reduction follows the same selected
Jin–Kang–Steffen Appendix 5.1.5 / Cranston short-proof route. The local Lean
implementation constructs and glues actual strict induced cuts, using the
previously proved connected-prescription extension to colour all short leaves.
It independently checks the two exceptional six-vertex configurations, retaining
them for the final deletion step rather than claiming that they are eliminated.
The independent contract imports only previously checked prerequisites, not any
of the seven new proof modules.


The structural three-path reductions follow the same Jin–Kang–Steffen Appendix
5.1.6 / Cranston short-proof route. All actual cuts, short-neighbour attachments,
replacement paths, native orientation and gluing are proved locally in Lean.
The good-fourth-list deletion reuses the earlier checked edge-prescription
argument while retaining the whole old path tail and checking its residual
singleton colours. The alternating and six-vertex exceptional final deletions
are still unfinished; no proof of them is imported or assumed.


The three-vertex alternating-list case and compatible six-cycle completion
continue the selected short-proof route. Actual native paths, allowed colours,
restoration of the one enlarged list and strict induction are checked locally.
The current-cardinality small-star, empty-prescription and singleton-prescription
proofs reuse the already checked root-star constructions and the newly closed
three-vertex case. Their main-induction calls are still strictly smaller.
Short facial-arc saturation is derived from the existing separating-short-cycle
proof, not assumed from a drawing. The exceptional final colouring remains open.
