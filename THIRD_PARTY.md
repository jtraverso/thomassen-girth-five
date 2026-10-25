# Sources, reuse and attribution

## Existing formalizations

- **planar-list-colouring**, `jtraverso/planar-list-colouring`, registered as
  **PALOMAR-2026-10-15-000005v1**, pinned commit
  `ec1eafbc091713857eb5683a46e460902b2d47b3`.
  [Pinned source](https://github.com/jtraverso/planar-list-colouring/tree/ec1eafbc091713857eb5683a46e460902b2d47b3).
  The `LeanPool/K5MinorFreeChoosability` library and original Challenge/Solution
  contracts provide list-colouring glue and extension, restrictions, minors,
  rotation systems and planarity. Aggregate imports were narrowed; proof bodies
  remain preserved as documented in `verification/source-reuse.json`.
- **grotzsch-ore**, `jtraverso/grotzsch-ore`, registered as
  **PALOMAR-2026-10-15-000005v2**, pinned commit
  `ff6d5123c06e4c99bb6074e0a72e8be8d595eefa`.
  [Pinned source](https://github.com/jtraverso/grotzsch-ore/tree/ff6d5123c06e4c99bb6074e0a72e8be8d595eefa).
  Reused `LeanPool/K5MinorFreeChoosability/Planar/FaceApex.lean`,
  `Grotzsch/FacialCycle.lean` and `Grotzsch/Regions.lean` for actual face orbits,
  map restriction and gap/region separation. Adaptations are explicit imports
  and two unused-binder renamings in Regions; proof substance is retained.
- **Mathlib**, pinned commit `c55e6e786f49471c72fbddbec5415808896aec1e`,
  Lean `v4.35.0-rc3`. Uses native simple graphs, walks, paths, extended girth,
  induced graphs, connected components, finite lists and permutations.
  Relevant definitions are reproduced with attribution in `MATHLIB_DEFINITIONS.md`.

Reused source notices and Apache-2.0 licences are retained. Their notices name
Juan Pablo Traverso Gianini; upstream paper attribution remains in the source
modules and `upstream-planar/README.md`. The original prerequisite contracts are
preserved. Source hashes and exact adaptation notes are recorded in
`verification/source-reuse.json`; detailed historical notes are retained in
`verification/source-reuse-notes.md`.

The new proof supplies its own boundary invariant, actual induced-face and
separator geometry, compatible partial colours, residual bounds, connected
branching prescriptions and strong induction. In the final six-vertex case,
newly short vertices attached to internal prescribed vertices are treated as
pendant branches. At the inner five-face, girth excludes simultaneous prescribed
neighbours at both adjacent interior vertices; explicit colours preserve all old
singletons. These are locally proved reductions, not calls to an external
list-extension theorem. The complete boundary-extension and unconditional
three-choosability theorems are proved in `Thomassen/BoundaryExtension.lean`.

## Mathematical references

- C. Thomassen, *3-List-Coloring Planar Graphs of Girth 5*, Journal of Combinatorial
  Theory B 64 (1995), 101–107, doi:10.1006/jctb.1995.1027. The publisher abstract
  and bibliographic record were consulted initially. On 2026-10-24 the user supplied
  a valid scanned original in a ZIP; all seven pages, including Theorem 2.1 and
  its proof, were read directly. See `SOURCE_REVIEW.md` for provenance and the
  distinction from the earlier invalid publisher-page attachments.
  The completed scope now includes the finite 3-choosability theorem,
  both alternatives of the full original Theorem 2.1 and Corollary 2.2.
  The exceptional branch follows original reductions (9) and (10), with
  the already proved independent branch supplying the rest of the induction.
  Intermediate proof reductions are exposed where useful; a separate Lean
  declaration for every sentence is not claimed.
- C. Thomassen, *A short list color proof of Grötzsch’s theorem*, JCT B 88 (2003),
  189–192, doi:10.1016/S0095-8956(03)00029-7. The bibliographic record was consulted.
- L. Jin, Y. Kang and E. Steffen, *Choosability in signed planar graphs*,
  arXiv:1502.04561v2, appendix Theorem 5.1, pp. 11–13,
  [consulted full text](https://arxiv.org/pdf/1502.04561).
  Its proof explicitly follows Thomassen's short proof. The unsigned specialization
  provides the boundary-extension proof roadmap. The local proof implements
  the unsigned boundary-extension induction; no signed-graph theorem is assumed.
- Z. Dvořák and K. Kawarabayashi, *Choosability of planar graphs of girth 5*,
  [arXiv:1109.2976](https://arxiv.org/pdf/1109.2976), Theorem 1, pp. 1–2.
  Consulted for the precise precoloured-path/list-size invariant. The much stronger
  theorem developed in that paper is not a completed dependency of this project.
- N. Asghar, *Grötzsch's Theorem*, Waterloo research essay (2012), Chapter 3,
  Theorem 3.2.1 and its proof, printed pp. 37–52,
  [consulted text](https://uwaterloo.ca/combinatorics-and-optimization/sites/default/files/uploads/documents/nabiha_asghar.pdf).
  That chapter attributes its approach to unpublished work of C. Nunes da Silva,
  R. B. Richter and D. Younger. It supplies an expanded list-extension roadmap;
  its alternative simultaneous-state induction is not used as a Lean dependency.
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
  boundary-extension induction is now proved locally.
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


## Assistance and review

New Lean code was produced with OpenAI Codex under the author's Spanish-language
direction. No sub-agents or external theorem-proving service were used. Existing
work from the author's reserved repositories was not modified. The agent reviewed
the statements and ran compilation, source/axiom audits, independent statement
comparison and Lean/NanoDa checks. This is not independent human review.
No mathematical novelty or priority claim is made. Registry verification and
editorial review are separate from the local checks.

## Requested additional results (1–4)

- Dvořák–Kawarabayashi, *Choosability of planar graphs of girth 5* (2011),
  arXiv:1109.2976, Theorem 1, which attributes the result to Thomassen.
  `PublicBoundaryExtension` and `PublicBoundaryGlobal` provide source-aligned
  interfaces, including proper prescribed chords and multiple exterior components.
  The paper's stronger Theorem 3 and quantitative criticality results are not claimed.
- Rado (1949), *Axiomatic Treatment of Rank in Infinite Sets*, CJM 1, 337–343,
  doi:10.4153/CJM-1949-031-1, and de Bruijn–Erdős (1951), *A colour problem for
  infinite graphs and a problem in the theory of relations*, Proc. KNAW A 54,
  371–373, supply the classical compactness provenance. `InfiniteChoosability`
  directly reuses `Finset.rado_selection_subtype` from Mathlib's
  `Combinatorics/Compactness.lean`, copyright 2025 Bhavik Mehta, Apache-2.0.
  Its proof body is imported, not copied or presented as new work. Original-paper
  bibliographic metadata were checked; neither entire classical paper was ported.
- `ArbitraryShortCycle` implements the arbitrary-five-cycle extension described
  in Thomassen (1995), plus the six-cycle consequence of the already proved
  short-boundary theorem. It uses actual induced sides and agreement on the cycle.
- Asghar (2012), *Grötzsch's Theorem*, Waterloo MMath research essay, Lemma
  3.2.3, provides the known outer-seven-cycle statement. Her Chapter 3 attributes
  the proof to unpublished work of C. Nunes da Silva, R. B. Richter and D. Younger,
  inspired by Thomassen. `OuterSevenCycle` proves the girth-five specialization
  by releasing a vertex whose neighbours have distinct colours. It does not port
  the essay's simultaneous three-state induction or prove its outer-four-cycle
  exception. No original mathematical theorem is claimed.

The README contains the source URLs, exact scope and declaration mapping for a
future Palomar submission. These additions are local formalization work; they
have not been separately published or registered in this step.
