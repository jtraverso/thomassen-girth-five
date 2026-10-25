/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedEndpointDeletion

/-! Independent contracts for arbitrary facial subarcs, the short-endpoint
three-path case and old-short-list conflicts at prescribed endpoints.
None of the five proof modules implementing these contracts is imported.
The unconditional main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section FacialCycleRebaseContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Every forward cycle dart belongs to the original actual face orbit. -/
lemma facial_cycle_forward_sameCycle (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) (i : ZMod k) :
    SameCycle M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
      (toDart cyclicSubgraph_le (cycleForward hc i)) := by
  sorry

/-- A native cycle with the exact order of an indexed facial cycle inherits
its original face corners and exact first dart. -/
lemma ordered_native_cycle_isFacial (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length = k) (horder : ∀ i ≤ k, p.getVert i = c (i : ZMod k)) :
    IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧
      walkArcRoot p hp = toDart cyclicSubgraph_le (cycleForward hc 0) := by
  sorry

/-- Rebase the old actual facial cycle at any chosen native position, without
changing its orientation. Every new native vertex and the old face orbit are
retained explicitly. -/
theorem exists_rebased_native_face_cycle (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (s : ℕ) (hs : s < p.length) :
    ∃ q : G.Walk (p.getVert s) (p.getVert s), ∃ hq : q.IsCycle,
      q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s + i : ℕ) : ZMod p.length)) ∧
      IsFacialCycleAlong M (walk_isCycleMap q hq) Set.univ ∧
      SameCycle M.facePerm outer (walkArcRoot q hq) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The chordlessness reduction applies to every native representative of the
selected face, including representatives obtained by rebasing the initial dart. -/
lemma native_face_cycle_chordless_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : p.IsChordless := by
  sorry

end BoundaryInstance
end Thomassen

end FacialCycleRebaseContracts

section InteriorTwoPathSubarcContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Rebased native face intervals are exactly the corresponding old shifted
intervals, with all index and length casts accounted for. -/
lemma rebased_native_cycleInterval {a b : V} (p : G.Walk a a) (q : G.Walk b b)
    (s l : ℕ) (hlen : q.length = p.length)
    (horder : ∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s + i : ℕ) : ZMod p.length))
    (hl : 1 + l ≤ p.length) :
    cycleInterval (walkCycleVertices q) 1 l = cycleInterval (walkCycleVertices p) (s + 1) l := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The prescription-free two-edge reduction applies to any specified old
facial subarc. Rebasing, exact arc transport and chordlessness of the new native
representative are proved internally under the strict main induction. -/
theorem colourable_of_interior_two_path_free_subarc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hzs : G.Adj z (p.getVert s)) (hzn : G.Adj z (p.getVert n))
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- In a smallest counterexample, an interior vertex has at most one
neighbour on a specified closed facial arc whose open part avoids the original
prescription. Adjacent incidences violate girth; separated incidences give the
completed two-path subarc reduction. -/
lemma interior_neighbours_unique_on_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (n : ℕ) (hnp : n + 2 ≤ p.length)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (z : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n)
    (hzi : G.Adj z (p.getVert i)) (hzj : G.Adj z (p.getVert j)) : i = j := by
  sorry

end BoundaryInstance
end Thomassen

end InteriorTwoPathSubarcContracts

section InteriorThreePathReductionContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A three-edge interior path cutting off a prescription-free facial arc is
closed when its initial boundary endpoint has a short list. Two-path reductions
exclude interior incidences; the actual boundary captures the only possible
additional short endpoint neighbour. No capture hypothesis is supplied. -/
theorem colourable_of_interior_three_path_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists a).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The completed short-endpoint three-path case works on every specified
old facial subarc, with exact transport of its prescription-free condition. -/
theorem colourable_of_interior_three_path_free_subarc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u (p.getVert s)) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists (p.getVert s)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end InteriorThreePathReductionContracts

section PrescribedEndpointTwoPathContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A smallest counterexample has no interior two-edge path from a prescribed
endpoint to a distinct boundary vertex outside the open prescribed path. This
also covers the other prescribed endpoint. One old arc is proved prescription-
free from the exact orientation of the original path. -/
theorem no_interior_two_path_from_prescribed_endpoint_to_noninternal_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a)
    (hyInternal : ∀ k, 0 < k → k < r.length → r.getVert k ≠ y)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  sorry

/-- In particular the endpoint cannot have an interior two-path to an
unprescribed boundary vertex. -/
theorem no_interior_two_path_from_prescribed_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hyP : y ∉ I.precolor.vertices)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  sorry

/-- The remaining interior common-neighbour obstruction at a prescribed
endpoint can reach only native positions three or four of the prescription.
The other endpoint was excluded above, and girth excludes positions one/two. -/
lemma interior_endpoint_shared_neighbour_indices (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hyP : y ∈ I.precolor.vertices) (hya : y ≠ a) (hxa : G.Adj x a) (hxy : G.Adj x y) :
    ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ k < r.length ∧ r.getVert k = y := by
  sorry

end Thomassen.BoundaryInstance

end PrescribedEndpointTwoPathContracts

section EndpointResidualConflictsContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Root neighbours on a chordless native cycle are precisely its two
cyclic neighbours, expressed in the original natural-index convention. -/
lemma chordless_native_cycle_root_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    {x : V} (hx : x ∈ p.support) (hax : G.Adj a x) :
    x = p.getVert 1 ∨ x = p.getVert (p.length - 1) := by
  sorry

/-- The two neighbours of the old final cycle vertex are the root and the
old penultimate vertex. -/
lemma chordless_native_cycle_last_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    {x : V} (hx : x ∈ p.support) (hadj : G.Adj (p.getVert (p.length - 1)) x) :
    x = a ∨ x = p.getVert (p.length - 2) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- A neighbour of a prescribed endpoint that meets an old unprescribed
two-list must itself be on the original face. Interior witnesses are excluded
by the completed prescribed-endpoint two-path reduction. -/
lemma endpoint_old_short_conflict_on_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hyP : y ∉ I.precolor.vertices) (hys : (I.lists y).card ≤ 2)
    (hax : G.Adj a x) (hxy : G.Adj x y) : OnOuterFace I.embedding I.outer x := by
  sorry

/-- The old-short-list conflict is absent when the first forward face
neighbour is prescribed and the second backward face neighbour has a three-list.
This conclusion is derived, rather than supplied to endpoint deletion. -/
lemma prescribed_endpoint_no_old_short_conflicts (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ x, x ∉ r.support → G.Adj a x → ∀ y, y ∉ r.support → (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
  sorry

/-- With that actual boundary pattern the endpoint-deletion theorem no
longer needs an old-short-list-conflict hypothesis. The possible remaining
prescribed common neighbour is still explicit for longer prescribed paths. -/
theorem colourable_of_good_second_boundary_list (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hNoShared : ∀ x, x ∉ r.support → G.Adj a x → ∀ y ∈ r.support, y ≠ a → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The first final-deletion branch is fully closed for prescribed paths on
at most three vertices: the concrete boundary list bound supplies the old-short
exclusion and girth supplies the remaining-prescription exclusion. -/
theorem colourable_of_short_prescription_good_second_boundary_list (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length ≤ 2)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The same first deletion branch is closed for prescribed paths on up to
four vertices. Interior conflicts would require an internal prescribed index
three or four; boundary conflicts would force the three-list vertex prescribed. -/
theorem colourable_of_four_vertex_prescription_good_second_boundary_list (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length ≤ 3)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- A smallest counterexample with this short prescription must have at most
two colours at the second backward boundary neighbour. -/
lemma short_prescription_second_boundary_list_le_two (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length ≤ 2)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length - 2))).card ≤ 2 := by
  sorry

end BoundaryInstance
end Thomassen

end EndpointResidualConflictsContracts
