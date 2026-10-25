/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedEndpointTwoPath

/-! Resolving old two-list conflicts at an original prescribed endpoint. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Root neighbours on a chordless native cycle are precisely its two
cyclic neighbours, expressed in the original natural-index convention. -/
lemma chordless_native_cycle_root_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    {x : V} (hx : x ∈ p.support) (hax : G.Adj a x) :
    x = p.getVert 1 ∨ x = p.getVert (p.length - 1) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hzero : walkCycleVertices p 0 = a := by simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hplus : walkCycleVertices p 1 = p.getVert 1 := by
    simpa only [Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
  have hmcast : ((p.length - 1 : ℕ) : ZMod p.length) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p.length), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hminus : walkCycleVertices p (-1) = p.getVert (p.length - 1) := by
    rw [← hmcast, walkCycleVertices_nat_le p (by omega)]
  have hedge := (walkCycleVertices_edges p hp a x).2 (hch.mem_edges p.start_mem_support hx hax)
  have hedge0 : (cyclicSubgraph G (walkCycleVertices p)).Adj (walkCycleVertices p 0) x := by simpa only [hzero] using hedge
  simpa only [zero_add, zero_sub, hplus, hminus] using (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) 0 x).1 hedge0

/-- The two neighbours of the old final cycle vertex are the root and the
old penultimate vertex. -/
lemma chordless_native_cycle_last_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    {x : V} (hx : x ∈ p.support) (hadj : G.Adj (p.getVert (p.length - 1)) x) :
    x = a ∨ x = p.getVert (p.length - 2) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hzero : walkCycleVertices p 0 = a := by simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hmcast : ((p.length - 1 : ℕ) : ZMod p.length) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p.length), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hminus : walkCycleVertices p (-1) = p.getVert (p.length - 1) := by
    rw [← hmcast, walkCycleVertices_nat_le p (by omega)]
  have hm2cast : ((p.length - 2 : ℕ) : ZMod p.length) = -2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p.length), ZMod.natCast_self, Nat.cast_ofNat, zero_sub]
  have hminus2 : walkCycleVertices p (-2) = p.getVert (p.length - 2) := by
    rw [← hm2cast, walkCycleVertices_nat_le p (by omega)]
  have hedge := (walkCycleVertices_edges p hp _ x).2 (hch.mem_edges (p.getVert_mem_support _) hx hadj)
  rw [← hminus] at hedge
  simpa only [neg_add_cancel, show (-1 : ZMod p.length) - 1 = -2 by ring, hzero, hminus2] using
    (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) (-1) x).1 hedge

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
  by_contra hx
  have hyface : OnOuterFace I.embedding I.outer y := by
    by_contra hy
    have h3 := I.interior_lists y hy
    omega
  exact I.no_interior_two_path_from_prescribed_endpoint hG p hp hface hroot hExact r hr hP hbad hsmall
    x y hx hyface hyP hax.symm hxy

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
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  intro x hx hax y hy hys hxy
  have hyP : y ∉ I.precolor.vertices := fun h => hy ((hP y).1 h)
  have hyface : OnOuterFace I.embedding I.outer y := by
    by_contra h
    have h3 := I.interior_lists y h
    omega
  have hxface := I.endpoint_old_short_conflict_on_boundary hG p hp hface hroot hExact r hr hP hbad hsmall x y hyP hys hax hxy
  rcases chordless_native_cycle_root_neighbours p hp hch (hExact x hxface) hax with hx1 | hxlast
  · have hxP : x ∈ I.precolor.vertices := by rw [hx1]; exact hfirst
    exact hx ((hP x).1 hxP)
  · have hlasty : G.Adj (p.getVert (p.length - 1)) y := by rwa [hxlast] at hxy
    rcases chordless_native_cycle_last_neighbours p hp hch (hExact y hyface) hlasty with hya | hy2
    · exact hy (hya ▸ r.start_mem_support)
    · rw [hy2] at hys
      omega

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
  by_contra hbad
  have hPv : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support := by simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hNoOld := I.prescribed_endpoint_no_old_short_conflicts hG p hp hface hroot hExact r hr hPv hfirst hsecond hbad hsmall
  exact hbad (I.colourable_of_prescribed_endpoint_deletion hG r hr hn hP hNoShared hNoOld hsmall)

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
  apply I.colourable_of_good_second_boundary_list hG p hp hface hroot hExact r hr hn hP hfirst hsecond ?_ hsmall
  intro x hx hax y hy hya hxy
  exact hya (external_short_path_neighbour_unique I.girth r hr hrlen r.start_mem_support hx hax.symm hy hxy)

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
  by_contra hbad
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hPv : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support := by simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hNoShared : ∀ x, x ∉ r.support → G.Adj a x → ∀ y ∈ r.support, y ≠ a → ¬ G.Adj x y := by
    intro x hx hax y hy hya hxy
    have hyP : y ∈ I.precolor.vertices := (hPv y).2 hy
    by_cases hxface : OnOuterFace I.embedding I.outer x
    · rcases chordless_native_cycle_root_neighbours p hp hch (hExact x hxface) hax with hx1 | hxlast
      · have hxP : x ∈ I.precolor.vertices := by rw [hx1]; exact hfirst
        exact hx ((hPv x).1 hxP)
      · have hlasty : G.Adj (p.getVert (p.length - 1)) y := by rwa [hxlast] at hxy
        rcases chordless_native_cycle_last_neighbours p hp hch (hExact y (I.on_outer y hyP)) hlasty with hya' | hy2
        · exact hya hya'
        · have hycard : (I.lists y).card = 1 := by simp only [I.singleton y hyP, Finset.card_singleton]
          rw [hy2] at hycard
          omega
    · obtain ⟨k, hk, hklt, _⟩ := I.interior_endpoint_shared_neighbour_indices hG p hp hface hroot hExact r hr hn hP hbad hsmall
        x y hxface hyP hya hax.symm hxy
      omega
  exact hbad (I.colourable_of_good_second_boundary_list hG p hp hface hroot hExact r hr hn hP hfirst hsecond hNoShared hsmall)

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
  by_contra h
  exact hbad (I.colourable_of_short_prescription_good_second_boundary_list hG p hp hface hroot hExact r hr hn hP hrlen hfirst (by omega) hsmall)

end BoundaryInstance
end Thomassen
