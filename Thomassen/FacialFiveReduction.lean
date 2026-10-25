/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FiveCycle
public import Thomassen.CutPrecolor

/-! Facial prescribed cycles with no shared exterior neighbour. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- Delete and restore one vertex of a prescribed facial cycle of at most six
vertices, when its new two-lists have no neighbour in the remaining prescription.
The cutvertex alternative uses the already verified reduction. -/
theorem colourable_of_facial_cycle_without_shared_neighbours (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hNoShared : ∀ x, x ∉ p.support → G.Adj a x → ∀ y ∈ p.support, y ≠ a → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  classical
  have hlen := hp.three_le_length
  have hUpper : p.length ≤ 6 := by rwa [cycle_support_card_eq_length p hp] at hbound
  have haP := (hP a).2 p.start_mem_support
  let S : Set V := ({a} : Set V)ᶜ
  by_cases hremain : (G.induce S).Preconnected
  swap
  · exact I.colourable_of_precolored_cutvertex a haP hconn hremain hsmall
  have h1 : p.getVert 1 ≠ a := by
    intro h
    have he := (hp.getVert_endpoint_iff (i := 1) (by omega)).1 h
    omega
  have h2 : p.getVert 2 ≠ a := by
    intro h
    have he := (hp.getVert_endpoint_iff (i := 2) (by omega)).1 h
    omega
  have h12 : (G.induce S).Adj ⟨p.getVert 1, h1⟩ ⟨p.getVert 2, h2⟩ :=
    p.adj_getVert_succ (by omega : 1 < p.length)
  let : Nontrivial S := h12.nontrivial
  obtain ⟨outer, hOldFace, hNeighbour⟩ := exists_outer_after_boundary_vertex I.embedding I.outer a
    (I.on_outer a haP) hremain
  let r : V → Finset C := residual G I.lists {a} I.prescribed
  have hL3 : ∀ x, x ∉ p.support → 3 ≤ (I.lists x).card :=
    fun x hx => I.interior_lists x (fun hf => hx ((hface x).1 hf))
  have hResP : ∀ x ∈ p.support, r x = {I.prescribed x} := by
    intro x hx
    have hOrig := I.singleton x ((hP x).2 hx)
    apply Finset.Subset.antisymm
    · have h := residual_subset G I.lists {a} I.prescribed x
      rwa [hOrig] at h
    · apply Finset.singleton_subset_iff.2
      apply (mem_residual_iff I.lists {a} I.prescribed x _).2
      refine ⟨by simp only [hOrig, Finset.mem_singleton], ?_⟩
      intro y hy hxy
      have heq : y = a := Finset.mem_singleton.1 hy
      subst y
      exact I.proper_on_precolored_vertices ((hP x).2 hx) haP hxy
  have hNewShort : ∀ x, x ∉ p.support → (r x).card ≤ 2 → G.Adj a x := by
    intro x hx hshort
    obtain ⟨y, hy, hyx⟩ := short_residual_neighbor I.lists {a} I.prescribed x (hL3 x hx) hshort
    have heq : y = a := Finset.mem_singleton.1 hy
    exact heq ▸ hyx
  have hResTwo : ∀ x, x ∉ p.support → 2 ≤ (r x).card := by
    intro x hx
    have hcount : (({a} : Finset V).filter (G.Adj x)).card ≤ 1 := by
      calc
        _ ≤ ({a} : Finset V).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := Finset.card_singleton a
    exact residual_three_to_two I.lists {a} I.prescribed x (hL3 x hx) hcount
  let q := p.tail.dropLast
  have hqsmall : q.support.toFinset.card ≤ 6 := by
    calc
      _ ≤ p.support.toFinset.card := Finset.card_le_card (fun x hx => List.mem_toFinset.2
        ((cycle_tail_dropLast_support p hp x).1 (List.mem_toFinset.1 hx)).1)
      _ ≤ 6 := hbound
  let P : BoundaryPrecolor G := .path q hp.isPath_tail.dropLast hqsmall
  have hPS : ∀ x ∈ P.vertices, x ∈ S := fun x hx =>
    ((cycle_tail_dropLast_support p hp x).1 (List.mem_toFinset.1 hx)).2
  let Q := P.induce S hPS
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ p.support := by
    intro x
    rw [BoundaryPrecolor.mem_vertices_induce]
    change x.1 ∈ q.support.toFinset ↔ x.1 ∈ p.support
    simp only [q, List.mem_toFinset, cycle_tail_dropLast_support p hp]
    exact ⟨And.left, fun hx => ⟨hx, x.2⟩⟩
  let : NeZero p.length := ⟨by omega⟩
  have hch := short_cycle_isChordless I.girth (walk_isCycleMap p hp) hp.three_le_length hUpper
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := outer
    precolor := Q
    lists := fun x => r x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := fun x hx => hOldFace x ((hface x.1).2 ((hQv x).1 hx))
    singleton := fun x hx => hResP x.1 ((hQv x).1 hx)
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact I.proper_on_precolored_vertices ((hP x.1).2 ((hQv x).1 hends.1))
        ((hP y.1).2 ((hQv y).1 hends.2)) (Q.adj_of_mem_edges he)
    boundary_lists := fun x _ hx => hResTwo x.1 (fun h => hx ((hQv x).2 h))
    interior_lists := by
      intro x hx
      have hNoAdj : ¬ G.Adj x.1 a := fun h => hx (hNeighbour x h)
      have hNoOld : ¬ OnOuterFace I.embedding I.outer x.1 := fun h => hx (hOldFace x h)
      have heq : r x.1 = I.lists x.1 := by
        apply residual_unchanged
        intro y hy
        have heq : y = a := Finset.mem_singleton.1 hy
        exact heq.symm ▸ hNoAdj
      rw [heq]
      exact I.interior_lists x.1 hNoOld
    short_edges := by
      intro x y hxy hx hy
      by_cases hxC : x.1 ∈ p.support <;> by_cases hyC : y.1 ∈ p.support
      · apply (BoundaryPrecolor.mem_edges_induce P S hPS x y).2
        apply List.mem_toFinset.2
        apply (cycle_tail_dropLast_edges p hp x.2 y.2).2
        apply (walkCycleVertices_edges p hp x.1 y.1).1
        apply cyclicSubgraph_of_chordless hch
        · rwa [walkCycleVertices_range p hp]
        · rwa [walkCycleVertices_range p hp]
        · exact hxy
      · exact (hNoShared y.1 hyC
          (hNewShort y.1 hyC hy) x.1 hxC x.2 hxy.symm).elim
      · exact (hNoShared x.1 hxC
          (hNewShort x.1 hxC hx) y.1 hyC y.2 hxy).elim
      · exact (neighbors_nonadjacent I.girth (hNewShort x.1 hxC hx)
          (hNewShort y.1 hyC hy) hxy).elim }
  obtain ⟨col, hcol⟩ := hsmall S (G.induce S) J
    (card_induced_vertices_lt S (x := a) (by simp [S]))
  have hc : ∀ x : S, col x ∈ r x.1 := hcol
  let d : V → C := fun x => if hx : x = a then I.prescribed x else col ⟨x, hx⟩
  have hne : ∀ x, x ∈ (Finset.univ \ ({a} : Finset V)) → x ≠ a :=
    fun x hx heq => (Finset.mem_sdiff.1 hx).2 (Finset.mem_singleton.2 heq)
  apply (col_univ_iff I.lists).1
  refine glue_residual Finset.univ {a} I.lists I.prescribed d ?_ ?_ ?_ ?_
  · intro x hx
    have heq : x = a := Finset.mem_singleton.1 hx
    subst x
    simp only [I.singleton a haP, Finset.mem_singleton]
  · intro x hx y hy hxy
    exact (hxy.ne ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm)).elim
  · intro x hx
    simpa only [d, dite_eq_right (hne x hx)] using hc ⟨x, hne x hx⟩
  · intro x hx y hy hxy
    simpa only [d, dite_eq_right (hne x hx), dite_eq_right (hne y hy)] using
      col.valid (show (G.induce S).Adj ⟨x, hne x hx⟩ ⟨y, hne y hy⟩ from hxy)

/-- The full five-cycle case: girth excludes the shared-neighbour obstruction. -/
theorem colourable_of_facial_five_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 5)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_facial_cycle_without_shared_neighbours hconn p hp
    (by rw [cycle_support_card_eq_length p hp, hlen]; decide) hP hface ?_ hsmall
  intro x hx hax y hy hya
  exact off_native_five_cycle_unique_neighbour I.girth p hp hlen hx hax hy hya

/-- The facial six-cycle case without an exterior common neighbour of a
pair of opposite cycle vertices. The remaining exceptional configuration is
kept explicit rather than treated as an extension hypothesis. -/
theorem colourable_of_facial_six_cycle_without_opposite_neighbour
    (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hNoOpposite : ∀ x, x ∉ p.support → ¬ (G.Adj a x ∧ G.Adj x (p.getVert 3)))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_facial_cycle_without_shared_neighbours hconn p hp
    (by rw [cycle_support_card_eq_length p hp, hlen]) hP hface ?_ hsmall
  intro x hx hax y hy hya hxy
  have heq := off_native_six_cycle_second_neighbour I.girth p hp hlen hx hax hy hya hxy
  exact hNoOpposite x hx ⟨hax, heq ▸ hxy⟩

end Thomassen.BoundaryInstance
