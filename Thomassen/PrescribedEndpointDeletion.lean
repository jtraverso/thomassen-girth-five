/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorTwoPathReduction

/-! Deletion and restoration of an original prescribed-path endpoint. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a t : V}

/-- Deleting the first vertex of a native prescribed path gives the exact
remaining native path, or the empty prescription for an original singleton. -/
lemma exists_prescription_after_initial_deletion (p : G.Walk a t) (hp : p.IsPath)
    (hn : p.support.toFinset.card ≤ 6) :
    ∃ Q : BoundaryPrecolor (G.induce ({a} : Set V)ᶜ),
      (∀ x : ↥(({a} : Set V)ᶜ), x ∈ Q.vertices ↔ x.1 ∈ p.support) ∧
      (∀ x y : ↥(({a} : Set V)ᶜ), s(x,y) ∈ Q.edges ↔ s(x.1,y.1) ∈ p.edges) := by
  cases p with
  | nil =>
    refine ⟨.empty, ?_, ?_⟩
    · intro x
      simp only [BoundaryPrecolor.vertices_empty, Finset.notMem_empty, Walk.support_nil, List.mem_singleton]
      exact iff_of_false False.elim x.2
    · intro x y
      simp only [BoundaryPrecolor.edges_empty, Finset.notMem_empty, Walk.edges_nil, List.not_mem_nil]
  | @cons a b t hab r =>
    have hnot : a ∉ r.support := (List.nodup_cons.1 hp.support_nodup).1
    have hrn : r.support.toFinset.card ≤ 6 := (Finset.card_le_card
      (by intro x hx; exact List.mem_toFinset.2 (List.mem_cons_of_mem _ (List.mem_toFinset.1 hx)))).trans hn
    let P : BoundaryPrecolor G := .path r hp.of_cons hrn
    have hPS : ∀ x ∈ P.vertices, x ∈ ({a} : Set V)ᶜ := by
      intro x hx hxa
      exact hnot (hxa ▸ List.mem_toFinset.1 hx)
    refine ⟨P.induce ({a} : Set V)ᶜ hPS, ?_, ?_⟩
    · intro x
      rw [BoundaryPrecolor.mem_vertices_induce]
      change x.1 ∈ r.support.toFinset ↔ x.1 ∈ (Walk.cons hab r).support
      simp only [List.mem_toFinset, Walk.support_cons, List.mem_cons]
      exact (or_iff_right x.2).symm
    · intro x y
      rw [BoundaryPrecolor.mem_edges_induce]
      change s(x.1,y.1) ∈ r.edges.toFinset ↔ s(x.1,y.1) ∈ (Walk.cons hab r).edges
      simp only [List.mem_toFinset, Walk.edges_cons, List.mem_cons]
      have hne : s(x.1,y.1) ≠ s(a,b) := by
        intro h
        rcases Sym2.eq_iff.1 h with h | h
        · exact x.2 h.1
        · exact y.2 h.2
      exact (or_iff_right hne).symm

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Delete and restore an original prescribed endpoint when its newly short
neighbours have no remaining prescribed neighbour and no old short-list
neighbour. Original two-lists remain unchanged; new two-lists are independent
by girth. Disconnection at the deleted vertex uses the completed cutvertex case. -/
theorem colourable_of_prescribed_endpoint_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hNoShared : ∀ x, x ∉ p.support → G.Adj a x → ∀ y ∈ p.support, y ≠ a → ¬ G.Adj x y)
    (hNoOldShort : ∀ x, x ∉ p.support → G.Adj a x → ∀ y, y ∉ p.support →
      (I.lists y).card ≤ 2 → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hcard : Nat.card V ≤ 2
  · exact I.colourable_of_card_le_two hcard hsmall
  have haP : a ∈ I.precolor.vertices := by simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset]; exact p.start_mem_support
  let S : Set V := ({a} : Set V)ᶜ
  by_cases hconn : (G.induce S).Preconnected
  swap
  · exact I.colourable_of_precolored_cutvertex a haP hG hconn hsmall
  have hcardS : Fintype.card S = Fintype.card V - 1 := by
    simpa [S] using Fintype.card_compl_set ({a} : Set V)
  let : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.1 (by
    rw [hcardS, ← Nat.card_eq_fintype_card]
    omega)
  obtain ⟨outer, hOldFace, hNeighbour⟩ := exists_outer_after_boundary_vertex I.embedding I.outer a
    (I.on_outer a haP) hconn
  let r : V → Finset C := residual G I.lists {a} I.prescribed
  have hVerts : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support := by simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hOldTwoUnchanged : ∀ x, x ∉ p.support → (I.lists x).card ≤ 2 → r x = I.lists x := by
    intro x hx hxs
    apply residual_unchanged
    intro y hy hxy
    have hyA : y = a := Finset.mem_singleton.1 hy
    subst y
    exact I.short_not_adj_precolored (fun h => hx ((hVerts x).1 h)) haP hxs hxy
  have hResP : ∀ x ∈ p.support, r x = {I.prescribed x} := by
    intro x hx
    have hOrig := I.singleton x ((hVerts x).2 hx)
    apply Finset.Subset.antisymm
    · have h := residual_subset G I.lists {a} I.prescribed x
      rwa [hOrig] at h
    · apply Finset.singleton_subset_iff.2
      apply (mem_residual_iff I.lists {a} I.prescribed x _).2
      refine ⟨by simp only [hOrig, Finset.mem_singleton], ?_⟩
      intro y hy hxy
      have hyA : y = a := Finset.mem_singleton.1 hy
      subst y
      exact I.proper_on_precolored_vertices ((hVerts x).2 hx) haP hxy
  have hResTwo : ∀ x, x ∉ p.support → 2 ≤ (r x).card := by
    intro x hx
    by_cases hxs : (I.lists x).card ≤ 2
    · rw [hOldTwoUnchanged x hx hxs]
      exact I.outside_precolor_list_ge_two (fun h => hx ((hVerts x).1 h))
    · exact residual_three_to_two I.lists {a} I.prescribed x (by omega)
        ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))
  have hNewShort : ∀ x, x ∉ p.support → (r x).card ≤ 2 →
      (I.lists x).card ≤ 2 ∨ G.Adj a x := by
    intro x _ hxs
    by_cases hold : (I.lists x).card ≤ 2
    · exact Or.inl hold
    · obtain ⟨y, hy, hyx⟩ := short_residual_neighbor I.lists {a} I.prescribed x (by omega) hxs
      have hyA : y = a := Finset.mem_singleton.1 hy
      subst y
      exact Or.inr hyx
  obtain ⟨Q, hQv, hQe⟩ := exists_prescription_after_initial_deletion p hp hn
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := outer
    precolor := Q
    lists := fun x => r x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := fun x hx => hOldFace x (I.on_outer x.1 ((hVerts x.1).2 ((hQv x).1 hx)))
    singleton := fun x hx => hResP x.1 ((hQv x).1 hx)
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact I.proper_on_precolored_vertices ((hVerts x.1).2 ((hQv x).1 hends.1))
        ((hVerts y.1).2 ((hQv y).1 hends.2)) (Q.adj_of_mem_edges he)
    boundary_lists := fun x _ hx => hResTwo x.1 (fun h => hx ((hQv x).2 h))
    interior_lists := by
      intro x hx
      have hNoAdj : ¬ G.Adj x.1 a := fun h => hx (hNeighbour x h)
      have hold : ¬ OnOuterFace I.embedding I.outer x.1 := fun h => hx (hOldFace x h)
      have heq : r x.1 = I.lists x.1 := by
        apply residual_unchanged
        intro y hy
        have hyA : y = a := Finset.mem_singleton.1 hy
        exact hyA.symm ▸ hNoAdj
      rw [heq]
      exact I.interior_lists x.1 hold
    short_edges := by
      intro x y hxy hx hy
      by_cases hxP : x.1 ∈ p.support <;> by_cases hyP : y.1 ∈ p.support
      · apply (hQe x y).2
        have he : s(x.1, y.1) ∈ I.precolor.edges := I.short_edges hxy (by simp [I.singleton x.1 ((hVerts x.1).2 hxP)])
          (by simp [I.singleton y.1 ((hVerts y.1).2 hyP)])
        simpa only [hP, BoundaryPrecolor.edges, List.mem_toFinset] using he
      · rcases hNewShort y.1 hyP hy with hyold | hynew
        · exact (I.short_not_adj_precolored (fun h => hyP ((hVerts y.1).1 h)) ((hVerts x.1).2 hxP) hyold hxy.symm).elim
        · exact (hNoShared y.1 hyP hynew x.1 hxP x.2 hxy.symm).elim
      · rcases hNewShort x.1 hxP hx with hxold | hxnew
        · exact (I.short_not_adj_precolored (fun h => hxP ((hVerts x.1).1 h)) ((hVerts y.1).2 hyP) hxold hxy).elim
        · exact (hNoShared x.1 hxP hxnew y.1 hyP y.2 hxy).elim
      · rcases hNewShort x.1 hxP hx with hxold | hxnew <;> rcases hNewShort y.1 hyP hy with hyold | hynew
        · exact (hxP ((hVerts x.1).1 (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxold hyold)).1)).elim
        · exact (hNoOldShort y.1 hyP hynew x.1 hxP hxold hxy.symm).elim
        · exact (hNoOldShort x.1 hxP hxnew y.1 hyP hyold hxy).elim
        · exact (neighbors_nonadjacent I.girth hxnew hynew hxy).elim }
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) J (card_induced_vertices_lt S (x := a) (by simp [S]))
  let d : V → C := fun x => if hx : x = a then I.prescribed a else cS ⟨x, hx⟩
  have hne : ∀ x, x ∈ (Finset.univ \ ({a} : Finset V)) → x ≠ a :=
    fun x hx heq => (Finset.mem_sdiff.1 hx).2 (Finset.mem_singleton.2 heq)
  apply (col_univ_iff I.lists).1
  refine glue_residual Finset.univ {a} I.lists I.prescribed d ?_ ?_ ?_ ?_
  · intro x hx
    have hxa := Finset.mem_singleton.1 hx
    subst x
    simp only [I.singleton a haP, Finset.mem_singleton]
  · intro x hx y hy hxy
    exact (hxy.ne ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm)).elim
  · intro x hx
    simpa only [d, dite_eq_right (hne x hx)] using hcS ⟨x, hne x hx⟩
  · intro x hx y hy hxy
    simpa only [d, dite_eq_right (hne x hx), dite_eq_right (hne y hy)] using
      cS.valid (show (G.induce S).Adj ⟨x, hne x hx⟩ ⟨y, hne y hy⟩ from hxy)

/-- For a prescribed path of at most three vertices, girth itself rules out
new two-lists adjacent to the remaining prescription. Only old-short-list
conflicts have to be excluded. -/
theorem colourable_of_short_prescribed_endpoint_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 2)
    (hNoOldShort : ∀ x, x ∉ p.support → G.Adj a x → ∀ y, y ∉ p.support →
      (I.lists y).card ≤ 2 → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_prescribed_endpoint_deletion hG p hp hn hP ?_ hNoOldShort hsmall
  intro x hx hax y hy hya hxy
  exact hya (external_short_path_neighbour_unique I.girth p hp hlen p.start_mem_support hx hax.symm hy hxy)

/-- The entire case with a short prescribed path and three-lists everywhere
else is closed by the strict main induction, without extra geometric inputs. -/
theorem colourable_of_short_prescription_and_three_lists (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 2)
    (hthree : ∀ x, x ∉ p.support → 3 ≤ (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_short_prescribed_endpoint_deletion hG p hp hn hP hlen ?_ hsmall
  intro x _ _ y hy hys
  have h3 := hthree y hy
  omega

/-- The endpoint-deletion reduction supplies explicit geometric obstruction
witnesses in a smallest counterexample; absence of those witnesses is not
assumed silently in the final induction. -/
lemma endpoint_deletion_obstruction_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (∃ x, x ∉ p.support ∧ G.Adj a x ∧ ∃ y ∈ p.support, y ≠ a ∧ G.Adj x y) ∨
      (∃ x, x ∉ p.support ∧ G.Adj a x ∧ ∃ y, y ∉ p.support ∧ (I.lists y).card ≤ 2 ∧ G.Adj x y) := by
  by_contra h
  have hNoShared : ∀ x, x ∉ p.support → G.Adj a x → ∀ y ∈ p.support, y ≠ a → ¬ G.Adj x y := by
    intro x hx hax y hy hya hxy
    exact h (Or.inl ⟨x, hx, hax, y, hy, hya, hxy⟩)
  have hNoOld : ∀ x, x ∉ p.support → G.Adj a x → ∀ y, y ∉ p.support →
      (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hax y hy hys hxy
    exact h (Or.inr ⟨x, hx, hax, y, hy, hys, hxy⟩)
  exact hbad (I.colourable_of_prescribed_endpoint_deletion hG p hp hn hP hNoShared hNoOld hsmall)

end BoundaryInstance
end Thomassen
