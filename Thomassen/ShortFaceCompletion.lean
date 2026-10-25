/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortBoundaryDeletion

/-! Completing compatible colourings of short actual outer faces. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- A compatible colouring of an actual outer cycle on at most six vertices
extends by the already proved full-prescribed-cycle case. The new instance
retains all original private three-lists and restores every original list. -/
theorem colourable_of_compatible_short_facial_cycle (I : BoundaryInstance G C)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hlen : p.length ≤ 6) (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ I.lists x)
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hbound : p.support.toFinset.card ≤ 6 := by rw [cycle_support_card_eq_length p hp]; exact hlen
  let P : BoundaryPrecolor G := .cycle p hp hbound
  have hPv : ∀ x, x ∈ P.vertices ↔ x ∈ p.support := by intro x; simp only [P, BoundaryPrecolor.vertices, List.mem_toFinset]
  have houter := native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot
  have hprivate : ∀ x, x ∉ p.support → 3 ≤ (I.lists x).card :=
    fun x hx => I.interior_lists x (fun h => hx (hExact x h))
  let L : V → Finset C := fun x => if x ∈ p.support then {f x} else I.lists x
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  have hch := short_cycle_isChordless I.girth (walk_isCycleMap p hp) hp.three_le_length hlen
  let J : BoundaryInstance G C := {
    girth := I.girth
    embedding := I.embedding
    outer := I.outer
    precolor := P
    lists := L
    prescribed := f
    on_outer := fun x hx => houter x ((hPv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hPv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := P.endpoints_of_mem_edges he
      exact hproper x ((hPv x).1 hends.1) y ((hPv y).1 hends.2) (P.adj_of_mem_edges he)
    boundary_lists := fun x hx hxp => (hxp ((hPv x).2 (hExact x hx))).elim
    interior_lists := by
      intro x hx
      have hnot : x ∉ p.support := fun h => hx (houter x h)
      simpa only [L, ite_eq_right hnot] using hprivate x hnot
    short_edges := by
      intro x y hxy hx hy
      have hxC : x ∈ p.support := by
        by_contra h
        have hc := hprivate x h
        simp only [L, ite_eq_right h] at hx
        omega
      have hyC : y ∈ p.support := by
        by_contra h
        have hc := hprivate y h
        simp only [L, ite_eq_right h] at hy
        omega
      apply List.mem_toFinset.2
      apply (walkCycleVertices_edges p hp x y).1
      apply cyclicSubgraph_of_chordless hch
      · rwa [walkCycleVertices_range p hp]
      · rwa [walkCycleVertices_range p hp]
      · exact hxy }
  obtain ⟨c, hc⟩ := J.colourable_of_prescribed_cycle p hp hbound hPv hsmall
  refine ⟨c, ?_⟩
  intro x
  have hx : c x ∈ L x := hc x
  by_cases hxC : x ∈ p.support
  · have he : c x = f x := Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hxC] using hx)
    rw [he]
    exact hf x hxC
  · simpa only [L, ite_eq_right hxC] using hx

/-- With only an edge prescribed, an actual five-vertex outer face can be
coloured compatibly: choose its middle unprescribed colour first and then its
two three-list neighbours. The checked full-cycle reduction handles the interior. -/
theorem colourable_of_prescribed_edge_five_vertex_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : p.length = 5)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hinj : ∀ i j, i < 5 → j < 5 → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (show i ≤ p.length-1 from by omega) (show j ≤ p.length-1 from by omega) he)
  have hna : ∀ i, 0 < i → i < 5 → p.getVert i ≠ a := by
    intro i hi hil
    simpa only [Walk.getVert_zero] using hinj i 0 hil (by omega) (by omega)
  have haP := (hP a).2 (Or.inl rfl)
  have h1P := (hP (p.getVert 1)).2 (Or.inr rfl)
  have h2not : p.getVert 2 ∉ I.precolor.vertices := fun h => ((hP _).1 h).elim
    (hna 2 (by omega) (by omega)) (hinj 2 1 (by omega) (by omega) (by omega))
  have h4not : p.getVert 4 ∉ I.precolor.vertices := fun h => ((hP _).1 h).elim
    (hna 4 (by omega) (by omega)) (hinj 4 1 (by omega) (by omega) (by omega))
  have h2three : 3 ≤ (I.lists (p.getVert 2)).card := by
    by_contra h
    exact I.short_not_adj_precolored h2not h1P (by omega)
      (by simpa only [show 1+1 = 2 by omega] using (p.adj_getVert_succ (by omega : 1 < p.length)).symm)
  have h4three : 3 ≤ (I.lists (p.getVert 4)).card := by
    by_contra h
    exact I.short_not_adj_precolored h4not haP (by omega)
      (by simpa only [show 4+1 = 5 by omega, ← hlen, Walk.getVert_length] using p.adj_getVert_succ (by omega : 4 < p.length))
  obtain ⟨c3, hc3⟩ := I.list_nonempty (p.getVert 3)
  have hchoice : ∀ x, 3 ≤ (I.lists x).card → ∀ c d : C, ∃ e ∈ I.lists x, e ≠ c ∧ e ≠ d := by
    intro x hx c d
    have hc : ({c,d} : Finset C).card < (I.lists x).card := Finset.card_le_two.trans_lt (by omega)
    obtain ⟨e, heL, heN⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hn : e ≠ c ∧ e ≠ d := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using heN
    exact ⟨e, heL, hn⟩
  obtain ⟨c2, hc2, h21, h23⟩ := hchoice (p.getVert 2) h2three (I.prescribed (p.getVert 1)) c3
  obtain ⟨c4, hc4, h40, h43⟩ := hchoice (p.getVert 4) h4three (I.prescribed a) c3
  let f : V → C := fun x => if x = a then I.prescribed a else if x = p.getVert 1 then I.prescribed x
    else if x = p.getVert 2 then c2 else if x = p.getVert 3 then c3 else c4
  have hf0 : f (p.getVert 0) = I.prescribed a := by simp only [Walk.getVert_zero, f, ite_true]
  have hf1 : f (p.getVert 1) = I.prescribed (p.getVert 1) := by simp only [f, ite_eq_right (hna 1 (by omega) (by omega)), ite_true]
  have hf2 : f (p.getVert 2) = c2 := by simp only [f, ite_eq_right (hna 2 (by omega) (by omega)), ite_eq_right (hinj 2 1 (by omega) (by omega) (by omega)), ite_true]
  have hf3 : f (p.getVert 3) = c3 := by simp only [f, ite_eq_right (hna 3 (by omega) (by omega)), ite_eq_right (hinj 3 1 (by omega) (by omega) (by omega)), ite_eq_right (hinj 3 2 (by omega) (by omega) (by omega)), ite_true]
  have hf4 : f (p.getVert 4) = c4 := by simp only [f, ite_eq_right (hna 4 (by omega) (by omega)), ite_eq_right (hinj 4 1 (by omega) (by omega) (by omega)), ite_eq_right (hinj 4 2 (by omega) (by omega) (by omega)), ite_eq_right (hinj 4 3 (by omega) (by omega) (by omega))]
  have hf5 : f (p.getVert 5) = I.prescribed a := by simpa only [← hlen, Walk.getVert_length, Walk.getVert_zero] using hf0
  have hedge : ∀ i, i < p.length → f (p.getVert i) ≠ f (p.getVert (i+1)) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [hf0, show 0+1 = 1 by omega, hf1]
      exact I.proper_on_precolored_vertices haP h1P
        (by simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length))
    · simpa only [show 1+1 = 2 by omega, hf1, hf2] using h21.symm
    · simpa only [show 2+1 = 3 by omega, hf2, hf3] using h23
    · simpa only [show 3+1 = 4 by omega, hf3, hf4] using h43.symm
    · simpa only [show 4+1 = 5 by omega, hf4, hf5] using h40
  apply hbad
  apply I.colourable_of_compatible_short_facial_cycle p hp hface hroot hExact (by omega) f ?_ ?_ hsmall
  · intro x hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [← hix]
    · rw [hf0, Walk.getVert_zero, I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [hf1, I.singleton _ h1P]; exact Finset.mem_singleton_self _
    · rw [hf2]; exact hc2
    · rw [hf3]; exact hc3
    · rw [hf4]; exact hc4
    · rw [hf5, ← hlen, Walk.getVert_length, I.singleton a haP]; exact Finset.mem_singleton_self _
  · intro x hx y hy hxy
    obtain ⟨i, hi, he⟩ := p.mk_mem_edges_iff_exists.1 (hch.mem_edges hx hy hxy)
    rcases Sym2.eq_iff.1 he with he | he
    · simpa only [he.1, he.2] using hedge i hi
    · simpa only [he.1, he.2] using (hedge i hi).symm

end Thomassen.BoundaryInstance
