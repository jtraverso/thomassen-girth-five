/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CurrentSmallStar

/-! Complete empty-prescription case of the strict boundary induction. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- With a short list present, choose its preceding facial neighbour as root.
Chordlessness puts every old short root neighbour among the two cycle neighbours,
so the proved nontrivial small-star extension closes the current instance. -/
theorem colourable_of_empty_prescription_with_short_list (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hshort : ∃ y, (I.lists y).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,_,_,a,p,hp,_,_,hverts,hface,hroot⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hpRoot hbad hsmall
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let c := walkCycleVertices p
  have hc : IsCycleMap G c := walk_isCycleMap p hp
  have hfaceAll : ∀ j, OnOuterFace I.embedding I.outer (c j) := by
    intro j
    apply (hverts (c j)).1
    exact p.getVert_mem_support _
  obtain ⟨y,hyShort⟩ := hshort
  have hyFace : OnOuterFace I.embedding I.outer y := by
    by_contra h
    have h3 := I.interior_lists y h
    omega
  have hyRange : y ∈ Set.range c := by
    rw [walkCycleVertices_range p hp]
    exact (hverts y).2 hyFace
  obtain ⟨i,hi⟩ := hyRange
  let j := i-1
  let v := c j
  let l := c (j+1)
  let r := c (j-1)
  have hvl : G.Adj v l := hc.adj j
  have hvr : G.Adj v r := by simpa only [sub_add_cancel] using (hc.adj (j-1)).symm
  have hlr : l ≠ r := by
    intro h
    have he := hc.inj h
    have htwo : (2 : ZMod p.length)=0 := by linear_combination he
    exact zmod_two_ne_zero_of_three_le hk htwo
  have hlShort : (I.lists l).card ≤ 2 := by
    simpa only [l,j,sub_add_cancel,hi] using hyShort
  have hbound : ∀ z, G.Adj v z → (I.lists z).card ≤ 2 → z=l ∨ z=r := by
    intro z hvz hzShort
    have hzFace : OnOuterFace I.embedding I.outer z := by
      by_contra h
      have h3 := I.interior_lists z h
      omega
    have hzP : z ∈ p.support := (hverts z).2 hzFace
    have hvP : v ∈ p.support := p.getVert_mem_support _
    have he := (walkCycleVertices_edges p hp v z).2 (hch.mem_edges hvP hzP hvz)
    exact (cyclicSubgraph_adj_at_iff hc j z).1 he
  obtain ⟨cv,hcv⟩ := I.list_nonempty v
  obtain ⟨f,_,hf,hproper⟩ := I.exists_rootStar_colours hP v cv hcv
  obtain ⟨col,hcol,_⟩ := I.rootStar_extension_of_two_neighbours_current hP v (hfaceAll j) f hf hproper
    l r hvl hvr hlr hbound ⟨l,hvl,hlShort⟩ hsmall
  exact hbad ⟨col,hcol⟩

/-- The full empty-prescription induction case. If all lists have at least
three colours, thin one actual boundary list to two and use the previous case.
The thinned instance retains the same graph, face and strict main induction. -/
theorem colourable_of_empty_prescription (I : BoundaryInstance G C)
    (hP : I.precolor = .empty)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hshort : ∃ y, (I.lists y).card ≤ 2
  · exact I.colourable_of_empty_prescription_with_short_list hP hshort hsmall
  · push Not at hshort
    have h3 : ∀ x, 3 ≤ (I.lists x).card := fun x => by have := hshort x; omega
    let v := I.outer.fst
    obtain ⟨S,hS,hScard⟩ := Finset.exists_subset_card_eq (s := I.lists v) (n := 2) (by have := h3 v; omega)
    let L : V → Finset C := fun x => if x=v then S else I.lists x
    have hLsub : ∀ x, L x ⊆ I.lists x := by
      intro x
      by_cases hx : x=v
      · simpa only [L,hx,ite_true] using hS
      · simp only [L,ite_eq_right hx]; exact Finset.Subset.refl _
    have hLtwo : ∀ x, 2 ≤ (L x).card := by
      intro x
      by_cases hx : x=v
      · simp only [L,ite_eq_left hx,hScard]; exact le_rfl
      · simp only [L,ite_eq_right hx]; exact (by omega : 2 ≤ 3).trans (h3 x)
    have hLshort : ∀ x, (L x).card ≤ 2 → x=v := by
      intro x hx
      by_contra h
      have hcard := h3 x
      simp only [L,ite_eq_right h] at hx
      omega
    let J : BoundaryInstance G C := {
      girth := I.girth
      embedding := I.embedding
      outer := I.outer
      precolor := .empty
      lists := L
      prescribed := I.prescribed
      on_outer := by intro x hx; exact (Finset.notMem_empty x hx).elim
      singleton := by intro x hx; exact (Finset.notMem_empty x hx).elim
      proper_precolor := by intro x y hxy; exact (Finset.notMem_empty _ hxy).elim
      boundary_lists := fun x _ _ => hLtwo x
      interior_lists := by
        intro x hx
        have hxv : x ≠ v := fun h => hx (h.symm ▸ onOuterFace_self I.embedding I.outer)
        simpa only [L,ite_eq_right hxv] using h3 x
      short_edges := fun {x y} hxy hx hy => (hxy.ne ((hLshort x hx).trans (hLshort y hy).symm)).elim }
    obtain ⟨col,hcol⟩ := J.colourable_of_empty_prescription_with_short_list rfl
      ⟨v,by change (L v).card ≤ 2; simp only [L,ite_true,hScard]; exact le_rfl⟩ hsmall
    exact ⟨col,fun x => hLsub x (hcol x)⟩

end Thomassen.BoundaryInstance
