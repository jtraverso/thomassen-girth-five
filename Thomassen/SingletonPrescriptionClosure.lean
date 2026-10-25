/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EmptyPrescriptionClosure

/-! The single prescribed vertex is retained through a compatible small star. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The singleton-prescription case, including arbitrary original faces.
Expand its singleton list by an allowed colour at a facial neighbour, then
fix that neighbour to the added colour. Properness forces the original
singleton colour. The auxiliary root star has at most three vertices. -/
theorem colourable_of_singleton_prescription (I : BoundaryInstance G C)
    (a : V) (hP : ∀ x, x ∈ I.precolor.vertices ↔ x=a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have haP : a ∈ I.precolor.vertices := (hP a).2 rfl
  have haFace := I.on_outer a haP
  obtain ⟨hG,_,_,b,p,hp,_,_,hverts,hface,hroot⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hpRoot hbad hsmall
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let c := walkCycleVertices p
  have hc : IsCycleMap G c := walk_isCycleMap p hp
  have haRange : a ∈ Set.range c := by
    rw [walkCycleVertices_range p hp]; exact (hverts a).2 haFace
  obtain ⟨i,hi⟩ := haRange
  let j := i-1
  let w := c j
  let l := c (j+1)
  let r := c (j-1)
  have hla : l=a := by simpa only [l,j,sub_add_cancel] using hi
  have hwl : G.Adj w l := hc.adj j
  have hwa : G.Adj w a := hla ▸ hwl
  have hwr : G.Adj w r := by simpa only [sub_add_cancel] using (hc.adj (j-1)).symm
  have hlr : l ≠ r := by
    intro h
    have he := hc.inj h
    have htwo : (2 : ZMod p.length)=0 := by linear_combination he
    exact zmod_two_ne_zero_of_three_le hk htwo
  have hwP : w ∉ I.precolor.vertices := fun h => hwa.ne ((hP w).1 h)
  have hw3 : 3 ≤ (I.lists w).card := by
    by_contra h
    exact I.short_not_adj_precolored hwP haP (by omega) hwa
  obtain ⟨cw,hcw,hcwNe⟩ := Finset.exists_mem_ne (s := I.lists w) (by omega) (I.prescribed a)
  let L : V → Finset C := fun x => if x=a then {I.prescribed a,cw} else I.lists x
  have hLa : L a = {I.prescribed a,cw} := ite_eq_left rfl
  have hLaCard : (L a).card=2 := by rw [hLa,Finset.card_pair hcwNe.symm]
  have hLold : ∀ x, x ≠ a → L x = I.lists x := fun _ hx => ite_eq_right hx
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
    boundary_lists := by
      intro x _ _
      by_cases hx : x=a
      · rw [hx,hLaCard]
      · rw [hLold x hx]; exact I.outside_precolor_list_ge_two (fun h => hx ((hP x).1 h))
    interior_lists := by
      intro x hx
      have hxa : x ≠ a := fun h => hx (h.symm ▸ haFace)
      rw [hLold x hxa]; exact I.interior_lists x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxa : x=a <;> by_cases hya : y=a
      · exact (hxy.ne (hxa.trans hya.symm)).elim
      · have hyOld : (I.lists y).card ≤ 2 := by rwa [hLold y hya] at hy
        exact (I.short_not_adj_precolored (fun h => hya ((hP y).1 h)) haP hyOld (hxa ▸ hxy.symm)).elim
      · have hxOld : (I.lists x).card ≤ 2 := by rwa [hLold x hxa] at hx
        exact (I.short_not_adj_precolored (fun h => hxa ((hP x).1 h)) haP hxOld (hya ▸ hxy)).elim
      · have he := I.short_edges hxy (by rwa [hLold x hxa] at hx) (by rwa [hLold y hya] at hy)
        exact (hxa ((hP x).1 (I.precolor.endpoints_of_mem_edges he).1)).elim }
  have hFaceAll : ∀ z, OnOuterFace J.embedding J.outer (c z) := by
    intro z; exact (hverts _).1 (p.getVert_mem_support _)
  have hbound : ∀ z, G.Adj w z → (J.lists z).card ≤ 2 → z=l ∨ z=r := by
    intro z hwz hzShort
    have hzFace : OnOuterFace J.embedding J.outer z := by
      by_contra h
      have h3 := J.interior_lists z h
      omega
    have hzP : z ∈ p.support := (hverts z).2 hzFace
    have hwP' : w ∈ p.support := p.getVert_mem_support _
    have he := (walkCycleVertices_edges p hp w z).2 (hch.mem_edges hwP' hzP hwz)
    exact (cyclicSubgraph_adj_at_iff hc j z).1 he
  have hcwJ : cw ∈ J.lists w := by change cw ∈ L w; rw [hLold w hwa.ne]; exact hcw
  obtain ⟨f,hfw,hf,hproper⟩ := J.exists_rootStar_colours rfl w cw hcwJ
  obtain ⟨col,hcol,hfixed⟩ := J.rootStar_extension_of_two_neighbours_current rfl w (hFaceAll j)
    f hf hproper l r hwl hwr hlr hbound ⟨a,hwa,by change (L a).card ≤ 2; rw [hLaCard]⟩ hsmall
  have hcolw : col w=cw := (hfixed w (Or.inl rfl)).trans hfw
  have hcola : col a=I.prescribed a := by
    have haL : col a ∈ ({I.prescribed a,cw} : Finset C) := by
      have haL' : col a ∈ L a := hcol a
      rwa [hLa] at haL'
    rcases Finset.mem_insert.1 haL with h | h
    · exact h
    · have hcolacw := Finset.mem_singleton.1 h
      exact ((col.valid hwa) (hcolw.trans hcolacw.symm)).elim
  apply hbad
  refine ⟨col,?_⟩
  intro x
  by_cases hxa : x=a
  · rw [hxa,hcola,I.singleton a haP]; exact Finset.mem_singleton_self _
  · have hxL : col x ∈ L x := hcol x
    rwa [hLold x hxa] at hxL

end Thomassen.BoundaryInstance
