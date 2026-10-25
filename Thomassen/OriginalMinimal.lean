/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalCuts
public import Thomassen.FacialCycleRebase

/-! Actual facial normalization for a minimal original-2.1 counterexample. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The original invariant extends on at most two vertices. -/
theorem extends_of_card_le_two (I : OriginalBoundaryInstance G C) (hcard : Nat.card V ≤ 2) :
    I.Extends := by
  have hall : ∀ x, x = I.a ∨ x = I.b := by
    intro x
    by_contra hn
    have hxa : x ≠ I.a := fun h => hn (Or.inl h)
    have hxb : x ≠ I.b := fun h => hn (Or.inr h)
    have h3 : ({I.a,I.b,x} : Finset V).card = 3 := by simp [I.edge.ne,hxa,hxb,Ne.symm]
    have hle := Finset.card_le_card (Finset.subset_univ ({I.a,I.b,x} : Finset V))
    rw [h3,Finset.card_univ,← Nat.card_eq_fintype_card] at hle
    omega
  let f : V → C := fun x => if x = I.a then I.ta else I.tb
  have hfa : f I.a = I.ta := ite_eq_left rfl
  have hfb : f I.b = I.tb := ite_eq_right I.edge.ne.symm
  refine ⟨Coloring.mk f ?_,?_,hfa,hfb⟩
  · intro x y hxy
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
    · exact (hxy.ne rfl).elim
    · rw [hfa,hfb]; exact I.colours_ne
    · rw [hfb,hfa]; exact I.colours_ne.symm
    · exact (hxy.ne rfl).elim
  · intro x
    change f x ∈ I.lists x
    rcases hall x with rfl | rfl
    · rw [hfa]; exact I.ta_mem
    · rw [hfb]; exact I.tb_mem

/-- A disconnected original instance reduces to its fixed-edge component.
All other components use the unconditionally proved free-instance colouring. -/
theorem extends_of_disconnected (I : OriginalBoundaryInstance G C) (hdisc : ¬ G.Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  let S : Set V := {x | G.Reachable I.a x}
  have haS : I.a ∈ S := Reachable.refl _
  have hbS : I.b ∈ S := I.edge.reachable
  have hSc : (G.induce S).Preconnected := by
    intro x y
    obtain ⟨p⟩ := x.2.symm.trans y.2
    exact ⟨p.induce S (fun z hz => x.2.trans (p.takeUntil z hz).reachable)⟩
  have hmiss : ∃ z, z ∉ S := by
    by_contra hn
    have hall : ∀ z, z ∈ S := by simpa only [not_exists,not_not] using hn
    exact hdisc (fun x y => (hall x).symm.trans (hall y))
  obtain ⟨z,hz⟩ := hmiss
  have hAdjS : (G.induce S).Adj ⟨I.a,haS⟩ ⟨I.b,hbS⟩ := I.edge
  let : Nontrivial S := hAdjS.nontrivial
  let J := I.induceWithEdge S hSc I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) J (card_induced_vertices_lt S hz)
  obtain ⟨c0,hc0⟩ := I.colourable
  let cT : (G.induce Sᶜ).Coloring C := c0.comp (Embedding.induce Sᶜ).toHom
  apply I.extends_of_glued_colourings S Sᶜ (by simp) ?_ haS hbS cS cT hcS (fun x => hc0 x.1) ?_ hca hcb
  · intro x y hxy
    by_cases hx : x ∈ S
    · exact Or.inl ⟨hx,hx.trans hxy.reachable⟩
    · exact Or.inr ⟨hx,fun hy => hx (hy.trans hxy.symm.reachable)⟩
  · intro x hx hy
    exact (hy hx).elim

/-- The source's connected, two-connected and chordless-face reductions,
proved under strict induction for the full original exceptional invariant. -/
theorem minimal_counterexample_has_chordless_native_face_cycle (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.IsChordless ∧
        p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  have hG : G.Preconnected := by
    by_contra hn
    exact hbad (I.extends_of_disconnected hn hsmall)
  have hcard : 3 ≤ Nat.card V := by
    by_contra hn
    exact hbad (I.extends_of_card_le_two (by omega))
  have hdel : ∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected := by
    intro w
    by_contra hn
    exact hbad (I.extends_of_cutvertex hG w hn hsmall)
  obtain ⟨a,p,hp,hlen,hverts,hface,hroot⟩ :=
    exists_native_face_cycle_of_delete_preconnected I.embedding I.outer hG hcard hdel
  have hplen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hf : ∀ i, OnOuterFace I.embedding I.outer (walkCycleVertices p i) := by
    intro i
    apply (hverts _).1
    change p.getVert i.val ∈ p.support
    exact p.getVert_mem_support i.val
  have hch : p.IsChordless := by
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    obtain ⟨i,hi⟩ := (walkCycleVertices_range p hp).symm ▸ (show x ∈ {z | z ∈ p.support} from hx)
    obtain ⟨j,hj⟩ := (walkCycleVertices_range p hp).symm ▸ (show y ∈ {z | z ∈ p.support} from hy)
    have hcon : j = i + 1 ∨ i = j + 1 := by
      by_contra hn
      push Not at hn
      exact hbad (I.extends_of_boundary_chord (walk_isCycleMap p hp) hplen hface hG hf i j
        (by rwa [hi,hj]) hn.1 hn.2 hsmall)
    apply (walkCycleVertices_edges p hp x y).1
    rw [← hi,← hj]
    apply (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) i _).2
    exact hcon.elim (fun h => Or.inl (congrArg (walkCycleVertices p) h))
      (fun h => Or.inr (congrArg (walkCycleVertices p) (by linear_combination -h)))
  exact ⟨hG,hcard,hdel,a,p,hp,hch,hlen,hverts,hface,hroot⟩

/-- Original step (6): actual separating rings of at most six vertices are
excluded by strict original induction and the completed short-ring theorem. -/
theorem extends_of_separating_short_cycle (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hbound : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates I.embedding p hp)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  obtain ⟨S,T,hSsmall,_,houter,hcover,hinter,hedges,hSc,_,⟨oS,_⟩,⟨oT,hTface⟩⟩ :=
    short_native_cycle_proper_cut I.embedding I.outer I.girth hG p hp hbound hsep
  let : Nontrivial S := oS.adj.nontrivial
  have haS := houter I.a I.a_outer
  have hbS := houter I.b I.b_outer
  let J := I.induceWithEdge S hSc.preconnected I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) J hSsmall
  have hprivate : ∀ x : T, x.1 ∉ p.support → 3 ≤ (I.lists x.1).card := by
    intro x hx
    apply I.list_three x.1
    intro hxA
    have h : x.1 ∈ S ∩ T := ⟨houter x.1 (I.on_outer x.1 hxA),x.2⟩
    rw [hinter] at h
    exact hx h
  obtain ⟨c,hc,hfixed⟩ := extend_exterior_across_short_ring S T hcover hedges I.girth p hp
    (by rw [cycle_support_card_eq_length p hp] at hbound; omega) hinter
    (inducedPlaneMap I.embedding T) oT (fun x hx => (hTface x).2 hx) I.lists hprivate cS hcS
  exact ⟨c,hc,(hfixed ⟨I.a,haS⟩).trans hca,(hfixed ⟨I.b,hbS⟩).trans hcb⟩

end Thomassen.OriginalBoundaryInstance
