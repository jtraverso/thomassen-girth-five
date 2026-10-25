/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarCutvertex

/-! Actual spoke cuts in the two-endpoint fan. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance
/-- A cut through either the fixed edge itself or a root-to-short-neighbour
spoke reduces to smaller edge-star pieces and the established root-star theorem. -/
theorem edgeStar_extension_of_spoke_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (r x : V) (hr : r = a ∨ r = b) (hrx : G.Adj r x)
    (hx : x = a ∨ x = b ∨ (I.lists x).card ≤ 2)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {r, x})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  have horient : ∃ U W : Set V, a ∈ U ∧ b ∈ U ∧ U ∪ W = Set.univ ∧ U ∩ W = {r, x} ∧
      (∀ {z w}, G.Adj z w → (z ∈ U ∧ w ∈ U) ∨ (z ∈ W ∧ w ∈ W)) ∧
      (G.induce U).Connected ∧ (G.induce W).Connected ∧ Nat.card U < Nat.card V ∧ Nat.card W < Nat.card V := by
    rcases hedges hab with hS | hT
    · exact ⟨S, T, hS.1, hS.2, hcover, hinter, hedges, hSc, hTc, hSsmall, hTsmall⟩
    · exact ⟨T, S, hT.1, hT.2, by rwa [Set.union_comm], by rwa [Set.inter_comm],
        fun {_ _} h => (hedges h).symm, hTc, hSc, hTsmall, hSsmall⟩
  obtain ⟨U, W, haU, hbU, hcov, hint, hedg, hUc, hWc, hUsmall, hWsmall⟩ := horient
  have hrUW : r ∈ U ∩ W := by rw [hint]; exact Or.inl rfl
  have hxUW : x ∈ U ∩ W := by rw [hint]; exact Or.inr rfl
  have hAdjU : (G.induce U).Adj ⟨r, hrUW.1⟩ ⟨x, hxUW.1⟩ := hrx
  have hAdjW : (G.induce W).Adj ⟨r, hrUW.2⟩ ⟨x, hxUW.2⟩ := hrx
  let : Nontrivial U := hAdjU.nontrivial
  let : Nontrivial W := hAdjW.nontrivial
  by_cases hxroot : x = a ∨ x = b
  · have hpair : ({a, b} : Set V) = {r, x} := by
      rcases hr with rfl | rfl <;> rcases hxroot with rfl | rfl
      · exact (hrx.ne rfl).elim
      · rfl
      · ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      · exact (hrx.ne rfl).elim
    have haUW : a ∈ U ∩ W := by rw [hint, ← hpair]; exact Or.inl rfl
    have hbUW : b ∈ U ∩ W := by rw [hint, ← hpair]; exact Or.inr rfl
    have haW : a ∈ W := haUW.2
    have hbW : b ∈ W := hbUW.2
    apply I.edgeStar_extension_of_edge_cut hP a b hab ha hb f hf hproper U W haU hbU haW hbW hcov
      ?_ hedg hUc.preconnected hWc.preconnected hUsmall hWsmall hedge
    intro z hz
    rw [hint, ← hpair] at hz
    rcases hz with rfl | hz
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inl (Set.mem_singleton_iff.1 hz))
  · have hxshort : (I.lists x).card ≤ 2 := hx.resolve_left (fun h => hxroot (Or.inl h)) |>.resolve_left (fun h => hxroot (Or.inr h))
    have hrface : OnOuterFace I.embedding I.outer r := by rcases hr with rfl | rfl; exact ha; exact hb
    have hsub : ∀ z ∈ rootStar I r, z ∈ edgeStar I a b := by
      intro z hz
      rcases hr with h | h
      · exact Or.inl (h ▸ hz)
      · exact Or.inr (h ▸ hz)
    have hsepStar : ∀ z ∈ U ∩ W, z ∈ rootStar I r := by
      intro z hz
      rw [hint] at hz
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · have heq := Set.mem_singleton_iff.1 hz
        exact Or.inr ⟨heq ▸ hrx, by simpa only [heq] using hxshort⟩
    have hAr : a = r ∨ a ∉ W := by
      by_cases h : a = r
      · exact Or.inl h
      · refine Or.inr (fun haW => ?_)
        have hz : a ∈ U ∩ W := ⟨haU, haW⟩
        rw [hint] at hz
        exact hxroot (Or.inl ((Set.mem_singleton_iff.1 (hz.resolve_left h)).symm))
    have hBr : b = r ∨ b ∉ W := by
      by_cases h : b = r
      · exact Or.inl h
      · refine Or.inr (fun hbW => ?_)
        have hz : b ∈ U ∩ W := ⟨hbU, hbW⟩
        rw [hint] at hz
        exact hxroot (Or.inr ((Set.mem_singleton_iff.1 (hz.resolve_left h)).symm))
    exact I.edgeStar_extension_of_root_cut hP a b hab ha hb f hf hproper U W haU hbU r hrface hrUW.2
      hsub hcov hsepStar (edgeStar_other_side_subset_rootStar I a b r U W hAr hBr hsepStar hedg)
      hedg hUc.preconnected hWc.preconnected hUsmall hWsmall N hN hsmall hedge

end BoundaryInstance
end Thomassen
