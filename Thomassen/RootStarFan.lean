/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStarCuts
public import Thomassen.BoundaryChordCut

/-! The auxiliary fan induction fixing a root and all its short neighbours. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A chord from the root to an old short-list neighbour separates two smaller
fan-extension problems with matching prescribed endpoint colours. -/
theorem rootStar_extension_of_facial_chord (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hv : OnOuterFace I.embedding I.outer (c 0)) (f : V → C)
    (hf : ∀ x ∈ rootStar I (c 0), f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I (c 0), ∀ y ∈ rootStar I (c 0), G.Adj x y → f x ≠ f y)
    (j : ℕ) (hj : 2 ≤ j) (hjk : j + 2 ≤ k) (hchord : G.Adj (c (j : ZMod k)) (c 0))
    (hshort : (I.lists (c (j : ZMod k))).card ≤ 2)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I (c 0) f := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc, _, _⟩ :=
    full_face_chord_separation I.embedding hc hk hface hG j hj hjk hchord
  have h0 : c 0 ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hj' : c (j : ZMod k) ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
  have hAdjS : (G.induce S).Adj ⟨c 0, h0.1⟩ ⟨c (j : ZMod k), hj'.1⟩ := hchord.symm
  have hAdjT : (G.induce T).Adj ⟨c 0, h0.2⟩ ⟨c (j : ZMod k), hj'.2⟩ := hchord.symm
  let : Nontrivial S := hAdjS.nontrivial
  let : Nontrivial T := hAdjT.nontrivial
  apply I.rootStar_extension_of_star_cut hP (c 0) hv f hf hproper S T h0.1 h0.2 hcover
    ?_ hedges hSc.preconnected hTc.preconnected hSsmall hTsmall hroot
  intro x hx
  rw [hinter] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact Or.inr ⟨hchord.symm, hshort⟩

/-- In a normalized simple facial boundary, either the bounded-star base case
applies, or an actual short-neighbour chord supplies the strict fan cut. -/
theorem rootStar_extension_of_facial_boundary (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (hv : OnOuterFace I.embedding I.outer (c 0)) (f : V → C)
    (hf : ∀ x ∈ rootStar I (c 0), f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I (c 0), ∀ y ∈ rootStar I (c 0), G.Adj x y → f x ≠ f y)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I (c 0) f := by
  by_cases hbound : ∀ z, G.Adj (c 0) z → (I.lists z).card ≤ 2 → z = c 1 ∨ z = c (-1)
  · apply I.rootStar_extension_of_two_neighbours hP (c 0) hv f hf hproper (c 1) (c (-1))
      (by simpa only [zero_add] using hc.adj 0)
      (by simpa only [neg_add_cancel] using (hc.adj (-1)).symm) ?_ hbound N hN hsmall
    intro heq
    have hz : (2 : ZMod k) = 0 := by have he := hc.inj heq; linear_combination he
    exact zmod_two_ne_zero_of_three_le hk hz
  · push Not at hbound
    obtain ⟨z, haz, hshort, hz1, hzm⟩ := hbound
    have hzface : OnOuterFace I.embedding I.outer z := by
      by_contra h
      have h3 := I.interior_lists z h
      omega
    obtain ⟨i, hi⟩ := hrange z hzface
    have h0 : i ≠ 0 := fun heq => haz.ne (by rw [heq] at hi; exact hi)
    have h1 : i ≠ 1 := fun heq => hz1 (by rw [heq] at hi; exact hi.symm)
    have hm : i ≠ -1 := fun heq => hzm (by rw [heq] at hi; exact hi.symm)
    have hi0 : i.val ≠ 0 := fun h => h0 (ZMod.val_injective _ (by simpa only [ZMod.val_zero] using h))
    have hi1 : i.val ≠ 1 := fun h => h1 (by
      rw [← ZMod.natCast_zmod_val i, h, Nat.cast_one])
    have hmval : (-1 : ZMod k).val = k - 1 := by
      obtain ⟨t, ht⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
      subst k
      exact ZMod.val_neg_one t
    have him : i.val ≠ k - 1 := fun h => hm (ZMod.val_injective _ (h.trans hmval.symm))
    have hival := ZMod.val_lt i
    apply I.rootStar_extension_of_facial_chord hP hG hc hk hface hv f hf hproper i.val
      (by omega) (by omega) ?_ ?_ hroot
    · rw [ZMod.natCast_zmod_val, hi]
      exact haz.symm
    · rwa [ZMod.natCast_zmod_val, hi]

end BoundaryInstance
end Thomassen
