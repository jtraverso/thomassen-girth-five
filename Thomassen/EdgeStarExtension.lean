/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarBoundary

/-! The complete auxiliary two-endpoint fan induction on smaller graphs. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance

/-- Fixing an edge and all its old short neighbours needs no additional
extension hypothesis. The main induction is used only below the explicit bound;
all cuts in the auxiliary induction strictly decrease its own vertex count. -/
theorem edgeStar_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (hN : Nat.card V < N) : EdgeStarExtension I a b f := by
  have haux : ∀ n, ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ a b : W, H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W = n → n < N → EdgeStarExtension J a b g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H J hJP hH a b hab ha hb g hg hgp hn hnN
      let : Fintype W := Fintype.ofFinite W
      have hedge : ∀ (W' : Type u) [Finite W'] (H' : SimpleGraph W') (K : BoundaryInstance H' C),
          K.precolor = .empty → H'.Preconnected → ∀ a' b' : W', H'.Adj a' b' →
          OnOuterFace K.embedding K.outer a' → OnOuterFace K.embedding K.outer b' → ∀ g' : W' → C,
          (∀ x ∈ edgeStar K a' b', g' x ∈ K.lists x) →
          (∀ x ∈ edgeStar K a' b', ∀ y ∈ edgeStar K a' b', H'.Adj x y → g' x ≠ g' y) →
          Nat.card W' < Nat.card W → EdgeStarExtension K a' b' g' := by
        intro W' _ H' K hKP hH' a' b' hab' ha' hb' g' hg' hgp' hcard
        exact ih (Nat.card W') (by omega) W' H' K hKP hH' a' b' hab' ha' hb' g' hg' hgp' rfl (by omega)
      by_cases hcard : 3 ≤ Nat.card W
      · by_cases hdelete : ∀ z, (H.induce ({z} : Set W)ᶜ).Preconnected
        · obtain ⟨d, hd, hda⟩ := ha
          have hdeg := two_le_card_neighbours_of_delete_preconnected hH hcard hdelete
          let c := faceOrbitVertex J.embedding d
          let k := faceOrbitLength J.embedding d
          have hk : 3 ≤ k := faceOrbitLength_three_le J.embedding hdeg d
          let : NeZero k := ⟨by omega⟩
          have hc : IsCycleMap H c := faceOrbitVertex_isCycleMap J.embedding d (by omega) hdelete
          have hca : c 0 = a := by
            change (J.embedding.facePerm^[(0 : ZMod k).val] d).fst = a
            simpa only [ZMod.val_zero, Function.iterate_zero, id_eq] using hda
          have hrange : ∀ x, OnOuterFace J.embedding J.outer x → x ∈ Set.range c := by
            intro x hx
            rw [faceOrbitVertex_range]
            obtain ⟨e, he, hex⟩ := hx
            exact ⟨e, hd.symm.trans he, hex⟩
          exact J.edgeStar_extension_of_facial_boundary hJP hH a b hab ⟨d, hd, hda⟩ hb g hg hgp hc hk
            (faceOrbitVertex_isFacial J.embedding d (by omega) hdelete) hrange hca N (by omega) hsmall hedge
        · push Not at hdelete
          obtain ⟨z, hz⟩ := hdelete
          exact J.edgeStar_extension_of_cutvertex hJP hH a b hab ha hb g hg hgp z hz N (by omega) hsmall hedge
      · have hpair : ({a, b} : Finset W) = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Finset.card_pair hab.ne]
          omega
        have hAll : ∀ x, x ∈ edgeStar J a b := by
          intro x
          have hx : x ∈ ({a, b} : Finset W) := by rw [hpair]; exact Finset.mem_univ _
          rcases Finset.mem_insert.1 hx with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl (Finset.mem_singleton.1 h))
        exact ⟨Coloring.mk g (fun {x y} hxy => hgp x (hAll x) y (hAll y) hxy),
          fun x => hg x (hAll x), fun _ _ => rfl⟩
  exact haux (Nat.card V) V G I hP hG a b hab ha hb f hf hproper rfl hN

end BoundaryInstance
end Thomassen
