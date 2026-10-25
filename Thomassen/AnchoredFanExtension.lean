/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanBoundary

/-! Complete anchored-fan induction below the strict main bound. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance

/-- Fix the root fan while retaining up to three original prescribed vertices
adjacent to the root. A complete separate strong induction closes the auxiliary
problem; the main boundary-extension induction is used only below `N`. -/
theorem anchoredFan_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hPcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (hN : Nat.card V < N) : RootStarExtension I b f := by
  have haux : ∀ n, ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor.vertices.card ≤ 3 → ∀ b : W, b ∉ J.precolor.vertices →
      (∃ a ∈ J.precolor.vertices, H.Adj b a) → H.Preconnected →
      OnOuterFace J.embedding J.outer b → ∀ f : W → C,
      (∀ x ∈ rootStar J b, f x ∈ J.lists x) →
      (∀ x ∈ rootStar J b, ∀ y ∈ rootStar J b, H.Adj x y → f x ≠ f y) →
      Nat.card W = n → n < N → RootStarExtension J b f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H J hJP b hbP ha hH hb f hf hp hn hnN
      let : Fintype W := Fintype.ofFinite W
      have hfan : AnchoredFanBelow.{u,v} C (Nat.card W) := by
        intro W' _ H' K hKP b' hbP' ha' hH' hb' f' hf' hp' hcard
        exact ih (Nat.card W') (by omega) W' H' K hKP b' hbP' ha' hH' hb' f' hf' hp' rfl (by omega)
      by_cases hcard : 3 ≤ Nat.card W
      · by_cases hdelete : ∀ z, (H.induce ({z} : Set W)ᶜ).Preconnected
        · obtain ⟨d, hd, hdb⟩ := hb
          have hdeg := two_le_card_neighbours_of_delete_preconnected hH hcard hdelete
          let c := faceOrbitVertex J.embedding d
          let k := faceOrbitLength J.embedding d
          have hk : 3 ≤ k := faceOrbitLength_three_le J.embedding hdeg d
          let : NeZero k := ⟨by omega⟩
          have hc : IsCycleMap H c := faceOrbitVertex_isCycleMap J.embedding d (by omega) hdelete
          have hcb : c 0 = b := by
            change (J.embedding.facePerm^[(0 : ZMod k).val] d).fst = b
            simpa only [ZMod.val_zero, Function.iterate_zero, id_eq] using hdb
          have hrange : ∀ x, OnOuterFace J.embedding J.outer x → x ∈ Set.range c := by
            intro x hx
            rw [faceOrbitVertex_range]
            obtain ⟨e, he, hex⟩ := hx
            exact ⟨e, hd.symm.trans he, hex⟩
          exact J.anchoredFan_extension_of_facial_boundary hJP b hbP ha hH ⟨d, hd, hdb⟩ f hf hp hc hk
            (faceOrbitVertex_isFacial J.embedding d (by omega) hdelete) hrange hcb N (by omega) hsmall hfan
        · push Not at hdelete
          obtain ⟨z, hz⟩ := hdelete
          exact J.anchoredFan_extension_of_cutvertex hJP b hbP ha hH hb f hf hp z hz N (by omega) hsmall hfan
      · obtain ⟨a, haP, hba⟩ := ha
        have hpair : ({b, a} : Finset W) = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Finset.card_pair hba.ne]
          omega
        have hAll : ∀ y, y ∈ rootStar J b := by
          intro y
          have hy : y ∈ ({b, a} : Finset W) := by rw [hpair]; exact Finset.mem_univ _
          rcases Finset.mem_insert.1 hy with h | h
          · exact Or.inl h
          · have hya := Finset.mem_singleton.1 h
            subst y
            exact Or.inr ⟨hba, by simp [J.singleton a haP]⟩
        exact ⟨Coloring.mk f (fun {x y} hxy => hp x (hAll x) y (hAll y) hxy),
          fun y => hf y (hAll y), fun _ _ => rfl⟩
  exact haux (Nat.card V) V G I hPcard b hbP ha hG hbface f hf hp rfl hN

end BoundaryInstance
end Thomassen
