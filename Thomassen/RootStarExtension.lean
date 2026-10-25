/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStarFan

/-! The complete auxiliary fan induction on smaller graphs. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance

/-- Within the main strict induction bound, fix any allowed root colour and
compatible colours on all its short neighbours. The auxiliary induction handles
all cutvertices and splits every short-neighbour chord until a native path
prescription suffices. No fan-extension hypothesis is supplied. -/
theorem rootStar_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected) (v : V)
    (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (hN : Nat.card V < N) : RootStarExtension I v f := by
  have haux : ∀ n, ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w →
      ∀ g : W → C, (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W = n → n < N → RootStarExtension J w g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H J hJP hH w hw g hg hgp hn hnN
      let : Fintype W := Fintype.ofFinite W
      have hroot : ∀ (W' : Type u) [Finite W'] (H' : SimpleGraph W') (K : BoundaryInstance H' C),
          K.precolor = .empty → H'.Preconnected → ∀ (w' : W'), OnOuterFace K.embedding K.outer w' →
          ∀ g' : W' → C, (∀ x ∈ rootStar K w', g' x ∈ K.lists x) →
          (∀ x ∈ rootStar K w', ∀ y ∈ rootStar K w', H'.Adj x y → g' x ≠ g' y) →
          Nat.card W' < Nat.card W → RootStarExtension K w' g' := by
        intro W' _ H' K hKP hH' w' hw' g' hg' hgp' hcard
        exact ih (Nat.card W') (by omega) W' H' K hKP hH' w' hw' g' hg' hgp' rfl (by omega)
      by_cases hshort : ∃ x, H.Adj w x ∧ (J.lists x).card ≤ 2
      · by_cases hcard : 3 ≤ Nat.card W
        · by_cases hdelete : ∀ z, (H.induce ({z} : Set W)ᶜ).Preconnected
          · obtain ⟨d, hd, hdw⟩ := hw
            have hdeg := two_le_card_neighbours_of_delete_preconnected hH hcard hdelete
            let c := faceOrbitVertex J.embedding d
            let k := faceOrbitLength J.embedding d
            have hk : 3 ≤ k := faceOrbitLength_three_le J.embedding hdeg d
            let : NeZero k := ⟨by omega⟩
            have hc : IsCycleMap H c := faceOrbitVertex_isCycleMap J.embedding d (by omega) hdelete
            have hcv : c 0 = w := by
              change (J.embedding.facePerm^[(0 : ZMod k).val] d).fst = w
              simpa only [ZMod.val_zero, Function.iterate_zero, id_eq] using hdw
            have hrange : ∀ x, OnOuterFace J.embedding J.outer x → x ∈ Set.range c := by
              intro x hx
              rw [faceOrbitVertex_range]
              obtain ⟨e, he, hex⟩ := hx
              exact ⟨e, hd.symm.trans he, hex⟩
            have hface : IsFacialCycleAlong J.embedding hc Set.univ :=
              faceOrbitVertex_isFacial J.embedding d (by omega) hdelete
            have hresult := J.rootStar_extension_of_facial_boundary hJP hH hc hk hface hrange
              (by rw [hcv]; exact ⟨d, hd, hdw⟩) g (by simpa only [hcv] using hg) (by simpa only [hcv] using hgp)
              N (by omega) hsmall hroot
            simpa only [hcv] using hresult
          · push Not at hdelete
            obtain ⟨z, hz⟩ := hdelete
            exact J.rootStar_extension_of_cutvertex hJP hH w hw g hg hgp z hz hroot
        · obtain ⟨x, hwx, hxshort⟩ := hshort
          have hpair : ({w, x} : Finset W) = Finset.univ := by
            apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Finset.card_pair hwx.ne]
            omega
          have hbound : ∀ y, H.Adj w y → (J.lists y).card ≤ 2 → y = x := by
            intro y hwy _
            have hy : y ∈ ({w, x} : Finset W) := by rw [hpair]; exact Finset.mem_univ _
            rcases Finset.mem_insert.1 hy with h | h
            · exact (hwy.ne h.symm).elim
            · exact Finset.mem_singleton.1 h
          have hexact : ∀ y, y ∈ hwx.toWalk.support ↔ y ∈ rootStar J w := by
            intro y
            simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (rfl | rfl)
              · exact Or.inl rfl
              · exact Or.inr ⟨hwx, hxshort⟩
            · rintro (rfl | ⟨hwy, hs⟩)
              · exact Or.inl rfl
              · exact Or.inr (hbound y hwy hs)
          exact J.rootStar_extension_of_path hJP w hw g hg hgp hwx.toWalk hwx.isPath_toWalk
            (by simp) hwx.isChordless_toWalk hexact N (by omega) hsmall
      · push Not at hshort
        have hexact : ∀ y, y ∈ (Walk.nil (G := H) (u := w)).support ↔ y ∈ rootStar J w := by
          intro y
          simp only [Walk.support_nil, List.mem_singleton]
          constructor
          · exact Or.inl
          · rintro (h | ⟨hwy, hs⟩)
            · exact h
            · exact (not_le_of_gt (hshort y hwy) hs).elim
        exact J.rootStar_extension_of_path hJP w hw g hg hgp .nil (by simp) (by simp)
          (short_path_isChordless J.girth .nil (by simp) (by simp)) hexact N (by omega) hsmall
  exact haux (Nat.card V) V G I hP hG v hv f hf hproper rfl hN

end BoundaryInstance
end Thomassen
