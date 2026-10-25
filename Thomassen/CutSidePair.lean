/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CutPrecolor

/-! Exact complementary cut sides. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {w : V} {S : Set V}

lemma cut_side_pair_properties (hw : w ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S)) :
    S ∪ insert w Sᶜ = Set.univ ∧ S ∩ insert w Sᶜ = {w} ∧
    (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ insert w Sᶜ ∧ y ∈ insert w Sᶜ)) ∧
    (∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ insert w Sᶜ ↔ y ∈ insert w Sᶜ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    tauto
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact h
      · exact (h hx).elim
    · rintro rfl
      exact ⟨hw, Or.inl rfl⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact Or.inl ⟨hx, hy⟩
      · have hxw : x = w := by
          by_contra hxw
          exact hy ((hsep hxy hxw (fun h => hy (h ▸ hw))).1 hx)
        exact Or.inr ⟨Or.inl hxw, Or.inr hy⟩
    · by_cases hy : y ∈ S
      · have hyw : y = w := by
          by_contra hyw
          exact hx ((hsep hxy (fun h => hx (h ▸ hw)) hyw).2 hy)
        exact Or.inr ⟨Or.inr hx, Or.inl hyw⟩
      · exact Or.inr ⟨Or.inr hx, Or.inr hy⟩
  · intro x y hxy hx hy
    simpa only [Set.mem_insert_iff, Set.mem_compl_iff, hx, hy, false_or] using
      not_congr (hsep hxy hx hy)

lemma exists_cut_side_containing (w v : V)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, w ∈ S ∧ v ∈ S ∧ (∃ a ∈ S, a ≠ w) ∧ (∃ b, b ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S) := by
  obtain ⟨S, hw, ⟨a, ha, haw⟩, ⟨b, hb⟩, hsep⟩ := exists_cut_side_of_delete_disconnected hdisc
  by_cases hv : v ∈ S
  · exact ⟨S, hw, hv, ⟨a, ha, haw⟩, ⟨b, hb⟩, hsep⟩
  · have haT : a ∉ insert w Sᶜ := by
      simpa only [Set.mem_insert_iff, Set.mem_compl_iff, haw, false_or, not_not] using ha
    exact ⟨insert w Sᶜ, Or.inl rfl, Or.inr hv, ⟨b, Or.inr hb, fun h => hb (h ▸ hw)⟩,
      ⟨a, haT⟩, (cut_side_pair_properties hw hsep).2.2.2⟩

end Thomassen
