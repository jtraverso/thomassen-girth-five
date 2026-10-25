/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalResidualDeletion

/-! The two-vertex deletion in original reduction (9). -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Old short vertices outside the exceptional edge lose no colours when
both exceptional endpoints are deleted. -/
theorem exceptional_pair_old_list_unchanged (A : Set V) (x y : V) (hxA : x ∈ A) (hyA : y ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (f : V → C) {z : V} (hzA : z ∈ A) (hzx : z ≠ x) (hzy : z ≠ y) :
    residual G L {x,y} f z = L z := by
  apply residual_unchanged
  intro w hw hzw
  rcases Finset.mem_insert.1 hw with rfl | hw
  · rcases hedge z hzA _ hxA hzw with h | h
    · exact hzx h.1
    · exact hzy h.1
  · have hw' : w=y := Finset.mem_singleton.1 hw
    subst w
    rcases hedge z hzA y hyA hzw with h | h
    · exact hzx h.1
    · exact hzy h.1

/-- The only possible old/new conflict after deleting the exceptional edge
is a two-edge path from its nondistinguished endpoint to an old short vertex.
Excluding those paths makes the entire residual marked short set independent. -/
theorem exceptional_pair_short_vertices_independent (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V)
    (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNoX : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (hNoY : ∀ z ∈ A, z ≠ x → z ≠ y → ∀ w, w ≠ x → w ≠ y → G.Adj y w → G.Adj w z → False)
    {z w : V} (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y)
    (hz : z ∈ A ∨ G.Adj x z ∨ G.Adj y z)
    (hw : w ∈ A ∨ G.Adj x w ∨ G.Adj y w) : ¬ G.Adj z w := by
  intro hzw
  rcases hz with hzA | hzn <;> rcases hw with hwA | hwn
  · rcases hedge z hzA w hwA hzw with h | h
    · exact hzx h.1
    · exact hzy h.1
  · rcases hwn with hxw | hyw
    · exact no_common_neighbour_of_no_two_path x A hNoX hzA hzx.symm hxw hzw.symm
    · exact hNoY z hzA hzx hzy w hwx hwy hyw hzw.symm
  · rcases hzn with hxz | hyz
    · exact no_common_neighbour_of_no_two_path x A hNoX hwA hwx.symm hxz hzw
    · exact hNoY w hwA hwx hwy z hzx hzy hyz hzw
  · exact deleted_edge_neighbors_independent hg hxy hzx hzy hwx hwy hzn hwn hzw

/-- Every remaining list has at least two colours after deleting the coloured
exceptional edge. No equal-list assumption is necessary. -/
theorem exceptional_pair_residual_card_ge_two (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card) (f : V → C)
    {z : V} (hzx : z ≠ x) (hzy : z ≠ y) : 2 ≤ (residual G L {x,y} f z).card := by
  by_cases hzA : z ∈ A
  · rw [exceptional_pair_old_list_unchanged A x y hxA hyA hedge L f hzA hzx hzy]
    exact hLtwo z
  · exact residual_edge_card_ge_two hg hxy L f z (hLthree z hzA)

end Thomassen
