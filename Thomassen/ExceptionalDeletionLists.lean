/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortLists

/-! The distinguished-endpoint deletion when its colour is absent at the
other endpoint of the unique short-list edge. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A simple two-edge-path exclusion in the original paper is precisely the
common-neighbour exclusion needed for residual short-list independence. -/
lemma no_common_neighbour_of_no_two_path (x : V) (A : Set V)
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    {z : V} (hz : z ∈ A) (hxz : x ≠ z) {w : V}
    (hxw : G.Adj x w) (hwz : G.Adj w z) : False := by
  let p : G.Walk x z := .cons hxw (.cons hwz .nil)
  apply hNo z hz p
  · simp [p,Walk.isPath_def,hxz,hxw.ne,hwz.ne]
  · rfl

/-- Deleting the distinguished vertex with a colour unavailable at the other
short-list endpoint preserves every remaining old short list. -/
lemma exceptional_delete_old_list_unchanged (A : Set V) (x y : V)
    (hxA : x ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (t : C) (hty : t ∉ L y)
    {z : V} (hz : z ∈ A) (hzx : z ≠ x) :
    residual G L {x} (fun _ => t) z = L z := by
  ext c
  rw [mem_residual_iff]
  constructor
  · exact And.left
  · intro hc
    refine ⟨hc,?_⟩
    intro w hw hzw hct
    have hwx : w = x := Finset.mem_singleton.1 hw
    subst w
    rcases hedge z hz x hxA hzw with h | h
    · exact hzx h.1
    · exact hty (by simpa only [h.1,hct] using hc)

/-- Under the original distinguished-endpoint condition, every residual short
edge disappears after this deletion. The old unique edge is removed, a new
short vertex cannot meet old A, and two new short vertices are nonadjacent by
the triangle exclusion. -/
lemma exceptional_delete_short_lists_independent (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (t : C) {z w : V} (hzx : z ≠ x) (hwx : w ≠ x)
    (hz : (residual G L {x} (fun _ => t) z).card ≤ 2)
    (hw : (residual G L {x} (fun _ => t) w).card ≤ 2) : ¬ G.Adj z w := by
  have hclass : ∀ v, (residual G L {x} (fun _ => t) v).card ≤ 2 →
      v ∈ A ∨ G.Adj x v := by
    intro v hv
    by_cases hA : v ∈ A
    · exact Or.inl hA
    · right
      by_contra hn
      have heq : residual G L {x} (fun _ => t) v = L v := by
        apply residual_unchanged
        intro a ha
        have he : a = x := Finset.mem_singleton.1 ha
        subst a
        exact fun h => hn h.symm
      have h3 := hLthree v hA
      rw [heq] at hv
      omega
  intro hzw
  rcases hclass z hz with hzA | hxz <;> rcases hclass w hw with hwA | hxw
  · rcases hedge z hzA w hwA hzw with h | h
    · exact hzx h.1
    · exact hwx h.2
  · exact no_common_neighbour_of_no_two_path x A hNo hzA hzx.symm hxw hzw.symm
  · exact no_common_neighbour_of_no_two_path x A hNo hwA hwx.symm hxz hzw
  · exact neighbors_nonadjacent hg hxz hxw hzw

end Thomassen
