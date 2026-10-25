/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.Lists

/-!
# Lists shortened by deleting a coloured edge

In a graph of girth at least five, deleting the endpoints of an edge from a
three-list instance leaves lists of size at least two. Vertices whose lists have
size at most two form an independent set. This is a local reduction, without any
planarity or extension hypothesis.
-/

@[expose] public section
open Finset
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma neighbors_in_edge_card_le_one (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (w : V) :
    (({a, b} : Finset V).filter (G.Adj w)).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨hx, hwx⟩ := mem_filter.1 hx
  obtain ⟨hy, hwy⟩ := mem_filter.1 hy
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact False.elim (neighbors_nonadjacent hG hwx hwy hab)
  · exact False.elim (neighbors_nonadjacent hG hwy hwx hab)
  · rfl

lemma residual_edge_card_ge_two (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (L : V → Finset C) (c : V → C) (w : V)
    (hL : 3 ≤ (L w).card) : 2 ≤ (residual G L {a, b} c w).card :=
  residual_three_to_two L {a, b} c w hL (neighbors_in_edge_card_le_one hG hab w)

lemma short_residual_edge_neighbor {a b : V} (L : V → Finset C) (c : V → C)
    (w : V) (hL : 3 ≤ (L w).card)
    (hshort : (residual G L {a, b} c w).card ≤ 2) : G.Adj a w ∨ G.Adj b w := by
  by_cases ha : G.Adj a w
  · exact Or.inl ha
  by_cases hb : G.Adj b w
  · exact Or.inr hb
  have heq : residual G L {a, b} c w = L w := by
    apply residual_unchanged
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact fun h => ha h.symm
    · exact fun h => hb h.symm
  rw [heq] at hshort
  omega

/-- Newly shortened lists do not conflict after deleting a coloured edge. -/
lemma short_residual_edge_independent (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (L : V → Finset C) (c : V → C) {x y : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b} c x).card ≤ 2)
    (hyshort : (residual G L {a, b} c y).card ≤ 2) : ¬ G.Adj x y :=
  deleted_edge_neighbors_independent hG hab hxa hxb hya hyb
    (short_residual_edge_neighbor L c x hxL hxshort)
    (short_residual_edge_neighbor L c y hyL hyshort)

end Thomassen
