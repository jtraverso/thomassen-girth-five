/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortLists

/-!
# Deleting three consecutive vertices

These local reductions are used in both Thomassen's 1995 proof and the expanded
list-colouring proof in Chapter 3 of Asghar's 2012 essay. A remaining vertex
loses at most one colour. An edge between newly shortened lists forces a simple
three-edge path between the endpoints of the deleted two-edge path.

No planarity, face separation, or extension theorem is assumed or proved here.
-/

@[expose] public section
open Finset SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma short_residual_neighbor (L : V → Finset C) (S : Finset V) (c : V → C)
    (w : V) (hL : 3 ≤ (L w).card)
    (hshort : (residual G L S c w).card ≤ 2) : ∃ z ∈ S, G.Adj z w := by
  by_contra hn
  have heq : residual G L S c w = L w := by
    apply residual_unchanged
    intro z hz hwz
    exact hn ⟨z, hz, hwz.symm⟩
  rw [heq] at hshort
  omega

lemma neighbors_in_two_edge_path_card_le_one (hG : 5 ≤ G.egirth) {a b d w : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d) (hwb : w ≠ b) :
    (({a, b, d} : Finset V).filter (G.Adj w)).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨hx, hwx⟩ := mem_filter.1 hx
  obtain ⟨hy, hwy⟩ := mem_filter.1 hy
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · rfl
  · exact False.elim (neighbors_nonadjacent hG hwx hwy hab)
  · exact False.elim (hwb (common_neighbor_unique hG had hwx.symm hwy.symm hab hbd.symm))
  · exact False.elim (neighbors_nonadjacent hG hwy hwx hab)
  · rfl
  · exact False.elim (neighbors_nonadjacent hG hwx hwy hbd)
  · exact False.elim (hwb (common_neighbor_unique hG had hwy.symm hwx.symm hab hbd.symm))
  · exact False.elim (neighbors_nonadjacent hG hwy hwx hbd)
  · rfl

lemma residual_two_edge_path_card_ge_two (hG : 5 ≤ G.egirth) {a b d w : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d) (hwb : w ≠ b)
    (L : V → Finset C) (c : V → C) (hL : 3 ≤ (L w).card) :
    2 ≤ (residual G L {a, b, d} c w).card :=
  residual_three_to_two L {a, b, d} c w hL
    (neighbors_in_two_edge_path_card_le_one hG hab hbd had hwb)

/-- An adjacency among exposed neighbours must connect the two endpoints' sides. -/
lemma deleted_two_edge_path_adjacent_neighbors (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (hxn : G.Adj a x ∨ G.Adj b x ∨ G.Adj d x)
    (hyn : G.Adj a y ∨ G.Adj b y ∨ G.Adj d y) (hxy : G.Adj x y) :
    (G.Adj a x ∧ G.Adj d y) ∨ (G.Adj d x ∧ G.Adj a y) := by
  simp only [mem_insert, mem_singleton, not_or] at hx hy
  have habex : ¬ ((G.Adj a x ∨ G.Adj b x) ∧ (G.Adj a y ∨ G.Adj b y)) := by
    rintro ⟨h1, h2⟩
    exact deleted_edge_neighbors_independent hG hab hx.1 hx.2.1 hy.1 hy.2.1 h1 h2 hxy
  have hbdex : ¬ ((G.Adj b x ∨ G.Adj d x) ∧ (G.Adj b y ∨ G.Adj d y)) := by
    rintro ⟨h1, h2⟩
    exact deleted_edge_neighbors_independent hG hbd hx.2.1 hx.2.2 hy.2.1 hy.2.2 h1 h2 hxy
  rcases hxn with hxa | hxb | hxd <;> rcases hyn with hya | hyb | hyd
  · exact False.elim (habex ⟨Or.inl hxa, Or.inl hya⟩)
  · exact False.elim (habex ⟨Or.inl hxa, Or.inr hyb⟩)
  · exact Or.inl ⟨hxa, hyd⟩
  · exact False.elim (habex ⟨Or.inr hxb, Or.inl hya⟩)
  · exact False.elim (habex ⟨Or.inr hxb, Or.inr hyb⟩)
  · exact False.elim (hbdex ⟨Or.inl hxb, Or.inr hyd⟩)
  · exact Or.inr ⟨hxd, hya⟩
  · exact False.elim (hbdex ⟨Or.inr hxd, Or.inl hyb⟩)
  · exact False.elim (hbdex ⟨Or.inr hxd, Or.inr hyd⟩)

lemma short_residual_two_edge_path_adjacent (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2) (hxy : G.Adj x y) :
    (G.Adj a x ∧ G.Adj d y) ∨ (G.Adj d x ∧ G.Adj a y) := by
  have hn (w : V) (hwL : 3 ≤ (L w).card)
      (hws : (residual G L {a, b, d} c w).card ≤ 2) :
      G.Adj a w ∨ G.Adj b w ∨ G.Adj d w := by
    obtain ⟨z, hz, hzw⟩ := short_residual_neighbor L {a, b, d} c w hwL hws
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Or.inl hzw
    · exact Or.inr (Or.inl hzw)
    · exact Or.inr (Or.inr hzw)
  exact deleted_two_edge_path_adjacent_neighbors hG hab hbd hx hy
    (hn x hxL hxshort) (hn y hyL hyshort) hxy

/-- The exceptional adjacency is witnessed by a native simple three-edge path. -/
lemma short_residual_two_edge_path_forces_three_path (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2) (hxy : G.Adj x y) :
    ∃ p : G.Walk a d, p.IsPath ∧ p.length = 3 ∧ b ∉ p.support := by
  have key {r s : V} (hr : r ∉ ({a, b, d} : Finset V))
      (hs : s ∉ ({a, b, d} : Finset V)) (har : G.Adj a r)
      (hrs : G.Adj r s) (hsd : G.Adj s d) :
      ∃ p : G.Walk a d, p.IsPath ∧ p.length = 3 ∧ b ∉ p.support := by
    simp only [mem_insert, mem_singleton, not_or] at hr hs
    let p : G.Walk a d := .cons har (.cons hrs (.cons hsd .nil))
    refine ⟨p, ?_, rfl, ?_⟩
    · simp [p, Walk.isPath_def, had, hr.1, hr.2.2, hs.1, hs.2.2, hrs.ne, Ne.symm]
    · simp [p, hab.ne, hbd.ne, hr.2.1, hs.2.1, Ne.symm]
  rcases short_residual_two_edge_path_adjacent hG hab hbd hx hy L c hxL hyL
      hxshort hyshort hxy with h | h
  · exact key hx hy h.1 hxy h.2.symm
  · exact key hy hx h.2 hxy.symm h.1.symm

lemma short_residual_two_edge_path_independent (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2)
    (hno : ∀ p : G.Walk a d, p.IsPath → p.length = 3 → b ∉ p.support → False) :
    ¬ G.Adj x y := by
  intro hxy
  obtain ⟨p, hp, hlen, havoid⟩ := short_residual_two_edge_path_forces_three_path
    hG hab hbd had hx hy L c hxL hyL hxshort hyshort hxy
  exact hno p hp hlen havoid

end Thomassen
