/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace Thomassen
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The girth convention includes forests: their extended girth is infinity. -/
theorem five_le_egirth_iff : 5 ≤ G.egirth ↔
    ∀ a (w : G.Walk a a), w.IsCycle → 5 ≤ w.length := by
  constructor
  · intro h a w hw
    exact_mod_cast (le_egirth.1 h a w hw)
  · intro h
    rw [le_egirth]
    intro a w hw
    exact_mod_cast h a w hw

/-- Subgraphs inherit the required girth. -/
theorem five_le_egirth_of_le {H : SimpleGraph V} (hG : 5 ≤ G.egirth) (hHG : H ≤ G) :
    5 ≤ H.egirth := hG.trans (SimpleGraph.egirth_anti hHG)

/-- The native Mathlib girth condition excludes triangles. -/
theorem cliqueFree_three (hG : 5 ≤ G.egirth) : G.CliqueFree 3 := by
  intro s hs
  obtain ⟨a, w, hw, hlen⟩ := SimpleGraph.is3Clique_iff_exists_cycle_length_three.1 ⟨s, hs⟩
  have h := five_le_egirth_iff.1 hG a w hw
  omega

/-- Neighbours of a vertex are pairwise nonadjacent. -/
theorem neighbors_nonadjacent (hG : 5 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c := by
  classical
  intro hbc
  exact cliqueFree_three hG {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)

/-- In girth at least five, distinct vertices have at most one common neighbour. -/
theorem common_neighbor_unique (hG : 5 ≤ G.egirth) {a b x y : V} (hab : a ≠ b)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  classical
  by_contra hxy
  let w : G.Walk a a := .cons hax (.cons hbx.symm (.cons hby (.cons hay.symm .nil)))
  have hw : w.IsCycle := by
    simp [w, Walk.cons_isCycle_iff, Walk.isPath_def, hax.ne, hbx.ne, hay.ne, hby.ne,
      hab, hxy, Ne.symm]
  have h := five_le_egirth_iff.1 hG a w hw
  simp [w] at h

/-- For an edge, its two open neighbourhoods are disjoint. -/
theorem edge_neighborhoods_disjoint (hG : 5 ≤ G.egirth) {a b : V} (hab : G.Adj a b) :
    Disjoint (G.neighborSet a) (G.neighborSet b) := by
  rw [Set.disjoint_left]
  intro x hax hbx
  exact neighbors_nonadjacent hG hab hax hbx

/-- After deleting an edge, all its remaining neighbours form an independent set.
This is the structural reason that two newly shortened lists cannot conflict. -/
theorem deleted_edge_neighbors_independent (hG : 5 ≤ G.egirth) {a b x y : V}
    (hab : G.Adj a b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : G.Adj a x ∨ G.Adj b x) (hy : G.Adj a y ∨ G.Adj b y) : ¬ G.Adj x y := by
  intro hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact neighbors_nonadjacent hG hx hy hxy
  · exact hxb (common_neighbor_unique hG hya.symm hx hxy.symm hab hy.symm)
  · exact hxa (common_neighbor_unique hG hyb.symm hx hxy.symm hab.symm hy.symm)
  · exact neighbors_nonadjacent hG hx hy hxy

end Thomassen
