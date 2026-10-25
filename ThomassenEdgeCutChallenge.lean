/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CutPrecolor
public import Thomassen.ChordSeparation

/-! Independent contracts for restrictions and induction at prescribed edge cuts.
Neither EdgeCutPrecolor nor EdgeCutReduction is imported. The full induction
contract requires both separator endpoints to be prescribed, but makes no
assumption placing the remaining prescription in one side. -/

@[expose] public section
section EdgeCutPrecolorContracts
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a b : V} {S : Set V}

/-- A path from one separator endpoint, avoiding the other endpoint, stays in
one side or meets it only at its initial vertex. -/
lemma path_side_dichotomy_of_avoids_other (ha : a ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z : V} (p : G.Walk a z) (hp : p.IsPath) (hb : b ∉ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a) := by
  sorry

/-- Oriented-edge version of the exact prescribed path restriction. -/
lemma exists_path_on_oriented_edge_cut (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (he : hab.toWalk.IsSubwalk p) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  sorry

/-- The exact path restriction works for either orientation of the prescribed
separator edge. Its support, edges and vertex bound can be transported intact. -/
lemma exists_path_on_edge_cut (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (he : s(a, b) ∈ p.edges) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  sorry

/-- A simple cycle rooted at one end of a prescribed separator edge lies in
one side or meets it exactly in the two ends of that edge. -/
lemma rooted_cycle_side_dichotomy_on_edge (ha : a ∈ S) (hb : b ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    (p : G.Walk a a) (hp : p.IsCycle) (he : s(a, b) ∈ p.edges) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a ∨ x = b) := by
  sorry

/-- Rotation gives the same cycle dichotomy independently of its native root. -/
lemma cycle_side_dichotomy_on_edge (ha : a ∈ S) (hb : b ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z : V} (p : G.Walk z z) (hp : p.IsCycle) (he : s(a, b) ∈ p.edges) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a ∨ x = b) := by
  sorry

/-- Restricting the exact prescription at a two-vertex cut containing one of
its edges again gives a native prescribed path/cycle, even when the old
prescription has vertices on both sides of the cut. -/
lemma BoundaryPrecolor.exists_induce_edge_cut (P : BoundaryPrecolor G)
    (ha : a ∈ S) (hb : b ∈ S) (he : s(a, b) ∈ P.edges)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  sorry

end Thomassen

end EdgeCutPrecolorContracts

section EdgeCutReductionContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Edge coverage and the exact two-endpoint intersection give side constancy
for every edge avoiding both separator vertices. -/
lemma edge_cut_side_constancy (S T : Set V) (a b : V)
    (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Complete two-piece induction when both ends of the separator edge are
prescribed. The exact native prescription is constructed independently on each
piece; no assumption places all remaining prescribed vertices in one side. -/
theorem colourable_of_prescribed_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (hab : G.Adj a b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∈ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Connected) (hTconn : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The facial-chord reduction for arbitrary placement of the remaining
prescription, when both chord endpoints are prescribed. -/
theorem colourable_of_prescribed_facial_chord_general (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hArc : IsFacialWalkArc I.embedding p hp)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (haP : a ∈ I.precolor.vertices) (hbP : p.penultimate ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end EdgeCutReductionContracts
