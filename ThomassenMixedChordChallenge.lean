/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EndpointChordCut

/-! Independent contracts for exact mixed-path restrictions, private-leaf
restoration, short-branch chord reductions and prescribed-path facial order.
None of the five proof modules implementing these contracts is imported.
The unconditional main theorem remains open. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section MixedPathPrecolorContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Avoiding the second separator vertex makes both branches at the prescribed
separator vertex constant in side membership. The retained native path has
exactly the retained original vertices and edges. -/
lemma exists_path_on_two_cut_avoiding (hv : v ∈ S) (b : V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → x ≠ b → y ≠ v → y ≠ b → (x ∈ S ↔ y ∈ S))
    {a z : V} (p : G.Walk a z) (hp : p.IsPath) (hvp : v ∈ p.support) (hb : b ∉ p.support) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  sorry

/-- A mixed cut retains an exact native prescribed path, with its original
six-vertex bound. No assumption about one-sided placement is needed. -/
lemma exists_induce_path_two_cut (P : BoundaryPrecolor G)
    {a t : V} (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : P = .path p hp hn) (hv : v ∈ S) (hvp : v ∈ P.vertices)
    (b : V) (hb : b ∉ P.vertices)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → x ≠ b → y ≠ v → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  sorry

end Thomassen

end MixedPathPrecolorContracts

section ReleasedLeafContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- The private prescribed leaf gets the two-list consisting of its old colour
and its prescribed neighbour's colour. Fixing that neighbour later forces the
leaf's original colour. The empty instance satisfies every short-edge condition. -/
lemma exists_empty_induced_releasing_leaf (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (a b t : V) (haS : a ∈ S) (hbS : b ∈ S)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (htP : t ∈ I.precolor.vertices)
    (hat : G.Adj a t) (htb : t ≠ b)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b ∨ x = t)
    (F : Finset C) (hF : 3 ≤ F.card) :
    ∃ J : BoundaryInstance (G.induce S) C, J.precolor = .empty ∧
      (∀ x : S, x.1 ≠ a → x.1 ≠ b → J.lists x =
        if x.1 = t then {I.prescribed t, I.prescribed a} else I.lists x.1) ∧
      (∀ x : S, I.lists x.1 ⊆ J.lists x) ∧
      OnOuterFace J.embedding J.outer ⟨a, haS⟩ ∧ OnOuterFace J.embedding J.outer ⟨b, hbS⟩ := by
  sorry

end BoundaryInstance
end Thomassen

end ReleasedLeafContracts

section MixedLeafCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A mixed edge cut is closed when one piece has only one private prescribed
vertex, adjacent to the prescribed separator end. Prescriptions elsewhere in the
other piece retain their exact native path and original singleton lists. -/
theorem colourable_of_mixed_leaf_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b t : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    (htP : t ∈ I.precolor.vertices) (hat : G.Adj a t)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = t)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end MixedLeafCutContracts

section ShortPrescriptionChordContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A branch with at most one edge is either a singleton separator or the
private-leaf case; both are complete reductions with exact original lists. -/
theorem colourable_of_mixed_short_branch_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    {d : V} (q : G.Walk a d) (hq : q.length ≤ 1)
    (hQsub : ∀ x ∈ q.support, x ∈ I.precolor.vertices)
    (hcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every mixed cut is closed if either branch at its prescribed separator
end has at most one edge. The other branch may have the full remaining bound. -/
theorem colourable_of_prescription_edge_cut_with_short_branch (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hap : a ∈ p.support)
    (hbranch : (p.takeUntil a hap).length ≤ 1 ∨ (p.dropUntil a hap).length ≤ 1)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every mixed edge cut is closed for a prescribed path with at most three
edges. If its two branches go to different sides, one has at most one edge. -/
theorem colourable_of_short_prescription_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- A facial chord at a prescribed vertex at distance at most one from a
prescribed-path endpoint is closed, including paths with five or six vertices. -/
theorem colourable_of_short_branch_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hip : c i ∈ p.support)
    (hbranch : (p.takeUntil (c i) hip).length ≤ 1 ∨ (p.dropUntil (c i) hip).length ≤ 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The only unresolved branch lengths at a mixed chord are (2,2), (2,3)
and (3,2). These are the central vertices of five/six-vertex prescriptions. -/
lemma remaining_boundary_chord_central_cases (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hip : c i ∈ p.support) :
    ((p.takeUntil (c i) hip).length = 2 ∧ (p.dropUntil (c i) hip).length = 2) ∨
      ((p.takeUntil (c i) hip).length = 2 ∧ (p.dropUntil (c i) hip).length = 3) ∨
      ((p.takeUntil (c i) hip).length = 3 ∧ (p.dropUntil (c i) hip).length = 2) := by
  sorry

/-- Construct the actual strict facial chord cut, then close every case for a
prescribed path on at most four vertices, regardless of its endpoint placement. -/
theorem colourable_of_short_prescription_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 3)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- In a smallest counterexample a boundary chord requires five or six
prescribed path vertices. Empty prescriptions and prescribed cycles are already
closed, and all shorter prescribed paths have now been eliminated as well. -/
lemma boundary_chord_requires_long_prescription (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j)) :
    5 ≤ I.precolor.vertices.card := by
  sorry

end BoundaryInstance
end Thomassen

end ShortPrescriptionChordContracts

section PrescribedPathOrderContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- A path using cycle edges cannot change direction: doing so would repeat
its preceding vertex. The result records every original native vertex in order. -/
lemma path_cycle_order_of_first_step (hc : IsCycleMap G c) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hedges : ∀ n, n < p.length → (cyclicSubgraph G c).Adj (p.getVert n) (p.getVert (n + 1)))
    (i e : ZMod k) (he : e = 1 ∨ e = -1)
    (hzero : p.getVert 0 = c i) (hone : p.getVert 1 = c (i + e)) :
    ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  sorry

/-- Every native simple path in an indexed cycle is one oriented interval. -/
lemma path_cycle_order (hc : IsCycleMap G c) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hedges : ∀ n, n < p.length → (cyclicSubgraph G c).Adj (p.getVert n) (p.getVert (n + 1)))
    (i : ZMod k) (hstart : a = c i) :
    ∃ e : ZMod k, (e = 1 ∨ e = -1) ∧
      ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V] [NeZero k]

/-- In a smallest counterexample the original prescribed path is a contiguous
arc of the actual facial cycle, in one of its two directions. No placement or
corner equations for a spliced path are silently assumed. -/
theorem prescribed_path_follows_facial_cycle (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support) :
    ∃ i e : ZMod k, (e = 1 ∨ e = -1) ∧
      ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  sorry

end BoundaryInstance
end Thomassen

end PrescribedPathOrderContracts
