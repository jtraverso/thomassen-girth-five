/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortPathGoodFourthDeletion
public import Thomassen.ShortCycleReduction

/-! Separate contracts for the six-vertex nonexceptional deletion, actual
short-cycle saturation, and the complete three-vertex prescribed-path case.
None of the seven new proof modules is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section BoundaryPairClassificationContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Every distinct boundary-neighbour pair of an interior vertex is exactly
one of the two mixed six-vertex exceptions, in either order. -/
theorem interior_boundary_pair_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxy : x ≠ y) (hux : G.Adj u x) (huy : G.Adj u y) :
    r.length=5 ∧
    ((x=r.getVert 2 ∧ y ∉ I.precolor.vertices ∧ G.Adj a y) ∨
     (x=r.getVert 3 ∧ y ∉ I.precolor.vertices ∧ G.Adj t y) ∨
     (y=r.getVert 2 ∧ x ∉ I.precolor.vertices ∧ G.Adj a x) ∨
     (y=r.getVert 3 ∧ x ∉ I.precolor.vertices ∧ G.Adj t x)) := by
  sorry
/-- An old short free boundary vertex cannot participate in either mixed
exception, because each exceptional free vertex adjoins a prescribed end. -/
theorem interior_neighbours_unique_at_short_free_boundary_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hxShort : (I.lists x).card ≤ 2)
    (hux : G.Adj u x) (huy : G.Adj u y) : x=y := by
  sorry
end Thomassen.BoundaryInstance

end BoundaryPairClassificationContracts

section SixPathGoodFourthDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- Delete the initial prescribed vertex and the first two backward free
boundary vertices. A short second list and a three-list at the fourth suffice
for every nontrivial original prescribed path on at most six vertices
when the backward six-vertex two-path exception is absent. -/
theorem colourable_of_path_short_second_good_fourth_without_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    {t0 : V} (r : G.Walk a t0) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hNoException : ∀ z, ¬ OnOuterFace I.embedding I.outer z →
      G.Adj z (p.getVert (p.length-1)) → ¬ G.Adj z (r.getVert 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- A remaining good-fourth-list counterexample necessarily has all six
prescribed vertices and the backward exceptional common neighbour. Thus the
general nonexceptional branch is closed without a five-vertex restriction. -/
theorem remaining_good_fourth_counterexample_has_backward_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    {t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    r.length=5 ∧ ∃ u, ¬ OnOuterFace I.embedding I.outer u ∧
      G.Adj u (p.getVert (p.length-1)) ∧ G.Adj u (r.getVert 2) := by
  sorry
end Thomassen.BoundaryInstance

end SixPathGoodFourthDeletionContracts

section ShortArcSaturationContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- If a short native cycle follows an old facial arc and some old face
vertex lies outside it, the arc vertices have no neighbours outside the cycle
in a smallest counterexample. Both face regions and the strict short-cycle
reduction are used; no empty-region assumption is supplied. -/
theorem neighbours_on_short_facial_arc_stay_on_cycle (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6) (A : Set V) (hAC : A ⊆ {x | x ∈ p.support})
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) A)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ p.support := by
  sorry
/-- In the same setting the backward open region is empty, while the forward
region contains an actual old face vertex outside the cycle. -/
theorem short_facial_arc_backward_region_empty (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ w, ¬ inSubface I.embedding cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) 0) w := by
  sorry
/-- Close a short prefix of the actual old face by an interior path. When
the resulting cycle has at most six vertices, every neighbour of an internal
prefix vertex lies on that cycle in a smallest counterexample. The facial
arc, its old root and a genuine outside vertex are all derived. -/
theorem neighbours_on_short_closed_face_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i : ℕ) (hi : 0 < i) (hin : i < n) (y : V) (hadj : G.Adj (p.getVert i) y) :
    y ∈ (spliceFacePath p n q).support := by
  sorry
end Thomassen.BoundaryInstance

end ShortArcSaturationContracts

section ExceptionalFiveCycleContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The backward mixed exception determines a short five-cycle through the
first three prescribed vertices. Its two internal old facial vertices have
exactly their two cycle neighbours. Extra neighbours would create a nonempty
inner region, already excluded by strict short-cycle induction. -/
theorem backward_exception_prescribed_end_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hub : G.Adj u (p.getVert (p.length-1))) (hu2 : G.Adj u (r.getVert 2))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (∀ y, G.Adj a y → y=r.getVert 1 ∨ y=p.getVert (p.length-1)) ∧
    (∀ y, G.Adj (r.getVert 1) y → y=a ∨ y=r.getVert 2) := by
  sorry
end Thomassen.BoundaryInstance

end ExceptionalFiveCycleContracts

section ThreeVertexAlternatingListsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- With three consecutive prescribed vertices, a short fourth backward
list is resolved by precolouring a six-vertex native boundary path. The only enlarged
list gets the adjacent prescribed colour as its extra colour, so every resulting
colouring restores that original list. Only the strict main induction is used. -/
theorem colourable_of_three_vertex_path_short_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1 ∨ x = p.getVert 2)
    (hlen : 8 ≤ p.length) (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end ThreeVertexAlternatingListsContracts

section ThreeVertexSixFaceContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- Three consecutive prescribed vertices on an actual six-vertex face
extend: colour the middle free vertex first, then its two three-list neighbours.
The existing compatible full-cycle theorem handles all interior vertices. -/
theorem colourable_of_three_prescribed_vertices_six_vertex_face (I : BoundaryInstance G C)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x=a ∨ x=p.getVert 1 ∨ x=p.getVert 2)
    (hlen : p.length=6)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end ThreeVertexSixFaceContracts

section ThreeVertexPathClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- All native-face cases with three consecutive prescribed vertices are
closed. This includes the alternating short lists and the six-vertex face. -/
theorem colourable_of_three_vertex_prescribed_path_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=2)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The entire three-vertex prescribed-path case, with the original arbitrary
face and either native direction. Only the strict main induction is assumed. -/
theorem colourable_of_three_vertex_prescribed_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- All nontrivial native prescriptions on at most three vertices are now
complete induction cases: an edge, or the three-vertex path above. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_three (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn3 : r.support.toFinset.card ≤ 3)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end ThreeVertexPathClosureContracts
