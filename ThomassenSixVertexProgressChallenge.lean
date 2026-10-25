/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FiveVertexPathClosure

/-! Separate contracts for the six-vertex good-fourth exception, generalized
free deletions and exact remaining mixed configurations. None of the ten new
proof modules is imported. The complete six-vertex case remains open.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section ConnectedResidualPinningContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

omit [Fintype V] in
/-- Residual lists depend only on the coloured neighbours of the vertex. -/
theorem residual_eq_of_same_neighbours (L : V → Finset C) (A B : Finset V) (f : V → C) (x : V)
    (h : ∀ y, G.Adj x y → (y ∈ A ↔ y ∈ B)) : residual G L A f x = residual G L B f x := by
  sorry
namespace BoundaryInstance

/-- After a connected boundary deletion, extend a proper connected residual
prescription whose simple paths have at most six vertices, without requiring
its residual lists to have at most two colours. The short-edge premise accounts
for the new singleton lists after pinning. Prescribed vertices
may be newly exposed neighbours of the deletion. Each actual remaining
component is treated separately, so deletion connectivity is not assumed. -/
theorem colourable_of_connected_residual_prescription_with_pinning (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (Q : Set V) (hQconn : ConnSet G Q) (hQA : ∀ x ∈ Q, x ∉ A)
    (hQface : ∀ x ∈ Q, OnOuterFace I.embedding I.outer x ∨ ∃ y ∈ A, G.Adj x y)
    (hQpaths : ∀ {x y : V} (q : G.Walk x y), q.IsPath →
      (∀ z ∈ q.support, z ∈ Q) → q.length ≤ 5)
    (g : V → C) (hg : ∀ x ∈ Q, g x ∈ residual G I.lists A f x)
    (hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y)
    (hTwo : ∀ x, x ∉ A → x ∉ Q → 2 ≤ (residual G I.lists A f x).card)
    (hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (x ∈ Q ∨ (residual G I.lists A f x).card ≤ 2) →
      (y ∈ Q ∨ (residual G I.lists A f y).card ≤ 2) → x ∈ Q ∧ y ∈ Q)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end BoundaryInstance
end Thomassen

end ConnectedResidualPinningContracts

section SixVertexExceptionalGoodFourthContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
set_option maxHeartbeats 1000000
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The backward mixed exception in the good-fourth-list branch is closed.
The interior witness is retained, and the remaining four old prescribed
vertices form a connected five-vertex replacement prescription with it. -/
theorem colourable_of_six_vertex_backward_exception_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hub : G.Adj u (p.getVert (p.length-1))) (hu2 : G.Adj u (r.getVert 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexExceptionalGoodFourthContracts

section SixVertexGoodFourthClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The good-fourth branch no longer has an exceptional hypothesis: the
unique problematic interior witness is retained by the replacement prescription. -/
theorem colourable_of_six_vertex_path_short_second_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- A remaining six-vertex counterexample must have short lists at both
the second and fourth backward positions. This includes the mixed exception. -/
theorem remaining_six_vertex_counterexample_has_short_second_and_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧ (I.lists (p.getVert (p.length-4))).card ≤ 2 := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexGoodFourthClosureContracts

section SixVertexUniqueBoundaryResidualContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A connected deletion can expose arbitrarily many short neighbours of
the old prescription. If these neighbours are independent and avoid its two
ends, they can all be fixed as pendant vertices and extended on strictly
smaller actual face pieces. No bound on the number of leaves is required. -/
theorem colourable_of_residual_short_leaves_unique_parent (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {s t : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hrlen : r.length ≤ 5)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (hPA : ∀ x ∈ I.precolor.vertices, x ∉ A)
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (hResP : ∀ x ∈ I.precolor.vertices, residual G I.lists A f x = {I.prescribed x})
    (hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f x).card)
    (hIndependent : ∀ x, x ∉ A → x ∉ I.precolor.vertices → ∀ y, y ∉ A → y ∉ I.precolor.vertices →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → ¬ G.Adj x y)
    (hEnds : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (residual G I.lists A f x).card ≤ 2 →
      ¬ G.Adj x s ∧ ¬ G.Adj x t)
    (hUnique : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (residual G I.lists A f x).card ≤ 2 →
      ∀ y ∈ I.precolor.vertices, ∀ z ∈ I.precolor.vertices, G.Adj x y → G.Adj x z → y=z)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryResidualContracts

section SixVertexUniqueBoundaryAttachmentsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- An interior vertex attached outside a free five-face cannot also meet
an old free short list or either old prescribed endpoint. Thus the new short
lists can only attach to internal vertices of the retained prescription. -/
theorem inner_five_face_attachment_no_forbidden_boundary_neighbour_unique_boundary (I : BoundaryInstance G C)
    {s t a : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haP : a ∉ I.precolor.vertices) (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u z : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : OnOuterFace I.embedding I.outer z)
    (hzA : z ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (huN : ∃ w ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj u w)
    (hforbidden : (z ∉ I.precolor.vertices ∧ (I.lists z).card ≤ 2) ∨ z=s ∨ z=t) : ¬ G.Adj u z := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryAttachmentsContracts

section SixVertexUniqueBoundaryFiveDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- All residual-state conditions for a free inner five-face follow from
the proved geometric exclusions. The inputs describe only a concrete proper
colouring of the deleted cycle, preservation of old short lists, and the old
boundary lists adjacent to that cycle. -/
theorem colourable_of_free_inner_five_face_deletion_unique_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length)
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (c : G.Walk a a) (hc : c.IsCycle) (hclen : c.length=5)
    (hC : ∀ z, z ∈ c.support ↔ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (f : V → C) (hf : ∀ z ∈ c.support, f z ∈ I.lists z)
    (hproper : ∀ z ∈ c.support, ∀ w ∈ c.support, G.Adj z w → f z ≠ f w)
    (hOldUnchanged : ∀ z, z ∉ c.support → (I.lists z).card ≤ 2 →
      residual G I.lists c.support.toFinset f z = I.lists z)
    (hBoundaryShort : ∀ z, z ∉ c.support → OnOuterFace I.embedding I.outer z →
      (∃ w ∈ c.support, G.Adj z w) → (I.lists z).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryFiveDeletionContracts

section SixVertexUniqueBoundaryFiveColouringContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
set_option maxHeartbeats 800000
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The free five-face can be coloured and deleted when the preceding
boundary list is short and the following one is a singleton. The entire old
prescription is retained. All residual lists and actual component faces are
handled by the previously proved deletion and pendant-prescription lemmas. -/
theorem colourable_of_free_inner_five_face_short_neighbours_unique_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length)
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (hprev : (I.lists (p.getVert (p.length-1))).card ≤ 2)
    (hnext : (I.lists (p.getVert 3)).card ≤ 1)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryFiveColouringContracts

section SixVertexUniqueBoundaryThreeDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- In the alternating short-list branch, delete only the first three free
boundary vertices. Every original prescribed vertex is retained. This closes
all prescriptions on at most six vertices under boundary-neighbour uniqueness,
if the interior three-path between
the first and third deleted vertices is absent. -/
theorem colourable_of_alternating_free_path_without_interior_three_path_unique_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj (p.getVert (p.length-1)) x → G.Adj x y → G.Adj y (p.getVert (p.length-3)) → False)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryThreeDeletionContracts

section SixVertexUniqueBoundaryClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- All six-vertex cases are closed if no interior vertex meets two old
boundary vertices. The complete exceptional configurations are isolated separately. -/
theorem colourable_of_six_vertex_path_with_unique_boundary_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexUniqueBoundaryClosureContracts

section SixVertexRemainingExceptionsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Without assuming any incidence exclusion, a remaining six-vertex
counterexample contains one of the two permitted mixed two-path
configurations, at the initial or terminal free boundary neighbour. -/
theorem remaining_six_vertex_counterexample_has_mixed_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧ (I.lists (p.getVert (p.length-4))).card ≤ 2 ∧
      ∃ u, ¬ OnOuterFace I.embedding I.outer u ∧
        ((G.Adj u (r.getVert 2) ∧ G.Adj u (p.getVert (p.length-1))) ∨
         (G.Adj u (r.getVert 3) ∧ G.Adj u (p.getVert 6))) := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexRemainingExceptionsContracts
