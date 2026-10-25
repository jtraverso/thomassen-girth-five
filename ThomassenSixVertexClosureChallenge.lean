/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexRemainingExceptions
public import Thomassen.Assembly

/-! Independent contracts for the complete six-vertex case, global boundary
extension and unconditional main theorem. None of the six new proof modules
is imported; the actual original main contract is checked separately as well. -/
@[expose] public section
universe u v

section SixVertexAlternatingFreeDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- In the alternating short-list branch, delete only the first three free
boundary vertices. Every original prescribed vertex is retained. This closes
all six-vertex prescriptions, allowing mixed witnesses as pendant vertices,
if the interior three-path between
the first and third deleted vertices is absent. -/
theorem colourable_of_six_vertex_alternating_path_without_interior_three_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj (p.getVert (p.length-1)) x → G.Adj x y → G.Adj y (p.getVert (p.length-3)) → False)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexAlternatingFreeDeletionContracts

section SixVertexFiveFaceAttachmentsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- An interior vertex attached outside a free five-face cannot also meet
an old free short list or either old prescribed endpoint. Thus the new short
lists can only attach to internal vertices of the retained prescription. -/
theorem inner_five_face_attachment_no_forbidden_boundary_neighbour_six (I : BoundaryInstance G C)
    {s t a : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
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

end SixVertexFiveFaceAttachmentsContracts

section SixVertexFiveFaceDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- All residual-state conditions for a free inner five-face follow from
the proved geometric exclusions. The inputs describe only a concrete proper
colouring of the deleted cycle, preservation of old short lists, and the old
boundary lists adjacent to that cycle. -/
theorem colourable_of_free_inner_five_face_deletion_six (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
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

end SixVertexFiveFaceDeletionContracts

section SixVertexFiveFaceColouringContracts

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
theorem colourable_of_free_inner_five_face_short_neighbours_six (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length)
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (hprev : (I.lists (p.getVert (p.length-1))).card ≤ 2)
    (hnextroot : p.getVert 3=s)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexFiveFaceColouringContracts

section SixVertexPathClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The six-vertex case, including both mixed exceptions, uses independent
short leaves attached only to internal prescribed vertices. -/
theorem colourable_of_six_vertex_prescribed_path_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The complete six-vertex path case for the original arbitrary selected face
and either orientation. The main induction is called only at smaller cardinality. -/
theorem colourable_of_six_vertex_prescribed_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SixVertexPathClosureContracts

section BoundaryExtensionContracts

open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical

/-- Strong induction discharges all boundary instances: every possible
remaining counterexample would have the now completed six-vertex prescription. -/
theorem boundary_instances_colourable_at_card (C : Type v) (n : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (I : BoundaryInstance G C),
      Nat.card V=n → ListColourable G I.lists := by
  sorry
/-- The full boundary-extension theorem. This is proved, rather than assumed
as a parameter of the unconditional planar list-colouring result. -/
theorem boundary_extension (C : Type v) : BoundaryExtension.{u,v} C := by
  sorry
end Thomassen

namespace PlanarChoosability

/-- Thomassen (1995): every finite planar graph of extended girth at least
five is three-choosable over any colour type. -/
theorem choosableWith_three_of_isPlanar {V : Type*} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : ChoosableWith G C 3 := by
  sorry
end PlanarChoosability

end BoundaryExtensionContracts
