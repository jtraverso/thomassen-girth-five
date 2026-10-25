/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.LongPrescriptionReduction

/-! Separate contracts for the alternating free deletion, short-face geometry,
pendant residual prescriptions and complete four- and five-vertex path cases.
None of the twelve new proof modules is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section AlternatingFreePathDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- In the alternating short-list branch, delete only the first three free
boundary vertices. Every original prescribed vertex is retained. This closes
all prescriptions on at most five vertices if the interior three-path between
the first and third deleted vertices is absent. -/
theorem colourable_of_alternating_free_path_without_interior_three_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj (p.getVert (p.length-1)) x → G.Adj x y → G.Adj y (p.getVert (p.length-3)) → False)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end AlternatingFreePathDeletionContracts

section ShortCycleFacePreservationContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A chordless cycle with no vertices in one open region has no gaps in
that region. Its face permutation is therefore preserved in the original map. -/
theorem facePerm_preserved_of_chordless_empty_region (M : PlaneMap G)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c)
    (hch : IsChordless G c) (o : (cyclicSubgraph G c).Dart)
    (hempty : ∀ w, ¬ inSubface M cyclicSubgraph_le o w)
    (e : (cyclicSubgraph G c).Dart)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm o e) :
    M.facePerm (toDart cyclicSubgraph_le e) =
      toDart cyclicSubgraph_le ((restrictMap M cyclicSubgraph_le).facePerm e) := by
  sorry
/-- A fully preserved backward cycle is precisely the vertex set of its
actual original face orbit, including at a fixed first backward edge. -/
theorem outerFace_vertices_of_backward_cycle_preserved (M : PlaneMap G)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : ∀ i, M.facePerm (toDart cyclicSubgraph_le (cycleBackward hc i)) =
      toDart cyclicSubgraph_le (cycleBackward hc (i-1))) (z : V) :
    OnOuterFace M (toDart cyclicSubgraph_le (cycleBackward hc 1)) z ↔ z ∈ Set.range c := by
  sorry
namespace BoundaryInstance
variable {C : Type v}

/-- In a smallest counterexample, the backward side of a short cycle
sharing an actual old facial edge is itself an actual face, whenever an old
face vertex lies outside the cycle. -/
theorem short_facial_arc_backward_face_preserved (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i : ZMod p.length) :
    I.embedding.facePerm (toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) i)) =
      toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) (i-1)) := by
  sorry
/-- All vertices on the inner face of a short closed old-face prefix are
exactly the vertices of that short native cycle. The original face root on
the first reversed edge is independent of the closing interior path. -/
theorem short_closed_face_prefix_inner_face_vertices (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (_hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) (z : V) :
    OnOuterFace I.embedding
      (walkArcRoot p hp).symm z ↔
      z ∈ (spliceFacePath p n q).support := by
  sorry
/-- Two short interior paths closing the same old facial prefix determine
the same inner-face vertices and have the same length. In particular a
three-edge closing path rules out every four-edge closing path. -/
theorem short_closed_face_prefix_unique (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q q' : G.Walk (p.getVert n) a) (hq : q.IsPath) (hq' : q'.IsPath)
    (hql : 0 < q.length) (hql' : 0 < q'.length)
    (hshort : n+q.length ≤ 6) (hshort' : n+q'.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hInner' : ∀ j, 0 < j → j < q'.length → ¬ OnOuterFace I.embedding I.outer (q'.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (∀ z, z ∈ (spliceFacePath p n q).support ↔ z ∈ (spliceFacePath p n q').support) ∧
      q.length=q'.length := by
  sorry
end BoundaryInstance
end Thomassen

end ShortCycleFacePreservationContracts

section InteriorThreePathUniquenessContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Closing two consecutive old face edges with an interior three-path
determines actual corners on the inner five-face. -/
theorem interior_three_path_facial_corners (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    I.embedding.facePerm (walkArcRoot p hp).symm =
      ⟨(a,y),hya.symm⟩ ∧
    I.embedding.facePerm ⟨(a,y),hya.symm⟩ = ⟨(y,x),hxy.symm⟩ := by
  sorry
/-- The actual face permutation forces both interior vertices to agree.
No uniqueness assumption is imposed on the plane graph. -/
theorem interior_three_path_across_two_face_edges_unique (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y x' y' : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hx' : ¬ OnOuterFace I.embedding I.outer x') (hy' : ¬ OnOuterFace I.embedding I.outer y')
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbx' : G.Adj (p.getVert 2) x') (hxy' : G.Adj x' y') (hya' : G.Adj y' a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : x=x' ∧ y=y' := by
  sorry
/-- The middle old face vertex on the two-edge arc has exactly its two
old cyclic neighbours. This removes all possible further attachments there. -/
theorem middle_vertex_of_interior_three_path_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2 := by
  sorry
end Thomassen.BoundaryInstance

end InteriorThreePathUniquenessContracts

section ResidualShortLeavesContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A connected deletion can expose arbitrarily many short neighbours of
the old prescription. If these neighbours are independent and avoid its two
ends, they can all be fixed as pendant vertices and extended on strictly
smaller actual face pieces. No bound on the number of leaves is required. -/
theorem colourable_of_residual_short_leaves (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {s t : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hrlen : r.length ≤ 4)
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
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end ResidualShortLeavesContracts

section AlternatingFiveFaceObstructionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- If an alternating deletion with at most five prescribed vertices still
fails, the interior three-path exists, is unique, and leaves exactly two
neighbours at the middle free face vertex. All conclusions are derived from
the strict induction hypothesis and the actual old facial cycle. -/
theorem remaining_alternating_counterexample_has_unique_five_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ x y, ¬ OnOuterFace I.embedding I.outer x ∧ ¬ OnOuterFace I.embedding I.outer y ∧
      G.Adj (p.getVert (p.length-1)) x ∧ G.Adj x y ∧ G.Adj y (p.getVert (p.length-3)) ∧
      (∀ x' y', ¬ OnOuterFace I.embedding I.outer x' → ¬ OnOuterFace I.embedding I.outer y' →
        G.Adj (p.getVert (p.length-1)) x' → G.Adj x' y' → G.Adj y' (p.getVert (p.length-3)) →
        x=x' ∧ y=y') ∧
      (∀ z, G.Adj (p.getVert (p.length-2)) z → z=p.getVert (p.length-3) ∨ z=p.getVert (p.length-1)) := by
  sorry
end Thomassen.BoundaryInstance

end AlternatingFiveFaceObstructionContracts

section FiveFaceInteriorAttachmentsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Edges between two interior vertices attached outside the forced five-face
would give either a triangle, a quadrilateral, a second five-face, or a six-face
with the same first reversed old facial edge. All four possibilities are
excluded by girth and preservation of the actual short face orbit. -/
theorem inner_five_face_interior_attachments_independent (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u v2 : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (huA : u ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (hvA : v2 ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (huN : ∃ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj u z)
    (hvN : ∃ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj v2 z) : ¬ G.Adj u v2 := by
  sorry
end Thomassen.BoundaryInstance

end FiveFaceInteriorAttachmentsContracts

section FiveCycleResidualContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The registered five-cycle neighbour lemma applies at every cycle vertex,
by translating its cyclic index. -/
theorem off_five_cycle_neighbours_unique (hg : 5 ≤ G.egirth) {c : ZMod 5 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c)
    {y z : V} (hy : y ∈ Set.range c) (hz : z ∈ Set.range c)
    (hxy : G.Adj x y) (hxz : G.Adj x z) : y=z := by
  sorry
/-- A vertex outside a native five-cycle has at most one neighbour on it.
This bound is independent of the embedding and of the chosen colours. -/
theorem off_native_five_cycle_neighbours_card_le_one {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length=5)
    (x : V) (hx : x ∉ p.support) :
    (p.support.toFinset.filter (G.Adj x)).card ≤ 1 := by
  sorry
/-- Original lists with at least three colours retain at least two after a
coloured native five-cycle has been deleted. -/
theorem residual_native_five_cycle_card_ge_two {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length=5)
    (L : V → Finset C) (f : V → C) (x : V) (hx : x ∉ p.support)
    (hL : 3 ≤ (L x).card) : 2 ≤ (residual G L p.support.toFinset f x).card := by
  sorry
end Thomassen

end FiveCycleResidualContracts

section FiveFaceBoundaryAttachmentsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- An interior vertex attached outside a free five-face cannot also meet
an old free short list or either old prescribed endpoint. Thus the new short
lists can only attach to internal vertices of the retained prescription. -/
theorem inner_five_face_attachment_no_forbidden_boundary_neighbour (I : BoundaryInstance G C)
    {s t a : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
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

end FiveFaceBoundaryAttachmentsContracts

section RemainingAlternatingCaseContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- For a prescription on at most five vertices, every remaining oriented
counterexample has short second and fourth backward lists, together with its
unique interior three-path. No list-pattern or path-existence assumption is
supplied by the caller. -/
theorem remaining_short_prescription_counterexample_alternating (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    3 ≤ r.length ∧ r.length ≤ 4 ∧
      (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧
      (I.lists (p.getVert (p.length-4))).card ≤ 2 ∧
      ∃ x y, ¬ OnOuterFace I.embedding I.outer x ∧ ¬ OnOuterFace I.embedding I.outer y ∧
        G.Adj (p.getVert (p.length-1)) x ∧ G.Adj x y ∧ G.Adj y (p.getVert (p.length-3)) ∧
        (∀ x' y', ¬ OnOuterFace I.embedding I.outer x' → ¬ OnOuterFace I.embedding I.outer y' →
          G.Adj (p.getVert (p.length-1)) x' → G.Adj x' y' → G.Adj y' (p.getVert (p.length-3)) →
          x=x' ∧ y=y') ∧
        (∀ z, G.Adj (p.getVert (p.length-2)) z → z=p.getVert (p.length-3) ∨ z=p.getVert (p.length-1)) := by
  sorry
end Thomassen.BoundaryInstance

end RemainingAlternatingCaseContracts

section FreeFiveFaceDeletionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- All residual-state conditions for a free inner five-face follow from
the proved geometric exclusions. The inputs describe only a concrete proper
colouring of the deleted cycle, preservation of old short lists, and the old
boundary lists adjacent to that cycle. -/
theorem colourable_of_free_inner_five_face_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn5 : r.support.toFinset.card ≤ 5)
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

end FreeFiveFaceDeletionContracts

section FreeFiveFaceColouringContracts

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
theorem colourable_of_free_inner_five_face_short_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn5 : r.support.toFinset.card ≤ 5)
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

end FreeFiveFaceColouringContracts

section FiveVertexPathClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Every remaining alternating case on four or five prescribed vertices
has its unique inner five-face. Rebase at its third free vertex and delete that
face with the explicit compatible colours, keeping the entire old prescription. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_five_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- All nontrivial prescriptions on at most five vertices, for the original
arbitrary face and either orientation, are complete strict induction cases. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_five (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn5 : r.support.toFinset.card ≤ 5)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- All other prescription states are closed: every remaining minimal
counterexample must prescribe exactly six vertices, as a native five-edge path. -/
theorem remaining_counterexample_has_six_prescribed_vertices (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ a t : V, ∃ (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6),
      I.precolor = .path r hr hn ∧ r.length=5 := by
  sorry
end Thomassen.BoundaryInstance

end FiveVertexPathClosureContracts
