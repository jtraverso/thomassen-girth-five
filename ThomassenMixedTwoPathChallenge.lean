/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedNeighbourUniqueness

/-! Separate contracts for mixed prescribed/free two-path cuts and their
six-vertex exception classification. None of the seven new proof modules
is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section FourEdgePendantGeometryContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- A path of at most four edges with independent pendant attachments has
all simple paths of length at most five if its initial endpoint has no leaves.
Only the remaining path vertices can belong to the branching core. -/
lemma four_edge_path_with_pendant_vertices_paths_short [Fintype V] {a b : V}
    (r : G.Walk a b) (hr : r.IsPath) (hlen : r.length ≤ 4)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges)
    (R : Set V)
    (hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y)
    (hRunique : ∀ x ∈ R, ∀ y ∈ r.support, ∀ z ∈ r.support,
      G.Adj x y → G.Adj x z → y = z)
    (hRstart : ∀ x ∈ R, ¬ G.Adj x a)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath)
    (hsub : ∀ z ∈ q.support, z ∈ {z | z ∈ r.support} ∪ R) : q.length ≤ 5 := by
  sorry
end Thomassen

end FourEdgePendantGeometryContracts

section CompatibleEdgeStarPathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Fix a short induced path whose new vertices lie on one edge. All old
short neighbours are assigned compatible colours and attached as independent
leaves, including leaves at the new terminal endpoint. No capture condition
or bound on the number of these leaves is required. -/
theorem colourable_induced_with_compatible_edge_star_path (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected) {a b : V} (q : G.Walk a b)
    (hq : q.IsPath) (hlen : q.length ≤ 4) (hch : q.IsChordless)
    (hQS : ∀ x ∈ q.support, x ∈ S)
    (hOldP : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (u w : V) (huw : G.Adj u w)
    (hnew : ∀ x ∈ q.support, x ∈ I.precolor.vertices ∨ x = u ∨ x = w)
    (haP : a ∈ I.precolor.vertices)
    (f : V → C) (hf : ∀ x ∈ q.support, f x ∈ I.lists x)
    (hproper : ∀ x ∈ q.support, ∀ y ∈ q.support, G.Adj x y → f x ≠ f y)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace M o x)
    (hOldFace : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → OnOuterFace M o x)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ q.support → c x = f x.1 := by
  sorry
end Thomassen.BoundaryInstance

end CompatibleEdgeStarPathContracts

section InteriorBoundaryNeighboursContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- In the forward native facial order, an interior vertex has at most one
unprescribed boundary neighbour. The complementary arc is rebased at the
terminal prescribed vertex; the proved free-arc reduction applies to it. -/
theorem interior_unprescribed_neighbour_unique_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x = y := by
  sorry
/-- The unprescribed-neighbour uniqueness is independent of the original
face representative and of the direction of the prescribed path. -/
theorem interior_unprescribed_neighbour_unique (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x = y := by
  sorry
/-- Every three boundary neighbours of an interior vertex contain a repeated
vertex. Both prescribed and unprescribed neighbours are bounded separately,
so there are at most two boundary neighbours in total. -/
theorem interior_at_most_two_boundary_neighbours (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y z : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hz : OnOuterFace I.embedding I.outer z)
    (hux : G.Adj u x) (huy : G.Adj u y) (huz : G.Adj u z) :
    x=y ∨ x=z ∨ y=z := by
  sorry
end Thomassen.BoundaryInstance

end InteriorBoundaryNeighboursContracts

section RetainedPrescriptionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Retain a connected part of the old prescription on a proper piece with
its actual exposed face. The original lists are unchanged, and the six-vertex
bound is inherited by every simple path in the retained prescribed set. -/
theorem colourable_induced_retaining_connected_prescription (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected)
    (hPconn : ConnSet G {x | x ∈ I.precolor.vertices ∧ x ∈ S})
    (hOldFace : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → OnOuterFace M o x)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable (G.induce S) (fun x => I.lists x.1) := by
  sorry
end Thomassen.BoundaryInstance

end RetainedPrescriptionContracts

section MixedPrescribedTwoPathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A mixed interior two-path is eliminated when its prescribed endpoint
leaves at most three old prescribed vertices on the initial side, and the
unprescribed endpoint is not adjacent to the initial prescribed vertex.
Both actual pieces, their faces and every short-list attachment are derived. -/
theorem colourable_of_mixed_two_path_short_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (i j : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (hrj : r.length < j) (hjp : j < p.length)
    (hba : ¬ G.Adj a (p.getVert j))
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert i)) (huj : G.Adj u (p.getVert j))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The short-prefix mixed reduction applies to the arbitrary original face
in either orientation. Native facial placement of the unprescribed endpoint
is recovered internally. -/
theorem colourable_of_mixed_two_path_short_prefix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hba : ¬ G.Adj a b) (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert i)) (hub : G.Adj u b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The same mixed reduction is available at the terminal end of the old
prescription. Reversal preserves every old list, edge and singleton colour. -/
theorem colourable_of_mixed_two_path_short_suffix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbt : ¬ G.Adj t b) (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert (r.length-i))) (hub : G.Adj u b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end MixedPrescribedTwoPathContracts

section MixedTwoPathExceptionsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- On the normalized native face a free boundary vertex cannot adjoin both
prescribed ends: that would leave a single free vertex, a case already closed. -/
theorem free_boundary_not_adjacent_both_prescribed_ends_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hab : G.Adj a b) (htb : G.Adj t b) : False := by
  sorry
/-- The two prescribed ends cannot share a free boundary neighbour, for the
original arbitrary embedding and either direction of the prescribed path. -/
theorem free_boundary_not_adjacent_both_prescribed_ends (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hab : G.Adj a b) (htb : G.Adj t b) : False := by
  sorry
/-- Every remaining two-path with one internal prescribed endpoint and one
free boundary endpoint has one of the two published six-vertex exceptions.
All other mixed configurations are complete strict-induction cases. -/
theorem mixed_interior_two_path_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (i : ℕ) (hi : 0 < i) (hir : i < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hui : G.Adj u (r.getVert i)) (hub : G.Adj u b) :
    r.length=5 ∧ ((i=2 ∧ G.Adj a b) ∨ (i=3 ∧ G.Adj t b)) := by
  sorry
end Thomassen.BoundaryInstance

end MixedTwoPathExceptionsContracts

section MixedTwoPathClassificationContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The initial-endpoint two-path exclusion holds for the original arbitrary
face and either prescribed-path orientation. -/
theorem no_interior_boundary_pair_at_initial_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a) (hua : G.Adj u a) (huy : G.Adj u y) : False := by
  sorry
/-- The terminal-endpoint exclusion is obtained by reversing the actual native
prescription. Its vertices, edges, lists and all instance invariants are kept. -/
theorem no_interior_boundary_pair_at_terminal_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : OnOuterFace I.embedding I.outer y) (hyt : y ≠ t) (hut : G.Adj u t) (huy : G.Adj u y) : False := by
  sorry
/-- Without any facial orientation or index supplied, the only mixed
prescribed/free pair of boundary neighbours in a counterexample is one of
the two exceptional configurations for six prescribed vertices. -/
theorem interior_prescribed_and_free_neighbours_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hux : G.Adj u x) (hub : G.Adj u b) :
    r.length=5 ∧ ((x=r.getVert 2 ∧ G.Adj a b) ∨ (x=r.getVert 3 ∧ G.Adj t b)) := by
  sorry
/-- With two to five old prescribed vertices, every mixed interior two-path
is a complete strict-induction case. The six-vertex exceptions are impossible. -/
theorem colourable_of_mixed_two_path_with_at_most_five_prescribed_vertices (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (u x b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hux : G.Adj u x) (hub : G.Adj u b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end MixedTwoPathClassificationContracts
