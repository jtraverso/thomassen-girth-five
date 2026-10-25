/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SingleBoundaryComplement

/-! Separate contracts for the complete zero-, one- and two-vertex outer
complement reductions. None of the three new proof modules is imported.
The strict main induction remains explicit; the main theorem is not asserted. -/
@[expose] public section
universe u v

section PendantResidualReductionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A connected boundary deletion is solved when new short-list vertices are
independent, each has at most one old prescribed neighbour, and none attaches
to an endpoint of the old path. Their colours and the complete residual
prescription are constructed internally, with no bound on their number. -/
theorem colourable_of_pendant_residual_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbt : b ≠ t)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (hAP : ∀ x ∈ I.precolor.vertices, x ∉ A)
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (hPcolour : ∀ x ∈ I.precolor.vertices, I.prescribed x ∈ residual G I.lists A f x)
    (hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f x).card)
    (N : Set V)
    (hN : ∀ x, x ∈ N ↔ x ∉ A ∧ x ∉ I.precolor.vertices ∧ (residual G I.lists A f x).card ≤ 2)
    (hNadj : ∀ x ∈ N, ∃ y ∈ A, G.Adj x y)
    (hNind : ∀ x ∈ N, ∀ y ∈ N, ¬ G.Adj x y)
    (hNunique : ∀ x ∈ N, ∀ y ∈ I.precolor.vertices, ∀ z ∈ I.precolor.vertices,
      G.Adj x y → G.Adj x z → y = z)
    (hNends : ∀ x ∈ N, ¬ G.Adj x b ∧ ¬ G.Adj x t)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end PendantResidualReductionContracts

section TwoBoundaryGeometryContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- An external cycle edge can meet a simple path in the cycle graph only at
an endpoint: an internal path vertex already uses its two cycle neighbours. -/
lemma cycle_path_attachment_is_endpoint (hc : IsCycleMap G c) {b t x y : V}
    (r : G.Walk b t) (hr : r.IsPath) (hx : x ∈ r.support) (hy : y ∉ r.support)
    (hrange : ∀ z ∈ r.support, z ∈ Set.range c)
    (hedges : ∀ {z w}, z ∈ r.support → w ∈ r.support → G.Adj z w →
      (cyclicSubgraph G c).Adj z w)
    (hxy : (cyclicSubgraph G c).Adj x y) : x = b ∨ x = t := by
  sorry
/-- An endpoint of an induced path lying on a cycle has a neighbour in the
cycle complement. This applies to either endpoint and any complement size. -/
lemma path_endpoint_has_cycle_complement_neighbour [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {b t : V} (r : G.Walk b t) (hr : r.IsPath)
    (A : Set V) (hcover : ∀ x, x ∈ Set.range c ↔ x ∈ A ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges) :
    ∃ x ∈ A, G.Adj b x := by
  sorry
/-- If two vertices form the entire cycle complement of a path and are not
adjacent, each is adjacent to both path endpoints. -/
lemma cycle_complement_vertex_adjacent_both_path_ends [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (ha : a ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y)
    (had : ¬ G.Adj a d) : G.Adj a b ∧ G.Adj a t := by
  sorry
/-- Exactly two vertices outside a nontrivial prescribed cycle path must be
consecutive in girth at least five. Otherwise the two free vertices and both
path endpoints form a forbidden four-cycle. -/
theorem two_cycle_complement_adjacent [NeZero k] (hg : 5 ≤ G.egirth)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (ha : a ∉ r.support) (hd : d ∉ r.support)
    (had : a ≠ d) (hbt : b ≠ t)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y) : G.Adj a d := by
  sorry
/-- Each end of the complementary cycle edge has exactly one prescribed
neighbour. Extra original-graph edges are checked against the cycle graph. -/
lemma cycle_complement_edge_endpoint_unique_path_neighbour [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V} (r : G.Walk b t)
    (_ha : a ∉ r.support) (hd : d ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (had : (cyclicSubgraph G c).Adj a d)
    (hch : ∀ x ∈ r.support, G.Adj a x → (cyclicSubgraph G c).Adj a x) :
    ∃ z ∈ r.support, G.Adj a z ∧ ∀ x ∈ r.support, G.Adj a x → x = z := by
  sorry
end Thomassen

end TwoBoundaryGeometryContracts

section TwoBoundaryComplementContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The actual facial case with two unprescribed boundary vertices. Their
adjacency, compatible deleted colours and every residual-list condition are
derived. The old prescription may have all six permitted vertices. -/
theorem colourable_of_two_boundary_complement (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (d : V) (hadne : a ≠ d)
    (haP : a ∉ I.precolor.vertices) (hdP : d ∉ I.precolor.vertices)
    (hcover : ∀ x, x ∈ p.support ↔ x = a ∨ x = d ∨ x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The complete strict main-induction case for an arbitrary original face
with exactly two unprescribed vertices. Connectivity, chordlessness, adjacency
of the free pair and facial orientation are not supplied as assumptions. -/
theorem colourable_of_two_unprescribed_outer_vertices (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (x y : V) (hxy : x ≠ y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hcover : ∀ z, OnOuterFace I.embedding I.outer z ↔
      z = x ∨ z = y ∨ z ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- A prescribed native path cannot contain the whole simple outer cycle.
In a smallest counterexample its endpoint must have a neighbour outside that
path. This eliminates the zero-vertex boundary complement as well. -/
theorem colourable_of_all_outer_vertices_in_prescribed_path (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hAll : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- All cases with at most two unprescribed outer vertices are complete.
No placement or cardinality witness for the individual free vertices is needed. -/
theorem colourable_of_at_most_two_unprescribed_outer_vertices (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hcard : (Finset.univ.filter (fun x => OnOuterFace I.embedding I.outer x ∧
      x ∉ I.precolor.vertices)).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- A remaining counterexample with a prescribed path has at least three
free boundary vertices. Its actual native facial cycle is longer than that
path by at least four edges. This is the short-complement normalization used
before selecting the remaining two- and three-path separators. -/
theorem prescribed_path_outer_cycle_length_lower_bound (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hverts : ∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) :
    r.length+4 ≤ p.length := by
  sorry
end Thomassen.BoundaryInstance

end TwoBoundaryComplementContracts
