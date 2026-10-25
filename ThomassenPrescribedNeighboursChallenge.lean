/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.TwoBoundaryComplement

/-! Separate contracts for compatible short-path stars, oriented native
face normalization, the central six-vertex two-path and uniqueness of an
interior prescribed neighbour. None of the four new proof modules is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section CompatiblePathStarContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Prescribe a short induced path on a strictly smaller piece, retaining all
old singleton vertices and fixing one new internal vertex. All its old short
neighbours are coloured independently and attached as leaves. Their number is
unbounded; the proved connected-prescription induction supplies extension. -/
theorem colourable_induced_with_compatible_path_star (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected) {a b : V} (q : G.Walk a b)
    (hq : q.IsPath) (hlen : q.length ≤ 5) (hch : q.IsChordless)
    (hQS : ∀ x ∈ q.support, x ∈ S)
    (hOldP : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (u : V) (huq : u ∈ q.support)
    (hnew : ∀ x ∈ q.support, x ∈ I.precolor.vertices ∨ x = u)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∈ I.precolor.vertices) (hab : a ≠ b)
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

end CompatiblePathStarContracts

section OrientedPrescriptionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A minimal counterexample admits an actual native facial cycle rooted at
the initial prescribed vertex and traversing the prescription forward, either
in its original embedding or in the proved mirror embedding. Every original
list and prescribed colour is retained. -/
theorem exists_oriented_native_face_for_prescribed_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧
      ((∃ q : G.Walk a a, ∃ hq : q.IsCycle,
        IsFacialCycleAlong I.embedding (walk_isCycleMap q hq) Set.univ ∧
        SameCycle I.embedding.facePerm I.outer (walkArcRoot q hq) ∧
        ∀ i ≤ r.length, r.getVert i = q.getVert i) ∨
      (∃ q : G.Walk a a, ∃ hq : q.IsCycle,
        IsFacialCycleAlong I.mirror.embedding (walk_isCycleMap q hq) Set.univ ∧
        SameCycle I.mirror.embedding.facePerm I.mirror.outer (walkArcRoot q hq) ∧
        ∀ i ≤ r.length, r.getVert i = q.getVert i)) := by
  sorry
end Thomassen.BoundaryInstance

end OrientedPrescriptionContracts

section CentralPrescribedTwoPathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The central remaining two-path with both ends internal to a six-vertex
prescription. The five-cycle on positions 1--4 is coloured compatibly with the
exterior five-vertex path. Old short neighbours of the new interior vertex are
handled by the proved branching-prescription extension. -/
theorem colourable_of_central_prescribed_two_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 5)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hu1 : G.Adj u (r.getVert 1)) (hu4 : G.Adj u (r.getVert 4))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The central six-vertex two-path is a complete main-induction case for the
original arbitrary embedding. A native facial placement and its orientation
are derived internally, using the verified mirror operation when necessary. -/
theorem colourable_of_central_prescribed_two_path_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 5)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hu1 : G.Adj u (r.getVert 1)) (hu4 : G.Adj u (r.getVert 4))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end CentralPrescribedTwoPathContracts

section PrescribedNeighbourUniquenessContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Neighbours of a vertex outside a simple path in girth five are separated
by at least three edges on that path. -/
lemma path_neighbour_indices_gap (hg : 5 ≤ G.egirth) {a t u : V}
    (r : G.Walk a t) (hr : r.IsPath) (hu : u ∉ r.support) (i j : ℕ)
    (hij : i < j) (hj : j ≤ r.length) (hui : G.Adj u (r.getVert i)) (huj : G.Adj u (r.getVert j)) :
    i+3 ≤ j := by
  sorry
namespace BoundaryInstance
variable [instFT : Fintype V]
include instFT

/-- The initial-endpoint two-path exclusion holds for the original arbitrary
face and either prescribed-path orientation. -/
theorem no_interior_prescribed_pair_at_initial_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : y ∈ I.precolor.vertices) (hya : y ≠ a) (hua : G.Adj u a) (huy : G.Adj u y) : False := by
  sorry
/-- The terminal-endpoint exclusion is obtained by reversing the actual native
prescription. Its vertices, edges, lists and all instance invariants are kept. -/
theorem no_interior_prescribed_pair_at_terminal_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : y ∈ I.precolor.vertices) (hyt : y ≠ t) (hut : G.Adj u t) (huy : G.Adj u y) : False := by
  sorry
/-- In a minimal counterexample no interior vertex has two distinct old
prescribed neighbours. Endpoint cases, all girth obstructions and the sole
central six-vertex configuration are resolved, for arbitrary original faces. -/
theorem interior_prescribed_neighbour_unique (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices) (hy : y ∈ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x=y := by
  sorry
end BoundaryInstance
end Thomassen

end PrescribedNeighbourUniquenessContracts
