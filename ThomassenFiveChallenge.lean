/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Thomassen.ThreeVertexDeletion
public import Thomassen.CutPrecolor
public import Thomassen.FaceBoundary
public import LeanPool.K5MinorFreeChoosability.Planar.FaceApex

/-! Independent contracts over previously checked prerequisites.
None of FiveCycle, FacialFiveReduction or FacialSixReduction is imported.
Smaller-cardinality induction remains explicit; the full six-cycle contract
has no opposite-neighbour restriction. -/

@[expose] public section
section FiveCycleContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- A vertex off a five-cycle cannot be adjacent to two cycle vertices. -/
lemma off_five_cycle_unique_neighbour (hg : 5 ≤ G.egirth) {c : ZMod 5 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c) (hax : G.Adj (c 0) x)
    {y : V} (hy : y ∈ Set.range c) (hya : y ≠ c 0) : ¬ G.Adj x y := by
  sorry

lemma off_native_five_cycle_unique_neighbour {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 5)
    {x : V} (hx : x ∉ p.support) (hax : G.Adj a x)
    {y : V} (hy : y ∈ p.support) (hya : y ≠ a) : ¬ G.Adj x y := by
  sorry

/-- On a six-cycle, a second neighbour of an exterior neighbour of the root
can only be the opposite vertex. -/
lemma off_six_cycle_second_neighbour (hg : 5 ≤ G.egirth) {c : ZMod 6 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c) (hax : G.Adj (c 0) x)
    {y : V} (hy : y ∈ Set.range c) (hya : y ≠ c 0) (hxy : G.Adj x y) : y = c 3 := by
  sorry

lemma off_native_six_cycle_second_neighbour {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    {x : V} (hx : x ∉ p.support) (hax : G.Adj a x)
    {y : V} (hy : y ∈ p.support) (hya : y ≠ a) (hxy : G.Adj x y) :
    y = p.getVert 3 := by
  sorry

lemma cycle_tail_dropLast_support {a : V} (p : G.Walk a a) (hp : p.IsCycle) (x : V) :
    x ∈ p.tail.dropLast.support ↔ x ∈ p.support ∧ x ≠ a := by
  sorry

lemma cycle_tail_dropLast_edges {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    {x y : V} (hx : x ≠ a) (hy : y ≠ a) :
    s(x, y) ∈ p.tail.dropLast.edges ↔ s(x, y) ∈ p.edges := by
  sorry

variable [Fintype V]

/-- Deleting a boundary vertex exposes its neighbours on the projected face. -/
lemma exists_outer_after_boundary_vertex (M : PlaneMap G) (outer : G.Dart) (a : V)
    [Nontrivial (({a} : Set V)ᶜ : Set V)] (ha : OnOuterFace M outer a)
    (hconn : (G.induce ({a} : Set V)ᶜ).Preconnected) :
    ∃ o : (G.induce ({a} : Set V)ᶜ).Dart,
      (∀ x : (({a} : Set V)ᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M ({a} : Set V)ᶜ) o x) ∧
      (∀ x : (({a} : Set V)ᶜ : Set V), G.Adj x.1 a →
        OnOuterFace (inducedPlaneMap M ({a} : Set V)ᶜ) o x) := by
  sorry

end Thomassen

end FiveCycleContracts

section FacialFiveReductionContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- Delete and restore one vertex of a prescribed facial cycle of at most six
vertices, when its new two-lists have no neighbour in the remaining prescription.
The cutvertex alternative uses the already verified reduction. -/
theorem colourable_of_facial_cycle_without_shared_neighbours (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hNoShared : ∀ x, x ∉ p.support → G.Adj a x → ∀ y ∈ p.support, y ≠ a → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The full five-cycle case: girth excludes the shared-neighbour obstruction. -/
theorem colourable_of_facial_five_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 5)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The facial six-cycle case without an exterior common neighbour of a
pair of opposite cycle vertices. The remaining exceptional configuration is
kept explicit rather than treated as an extension hypothesis. -/
theorem colourable_of_facial_six_cycle_without_opposite_neighbour
    (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hNoOpposite : ∀ x, x ∉ p.support → ¬ (G.Adj a x ∧ G.Adj x (p.getVert 3)))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end FacialFiveReductionContracts

section FacialSixContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Four pairwise adjacent disjoint connected bags meeting a minor-free
boundary would give a fifth bag at its apex. -/
lemma not_isK5Boundary_of_rooted_four_bags (B : Set V) (X : Fin 4 → Finset V)
    (hconn : ∀ i, ConnSet G ↑(X i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hadj : ∀ i j, i ≠ j → ∃ a ∈ X i, ∃ b ∈ X j, G.Adj a b)
    (hroot : ∀ i, ∃ a ∈ X i, a ∈ B) : ¬ IsK5Boundary G B := by
  sorry

/-- Two consecutive pairs of opposite vertices of a six-cycle cannot both
have exterior common neighbours in a minor-free boundary. -/
lemma six_cycle_no_consecutive_opposite_neighbours (hg : 5 ≤ G.egirth)
    {c : ZMod 6 → V} (hc : IsCycleMap G c) (hB : IsK5Boundary G (Set.range c))
    {x y : V} (hx : x ∉ Set.range c) (hy : y ∉ Set.range c)
    (h0x : G.Adj (c 0) x) (hx3 : G.Adj x (c 3))
    (h1y : G.Adj (c 1) y) (hy4 : G.Adj y (c 4)) : False := by
  sorry

/-- It suffices that deletion preserves connectivity at vertices of the chosen
face: the registered apex construction then gives its minor-free boundary. -/
lemma isK5Boundary_of_face_deletions [Finite V] (M : PlaneMap G) (outer : G.Dart)
    (hconn : ∀ v, OnOuterFace M outer v → (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsK5Boundary G {v | OnOuterFace M outer v} := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The complete prescribed facial six-cycle reduction. If an opposite pair has
an exterior common neighbour, the rooted four-bag obstruction permits deleting
the next cycle vertex instead. All changed-list conditions use the already
proved facial deletion reduction. -/
theorem colourable_of_facial_six_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every prescribed facial cycle allowed by the six-vertex invariant is now
covered. Girth leaves only the five- and six-cycle cases. -/
theorem colourable_of_facial_short_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance

end Thomassen

end FacialSixContracts
