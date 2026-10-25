/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ThreeVertexPathClosure

/-! Separate contracts for current-cardinality small stars, empty and singleton
prescriptions, and the residual four-to-six-vertex classification. None of
the four new proof modules is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section CurrentSmallStarContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A nontrivial root star on at most three vertices extends at the current
vertex cardinality by the proved small-prescription case. Its own calls to
the main induction remain strictly smaller. -/
theorem rootStar_extension_of_nontrivial_small_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hqlen : q.length ≤ 2) (hqpos : 0 < q.length) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ rootStar I v)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : RootStarExtension I v f := by
  sorry
/-- When all short neighbours of the root are among two distinct neighbours,
the full star is a native path of at most three vertices. -/
theorem rootStar_extension_of_two_neighbours_current (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (l r : V) (hl : G.Adj v l) (hr : G.Adj v r) (hlr : l ≠ r)
    (hbound : ∀ z, G.Adj v z → (I.lists z).card ≤ 2 → z = l ∨ z = r)
    (hHasShort : ∃ z, G.Adj v z ∧ (I.lists z).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : RootStarExtension I v f := by
  sorry
end Thomassen.BoundaryInstance

end CurrentSmallStarContracts

section EmptyPrescriptionClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- With a short list present, choose its preceding facial neighbour as root.
Chordlessness puts every old short root neighbour among the two cycle neighbours,
so the proved nontrivial small-star extension closes the current instance. -/
theorem colourable_of_empty_prescription_with_short_list (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hshort : ∃ y, (I.lists y).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The full empty-prescription induction case. If all lists have at least
three colours, thin one actual boundary list to two and use the previous case.
The thinned instance retains the same graph, face and strict main induction. -/
theorem colourable_of_empty_prescription (I : BoundaryInstance G C)
    (hP : I.precolor = .empty)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end EmptyPrescriptionClosureContracts

section SingletonPrescriptionClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The singleton-prescription case, including arbitrary original faces.
Expand its singleton list by an allowed colour at a facial neighbour, then
fix that neighbour to the added colour. Properness forces the original
singleton colour. The auxiliary root star has at most three vertices. -/
theorem colourable_of_singleton_prescription (I : BoundaryInstance G C)
    (a : V) (hP : ∀ x, x ∈ I.precolor.vertices ↔ x=a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SingletonPrescriptionClosureContracts

section LongPrescriptionReductionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Empty prescriptions, singleton prescriptions, edges, three-vertex paths
and all permitted cycles are complete strict-induction cases. Thus a remaining
counterexample must prescribe a native path on four to six vertices. -/
theorem remaining_counterexample_has_four_to_six_prescribed_vertices (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ a t : V, ∃ (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6),
      I.precolor = .path r hr hn ∧ 3 ≤ r.length ∧ r.length ≤ 5 := by
  sorry
end Thomassen.BoundaryInstance

end LongPrescriptionReductionContracts
