/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CutPrecolor
public import Thomassen.CycleSeparation

/-! Independent interior-cut contracts over previously checked cutvertex,
face connectivity and induced-instance prerequisites. InteriorCutReduction is
not imported. The cardinality restriction on the induction remains explicit. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Reachability avoiding a cutvertex preserves membership in either cut side. -/
lemma rIn_side_of_avoids_cut
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (hr : RIn G ({v} : Set V)ᶜ a b) : (a ∈ S ↔ b ∈ S) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Colour a cut side disjoint from the original selected face after colouring
the other side. Its original lists are all three-lists, so prescribing the cut
vertex leaves an admissible singleton path on any incident induced face. -/
theorem colourable_of_interior_cut_piece (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (v : V) (S : Set V) (hv : v ∈ S)
    (hleft : ∃ a ∈ S, a ≠ v) (hright : ∃ b, b ∉ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    (hNoFace : ∀ x ∈ S, ¬ OnOuterFace I.embedding I.outer x)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every cutvertex outside the selected face is eliminated by strict boundary
extension induction, without an extra assumption on its prescribed status. -/
theorem colourable_of_interior_cutvertex (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (v : V) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- In a smallest counterexample, every remaining cutvertex must lie on the
selected face and outside the prescription. This isolates the boundary fan
case without assuming two-connectivity. -/
lemma cutvertex_constraints (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (v : V) (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected) :
    OnOuterFace I.embedding I.outer v ∧ v ∉ I.precolor.vertices := by
  sorry

end BoundaryInstance
end Thomassen
