/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorTwoPathReduction

/-! Independent contracts for exact endpoint deletion and residual-list
restoration. The proof module is not imported. Geometric exclusions in the
main deletion case remain explicit; the unconditional theorem remains open. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a t : V}

/-- Deleting the first vertex of a native prescribed path gives the exact
remaining native path, or the empty prescription for an original singleton. -/
lemma exists_prescription_after_initial_deletion (p : G.Walk a t) (hp : p.IsPath)
    (hn : p.support.toFinset.card ≤ 6) :
    ∃ Q : BoundaryPrecolor (G.induce ({a} : Set V)ᶜ),
      (∀ x : ↥(({a} : Set V)ᶜ), x ∈ Q.vertices ↔ x.1 ∈ p.support) ∧
      (∀ x y : ↥(({a} : Set V)ᶜ), s(x,y) ∈ Q.edges ↔ s(x.1,y.1) ∈ p.edges) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Delete and restore an original prescribed endpoint when its newly short
neighbours have no remaining prescribed neighbour and no old short-list
neighbour. Original two-lists remain unchanged; new two-lists are independent
by girth. Disconnection at the deleted vertex uses the completed cutvertex case. -/
theorem colourable_of_prescribed_endpoint_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hNoShared : ∀ x, x ∉ p.support → G.Adj a x → ∀ y ∈ p.support, y ≠ a → ¬ G.Adj x y)
    (hNoOldShort : ∀ x, x ∉ p.support → G.Adj a x → ∀ y, y ∉ p.support →
      (I.lists y).card ≤ 2 → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- For a prescribed path of at most three vertices, girth itself rules out
new two-lists adjacent to the remaining prescription. Only old-short-list
conflicts have to be excluded. -/
theorem colourable_of_short_prescribed_endpoint_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 2)
    (hNoOldShort : ∀ x, x ∉ p.support → G.Adj a x → ∀ y, y ∉ p.support →
      (I.lists y).card ≤ 2 → ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The entire case with a short prescribed path and three-lists everywhere
else is closed by the strict main induction, without extra geometric inputs. -/
theorem colourable_of_short_prescription_and_three_lists (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 2)
    (hthree : ∀ x, x ∉ p.support → 3 ≤ (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The endpoint-deletion reduction supplies explicit geometric obstruction
witnesses in a smallest counterexample; absence of those witnesses is not
assumed silently in the final induction. -/
lemma endpoint_deletion_obstruction_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (∃ x, x ∉ p.support ∧ G.Adj a x ∧ ∃ y ∈ p.support, y ≠ a ∧ G.Adj x y) ∨
      (∃ x, x ∉ p.support ∧ G.Adj a x ∧ ∃ y, y ∉ p.support ∧ (I.lists y).card ≤ 2 ∧ G.Adj x y) := by
  sorry

end BoundaryInstance
end Thomassen
