/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OuterBoundary

/-! PENDING independent target for the entire original Theorem 2.1.
There is currently no matching solution declaration. This intentional challenge
placeholder must not be counted as a proved theorem or included in a passed gate.
-/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Thomassen (1995), Theorem 2.1, both alternatives and all exterior components.
The exceptional endpoint is distinguished: it has no simple length-two path
to any vertex of A. Lists and the two fixed colours are arbitrary. -/
theorem original_theorem_2_1
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (hA : (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) ∨
      ∃ x y, x ∈ A ∧ y ∈ A ∧ G.Adj x y ∧
        (∀ r ∈ A, ∀ s ∈ A, G.Adj r s → (r = x ∧ s = y) ∨ (r = y ∧ s = x)) ∧
        (∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False))
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
