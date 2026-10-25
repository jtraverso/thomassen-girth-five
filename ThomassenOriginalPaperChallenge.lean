/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedInstance
public import Thomassen.ConnectedPrescription

/-! Independent contracts for the proved original-paper corollary and
partial Theorem 2.1 results. No new proof module is imported.
The full exceptional alternative is a separate PENDING target in
ThomassenOriginalFullChallenge; it is not asserted by this passed gate. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

namespace Thomassen
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

def ComponentOuterBoundary (M : PlaneMap G) (B : Set V) : Prop :=
  ∀ K : G.ConnectedComponent, Nonempty K.toSimpleGraph.Dart →
    ∃ outer : K.toSimpleGraph.Dart, ∀ x : K,
      x.1 ∈ B → OnOuterFace (inducedPlaneMap M K.supp) outer x

end Thomassen

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem extend_outer_short_cycle (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

theorem original_corollary_2_2 (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length = 5)
    (hface : ∀ x, OnOuterFace M outer x ↔ x ∈ p.support)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

end Thomassen
end

section
namespace Thomassen.BoundaryInstance
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem extend_edge_of_preconnected (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem extend_edge (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen.BoundaryInstance
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem original_theorem_2_1_independent (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (A : Set V)
    (hAface : ∀ x ∈ A, OnOuterFace M outer x)
    (hAind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem extend_edge_of_independent_away_from_fixed_endpoint
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ x ∈ A, OnOuterFace M outer x)
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hAind : ∀ x ∈ A, x ≠ a → ∀ y ∈ A, y ≠ a → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem original_theorem_2_1_exceptional_incident
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ x ∈ A, OnOuterFace M outer x)
    (x y : V) (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hinc : x = a ∨ y = a ∨ x = b ∨ y = b) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
end

section
namespace Thomassen.ConnectedPrescription
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem colourable (I : ConnectedPrescription G C) : ListColourable G I.lists := by
  sorry

end Thomassen.ConnectedPrescription
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem extend_small_colour_core (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (L : V → Finset C)
    (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (B : Finset V) (hB : B.card ≤ 4) (hconn : ConnSet G (↑B : Set V))
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hedges : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∧ y ∈ B)
    (hunique : ∀ x, x ∉ B → (L x).card ≤ 2 → ∀ y ∈ B, ∀ z ∈ B,
      G.Adj x y → G.Adj x z → y = z)
    (f : V → C) (hf : ∀ x ∈ B, f x ∈ L x)
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ B, c x = f x := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem original_theorem_2_1_exceptional_adjacent
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hbx : G.Adj b x) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

theorem original_theorem_2_1_independent_global
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (hAind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
end
