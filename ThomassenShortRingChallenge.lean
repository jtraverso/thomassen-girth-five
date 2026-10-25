/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk

/-! Independent short-ring gluing contracts. No new byproduct proof module is
imported. An exterior colouring is explicitly required by the gluing operation;
the full original Theorem 2.1 is not asserted. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

theorem transfer_extension_to_prescribed_lists (P : Set V) (L : V → Finset C) (f : V → C)
    (hf : ∀ x ∈ P, f x ∈ L x)
    (hproper : ∀ x ∈ P, ∀ y ∈ P, G.Adj x y → f x ≠ f y)
    (hL : ∀ x, x ∉ P → 3 ≤ (L x).card)
    (hext : ∀ L' : V → Finset C, (∀ x, 3 ≤ (L' x).card) →
      (∀ x ∈ P, f x ∈ L' x) →
      ∃ c : G.Coloring C, (∀ x, c x ∈ L' x) ∧ ∀ x ∈ P, c x = f x) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ P, c x = f x := by
  sorry

theorem extend_outer_ring_of_interior_three_lists [Finite V]
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 7)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, x ∉ p.support → 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

theorem extend_exterior_across_short_ring [Fintype V]
    (S T : Set V) (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 7)
    (hinter : S ∩ T = {x | x ∈ p.support})
    (M : PlaneMap (G.induce T)) (outer : (G.induce T).Dart)
    (hface : ∀ x : T, x.1 ∈ p.support → OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x : T, x.1 ∉ p.support → 3 ≤ (L x.1).card)
    (cS : (G.induce S).Coloring C) (hcS : ∀ x : S, cS x ∈ L x.1) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x : S, c x.1 = cS x := by
  sorry

end Thomassen
