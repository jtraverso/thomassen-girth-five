/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Thomassen.OuterBoundary

/-! Independent contracts for requested byproducts 1–4. None of the five new
proof modules or the Rado compactness proof is imported. The unresolved full
original Theorem 2.1 is not asserted by this challenge. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [Finite V]

theorem colourable_connected_boundary_set_six
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (B : Finset V) (hB : B.card ≤ 6) (hconn : ConnSet G (↑B : Set V))
    (L : V → Finset C) (f : V → C)
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hsingle : ∀ x ∈ B, L x = {f x})
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x, OnOuterFace M outer x → x ∉ B → 2 ≤ (L x).card)
    (hinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (hshort : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∧ y ∈ B) :
    ListColourable G L := by
  sorry

theorem dvorak_kawarabayashi_theorem_1
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ 5)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (f : V → C)
    (hsingle : ∀ x ∈ p.support, L x = {f x})
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x, OnOuterFace M outer x → x ∉ p.support → 2 ≤ (L x).card)
    (hinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (hshort : ∀ x, (L x).card = 2 → ∀ y, (L y).card ≤ 2 → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT

theorem dvorak_kawarabayashi_theorem_1_global
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ 5)
    (hPB : ∀ x ∈ p.support, x ∈ B)
    (L : V → Finset C) (f : V → C)
    (hsingle : ∀ x ∈ p.support, L x = {f x})
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x ∈ B, x ∉ p.support → 2 ≤ (L x).card)
    (hinterior : ∀ x, x ∉ B → 3 ≤ (L x).card)
    (hshort : ∀ x, (L x).card = 2 → ∀ y, (L y).card ≤ 2 → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

theorem listColourable_of_finite_induced
    (L : V → Finset C)
    (hfinite : ∀ S : Finset V, ListColourable (G.induce (↑S : Set V)) (fun x => L x.1)) :
    ListColourable G L := by
  sorry

theorem infinite_three_list_colourable
    (hplanar : ∀ S : Finset V, IsPlanar (G.induce (↑S : Set V)))
    (hgirth : ∀ S : Finset V, 5 ≤ (G.induce (↑S : Set V)).egirth)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card) : ListColourable G L := by
  sorry

theorem infinite_three_list_colourable_of_egirth
    (hplanar : ∀ S : Finset V, IsPlanar (G.induce (↑S : Set V)))
    (hgirth : 5 ≤ G.egirth)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card) : ListColourable G L := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [Finite V]

theorem extend_short_cycle_of_preconnected (M : PlaneMap G) (hG : G.Preconnected)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 6)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

theorem extend_any_short_cycle (M : PlaneMap G) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 6)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable {k : ℕ} {c : ZMod k → V}

lemma cycle_isChordless_of_length_le_seven [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hsmall : k ≤ 7) : IsChordless G c := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma seven_cycle_exists_distinct_neighbour_colours (d : ZMod 7 → C)
    (hproper : ∀ i, d i ≠ d (i+1)) : ∃ j, d (j-1) ≠ d (j+1) := by
  sorry

theorem extend_outer_seven_cycle_map [Finite V] {n : ℕ} (hn : n = 7)
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (d : ZMod n → V) (hd : IsCycleMap G d)
    (hface : ∀ i, OnOuterFace M outer (d i))
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ i, f (d i) ∈ L (d i))
    (hproper : ∀ i, f (d i) ≠ f (d (i+1))) :
    ∃ col : G.Coloring C, (∀ x, col x ∈ L x) ∧ ∀ i, col (d i) = f (d i) := by
  sorry

theorem extend_outer_seven_cycle [Finite V]
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 7)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ col : G.Coloring C, (∀ x, col x ∈ L x) ∧ ∀ x ∈ p.support, col x = f x := by
  sorry

end Thomassen
end
