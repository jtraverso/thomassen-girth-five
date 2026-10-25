/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Challenge
public import Thomassen.CycleWalk
public import Thomassen.InducedInstance

/-! Public registry contract. Statements are reproduced from the existing
independent main, full-original, corollary and byproduct contracts. No selected
solution proof module is imported. Intentional placeholders occur only here;
the solution supplies and kernel-checks their proof bodies. -/
universe u v
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
def ComponentOuterBoundary (M : PlaneMap G) (B : Set V) : Prop :=
  ∀ K : G.ConnectedComponent, Nonempty K.toSimpleGraph.Dart →
    ∃ outer : K.toSimpleGraph.Dart, ∀ x : K,
      x.1 ∈ B → OnOuterFace (inducedPlaneMap M K.supp) outer x

end Thomassen

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph

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

namespace PlanarChoosability
/-- Thomassen (1995): every finite planar graph of girth at least five is
3-choosable, for lists over an arbitrary colour type. Extended girth includes
forests and edgeless graphs. -/
theorem choosableWith_three_of_isPlanar {V : Type*} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : ChoosableWith G C 3 := by
  sorry

end PlanarChoosability

namespace Thomassen
section
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

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]
theorem original_corollary_2_2 (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length = 5)
    (hface : ∀ x, OnOuterFace M outer x ↔ x ∈ p.support)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  sorry

end
end Thomassen
