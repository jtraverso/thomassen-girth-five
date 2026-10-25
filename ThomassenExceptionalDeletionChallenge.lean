/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ComponentBoundaryDeletion

/-! Independent contracts for the distinguished-endpoint deletion.
None of the four new proof modules is imported. These contracts do not assert
nonexistence of a counterexample with identical two-element endpoint lists. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT

lemma boundary_component_exit_at_vertex (M : PlaneMap G) (outer : G.Dart)
    (x : V) (hx : OnOuterFace M outer x)
    (K : (G.induce ({x} : Set V)ᶜ).ConnectedComponent)
    (hmeet : ∃ z ∈ componentVertexSet ({x} : Set V)ᶜ K, OnOuterFace M outer z) :
    ∃ d : G.Dart, SameCycle M.facePerm outer d ∧
      d.fst ∈ componentVertexSet ({x} : Set V)ᶜ K ∧ d.snd = x := by
  sorry

theorem exists_outer_component_after_boundary_vertex_deletion
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    (x : V) (hx : OnOuterFace M outer x)
    (K : (G.induce ({x} : Set V)ᶜ).ConnectedComponent)
    [Nontrivial (componentVertexSet ({x} : Set V)ᶜ K)] :
    ∃ o : (G.induce (componentVertexSet ({x} : Set V)ᶜ K)).Dart,
      (∀ z : componentVertexSet ({x} : Set V)ᶜ K, OnOuterFace M outer z.1 →
        OnOuterFace (inducedPlaneMap M (componentVertexSet ({x} : Set V)ᶜ K)) o z) ∧
      (∀ z : componentVertexSet ({x} : Set V)ᶜ K, G.Adj z.1 x →
        OnOuterFace (inducedPlaneMap M (componentVertexSet ({x} : Set V)ᶜ K)) o z) := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma no_common_neighbour_of_no_two_path (x : V) (A : Set V)
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    {z : V} (hz : z ∈ A) (hxz : x ≠ z) {w : V}
    (hxw : G.Adj x w) (hwz : G.Adj w z) : False := by
  sorry

lemma exceptional_delete_old_list_unchanged (A : Set V) (x y : V)
    (hxA : x ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (t : C) (hty : t ∉ L y)
    {z : V} (hz : z ∈ A) (hzx : z ≠ x) :
    residual G L {x} (fun _ => t) z = L z := by
  sorry

lemma exceptional_delete_short_lists_independent (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (t : C) {z w : V} (hzx : z ≠ x) (hwx : w ≠ x)
    (hz : (residual G L {x} (fun _ => t) z).card ≤ 2)
    (hw : (residual G L {x} (fun _ => t) w).card ≤ 2) : ¬ G.Adj z w := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT

theorem original_theorem_2_1_exceptional_colour_outside_other_list
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (t : C) (htx : t ∈ L x) (hty : t ∉ L y)
    (haavoid : G.Adj a x → ta ≠ t) (hbavoid : G.Adj b x → tb ≠ t) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

end Thomassen
end

section
namespace Thomassen
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT

theorem original_theorem_2_1_of_long_exceptional_endpoint
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (q : V) (hAind : ∀ z ∈ A, z ≠ q → ∀ w ∈ A, w ≠ q → ¬ G.Adj z w)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card) (hq : 3 ≤ (L q).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem exceptional_counterexample_endpoint_lists_equal_two
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b) (hax : ¬ G.Adj a x) (hbx : ¬ G.Adj b x)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb) :
    (L x).card = 2 ∧ (L y).card = 2 ∧ L x = L y := by
  sorry

end Thomassen
end
