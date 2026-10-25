module
public import Thomassen.ConnectedPrescription
public import Thomassen.OuterBoundary

/-! Independent contracts for additional exceptional-edge reductions.
None asserts the unresolved full original Theorem 2.1. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem extend_small_colour_core_of_short_edges_covered (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (L : V → Finset C)
    (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (B : Finset V) (hB : B.card ≤ 4) (hconn : ConnSet G (↑B : Set V))
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hedges : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∨ y ∈ B)
    (hunique : ∀ x, x ∉ B → (L x).card ≤ 2 → ∀ y ∈ B, ∀ z ∈ B,
      G.Adj x y → G.Adj x z → y = z)
    (f : V → C) (hf : ∀ x ∈ B, f x ∈ L x)
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ B, c x = f x := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

theorem original_theorem_2_1_exceptional_joined
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
    (hjoin : G.Adj a x ∨ G.Adj b x ∨ G.Adj a y ∨ G.Adj b y) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem original_theorem_2_1_exceptional_boundary_bridge
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ t ∈ A, OnOuterFace M outer t)
    (x y : V) (hxA : x ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ t, 2 ≤ (L t).card)
    (hLthree : ∀ t, t ∉ A → 3 ≤ (L t).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hay : ¬ G.Adj a y) (hby : ¬ G.Adj b y)
    (hax : ¬ G.Adj a x)
    (z : V) (hz : OnOuterFace M outer z) (hbz : G.Adj b z) (hzx : G.Adj z x) :
    ∃ c : G.Coloring C, (∀ t, c t ∈ L t) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem exceptional_counterexample_no_short_outer_bridge
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb) :
    x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      ¬ G.Adj a x ∧ ¬ G.Adj b x ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y ∧
      (L x).card = 2 ∧ (L y).card = 2 ∧ L x = L y ∧
      (∀ z, OnOuterFace M outer z →
        ¬ (G.Adj a z ∧ G.Adj z x) ∧ ¬ (G.Adj b z ∧ G.Adj z x) ∧
        ¬ (G.Adj a z ∧ G.Adj z y) ∧ ¬ (G.Adj b z ∧ G.Adj z y)) := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem listColourable_of_one_short_edge_on_face
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card) : ListColourable G L := by
  sorry

theorem assemble_fixed_component_with_one_short_edge
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ta tb : C)
    (K : G.ConnectedComponent) (haK : a ∈ K.supp)
    (cK : K.toSimpleGraph.Coloring C) (hcK : ∀ z : K, cK z ∈ L z.1)
    (hca : ∀ z : K, z.1 = a → cK z = ta)
    (hcb : ∀ z : K, z.1 = b → cK z = tb) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  sorry

theorem exceptional_counterexample_fixed_component
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb)
    (K : G.ConnectedComponent) (haK : a ∈ K.supp) :
    ∃ (_hxK : x ∈ K.supp) (_hyK : y ∈ K.supp) (hbK : b ∈ K.supp),
      ∃ outer : K.toSimpleGraph.Dart,
        (∀ z : K, z.1 ∈ B → OnOuterFace (inducedPlaneMap M K.supp) outer z) ∧
        ¬ ∃ c : K.toSimpleGraph.Coloring C, (∀ z : K, c z ∈ L z.1) ∧
          c ⟨a,haK⟩ = ta ∧ c ⟨b,hbK⟩ = tb := by
  sorry

theorem exceptional_global_counterexample_normal_form
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb) :
    G.Reachable a x ∧ G.Reachable a y ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      ¬ G.Adj a x ∧ ¬ G.Adj b x ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y ∧
      (L x).card = 2 ∧ (L y).card = 2 ∧ L x = L y := by
  sorry

end

end Thomassen
