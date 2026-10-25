/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ExceptionalDistinctLists

/-! Isolate identical two-colour endpoint lists in the separated exceptional case. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- If removing one vertex makes the old two-list set independent and that
vertex actually has at least three colours, the independent-set alternative
already applies. The old set A need not be a minimal description of short lists. -/
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
  apply original_theorem_2_1_independent M outer hg (A \ {q})
    (fun z hz => hAface z hz.1)
    (fun z hz w hw => hAind z hz.1 (by simpa using hz.2) w hw.1 (by simpa using hw.2))
    L hLtwo ?_ a b hab ha hb ta tb hta htb htab
  intro z hz
  by_cases heq : z = q
  · subst z; exact hq
  · exact hLthree z (fun h => hz ⟨h,by simpa only [Set.mem_singleton_iff] using heq⟩)

/-- Any remaining counterexample with the distinguished endpoint separated
from the prescribed edge must have exactly the same two-element list at both
exceptional endpoints. This is a proved necessary condition, not a proof that
such a counterexample cannot exist. -/
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
  have haway (q : V) (hq : x = q ∨ y = q) :
      ∀ z ∈ A, z ≠ q → ∀ w ∈ A, w ≠ q → ¬ G.Adj z w := by
    intro z hz hzq w hw hwq hzw
    rcases hedge z hz w hw hzw with h | h <;> rcases hq with hq | hq
    · exact hzq (h.1.trans hq)
    · exact hwq (h.2.trans hq)
    · exact hwq (h.2.trans hq)
    · exact hzq (h.1.trans hq)
  have hcard (q : V) (hq : x = q ∨ y = q) : (L q).card = 2 := by
    have h2 := hLtwo q
    by_contra hn
    have h3 : 3 ≤ (L q).card := by omega
    exact hbad (original_theorem_2_1_of_long_exceptional_endpoint M outer hg A hAface
      q (haway q hq) L hLtwo hLthree h3 a b hab ha hb ta tb hta htb htab)
  have hx2 := hcard x (Or.inl rfl)
  have hy2 := hcard y (Or.inr rfl)
  refine ⟨hx2,hy2,?_⟩
  by_contra hne
  have hnsub : ¬ L x ⊆ L y := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨t,htx,hty⟩ := Finset.not_subset.1 hnsub
  exact hbad (original_theorem_2_1_exceptional_colour_outside_other_list M outer hG hg A hAface
    x y hxA hedge hNo L hLtwo hLthree a b hab ha hb ta tb hta htb htab hxa hxb t htx hty
    (fun h => (hax h).elim) (fun h => (hbx h).elim))

end Thomassen
