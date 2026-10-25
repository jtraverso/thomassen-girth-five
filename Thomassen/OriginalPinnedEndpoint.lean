/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalIndependent

/-! Removing a fixed endpoint from the two-list set, with a genuine dummy colour. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- The dummy-colour reduction from the original proof, step (7).
A fixed endpoint may be removed from `A` even if it has only two colours.
An `Option` colour type supplies a genuinely fresh colour without assuming
that the user's colour type contains a third colour. -/
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
  let someEmb : C ↪ Option C := ⟨some,Option.some_injective C⟩
  let L' : V → Finset (Option C) := fun x =>
    if x = a then insert none ((L x).map someEmb) else (L x).map someEmb
  have hsome : ∀ x t, some t ∈ L' x ↔ t ∈ L x := by
    intro x t
    by_cases hx : x = a <;> simp [L',hx,someEmb]
  have hL' : ∀ x, 2 ≤ (L' x).card := by
    intro x
    by_cases hx : x = a
    · simp only [L',ite_eq_left hx]
      exact (hLtwo x).trans ((Finset.card_map someEmb).symm.trans_le
        (Finset.card_le_card (Finset.subset_insert _ _)))
    · simpa only [L',ite_eq_right hx,Finset.card_map] using hLtwo x
  have hLa : 3 ≤ (L' a).card := by
    have hn : none ∉ (L a).map someEmb := by simp [someEmb]
    simp only [L',ite_eq_left rfl,Finset.card_insert_of_notMem hn,Finset.card_map]
    have := hLtwo a
    omega
  obtain ⟨c,hc,hca,hcb⟩ := original_theorem_2_1_independent M outer hg
    (A \ {a}) (fun x hx => hAface x hx.1)
    (fun x hx y hy => hAind x hx.1 (by simpa using hx.2) y hy.1 (by simpa using hy.2))
    L' hL' (by
      intro x hx
      by_cases hxa : x = a
      · subst x; exact hLa
      · have hn : x ∉ A := fun h => hx ⟨h,by simpa using hxa⟩
        simpa only [L',ite_eq_right hxa,Finset.card_map] using hLthree x hn)
    a b hab ha hb (some ta) (some tb) ((hsome a ta).2 hta) ((hsome b tb).2 htb)
    (fun h => htab (Option.some.inj h))
  let f : V → C := fun x => (c x).getD ta
  have hdecode : ∀ x, some (f x) = c x := by
    intro x
    by_cases hx : x = a
    · subst x; simp [f,hca]
    · have hm := hc x
      change c x ∈ L' x at hm
      simp only [L',ite_eq_right hx,Finset.mem_map] at hm
      obtain ⟨t,_,ht⟩ := hm
      change some t = c x at ht
      simp [f,← ht]
  have hf : ∀ x, f x ∈ L x := by
    intro x
    apply (hsome x (f x)).1
    rw [hdecode x]
    exact hc x
  refine ⟨Coloring.mk f ?_,hf,?_,?_⟩
  · intro x y hxy he
    apply c.valid hxy
    rw [← hdecode x,← hdecode y,he]
  · change f a = ta
    apply Option.some.inj
    exact (hdecode a).trans hca
  · change f b = tb
    apply Option.some.inj
    exact (hdecode b).trans hcb

/-- The exceptional alternative of Theorem 2.1 is closed whenever its unique
short-list edge meets the fixed edge. The length-two-path condition is not
needed for this case. -/
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
  have haway (r : V) (hr : x = r ∨ y = r) :
      ∀ z ∈ A, z ≠ r → ∀ w ∈ A, w ≠ r → ¬ G.Adj z w := by
    intro z hz hzr w hw hwr hzw
    rcases hedge z hz w hw hzw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rcases hr with h | h
      · exact hzr h
      · exact hwr h
    · rcases hr with h | h
      · exact hwr h
      · exact hzr h
  rcases hinc with h | h | h | h
  · exact extend_edge_of_independent_away_from_fixed_endpoint M outer hg A hAface
      L hLtwo hLthree a b hab ha hb ta tb hta htb htab (haway a (Or.inl h))
  · exact extend_edge_of_independent_away_from_fixed_endpoint M outer hg A hAface
      L hLtwo hLthree a b hab ha hb ta tb hta htb htab (haway a (Or.inr h))
  · obtain ⟨c,hc,hcb,hca⟩ := extend_edge_of_independent_away_from_fixed_endpoint M outer hg A hAface
      L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm (haway b (Or.inl h))
    exact ⟨c,hc,hca,hcb⟩
  · obtain ⟨c,hc,hcb,hca⟩ := extend_edge_of_independent_away_from_fixed_endpoint M outer hg A hAface
      L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm (haway b (Or.inr h))
    exact ⟨c,hc,hca,hcb⟩

end Thomassen
