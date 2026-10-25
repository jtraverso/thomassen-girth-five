/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarSpoke
public import Thomassen.PrescribedCycleNormalization

/-! The complete facial-boundary step of two-endpoint fan induction. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance
/-- In a failed smaller edge-star problem, roots have no boundary chords to
another root or to any old short-list neighbour. -/
lemma edgeStar_adj_consecutive_of_strict_induction (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (hbad : ¬ EdgeStarExtension I a b f)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) (i j : ZMod k) (hiroot : c i = a ∨ c i = b)
    (hjroot : c j = a ∨ c j = b ∨ (I.lists (c j)).card ≤ 2)
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  by_contra h
  push Not at h
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj h.1 h.2
  exact hbad (I.edgeStar_extension_of_spoke_cut hP a b hab ha hb f hf hproper (c i) (c j) hiroot hadj hjroot
    S T hcover hinter hedges hSc hTc hSsmall hTsmall N hN hsmall hedge)

/-- An actual simple facial boundary reduces a two-endpoint fan to at most
four prescribed vertices. Every root chord is handled by a strict actual cut. -/
theorem edgeStar_extension_of_facial_boundary (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c) (hca : c 0 = a)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  by_contra hbad
  have hallowed := I.edgeStar_adj_consecutive_of_strict_induction hP hG a b hab ha hb f hf hproper
    hbad hc hk hface N hN hsmall hedge
  have hShort : ∀ i : ZMod k, c i = a ∨ c i = b → ∀ z, G.Adj (c i) z →
      (I.lists z).card ≤ 2 → z = c (i + 1) ∨ z = c (i - 1) := by
    intro i hiroot z hiz hzshort
    have hzface : OnOuterFace I.embedding I.outer z := by
      by_contra h
      have h3 := I.interior_lists z h
      omega
    obtain ⟨j, hj⟩ := hrange z hzface
    have hadj : G.Adj (c i) (c j) := by rwa [hj]
    rcases hallowed i j hiroot (Or.inr (Or.inr (by rwa [hj]))) hadj with h | h
    · exact Or.inl (by rw [← hj, h])
    · exact Or.inr (by rw [← hj, h, add_sub_cancel_right])
  obtain ⟨j, hj⟩ := hrange b hb
  have hcons := hallowed 0 j (Or.inl hca) (Or.inr (Or.inl hj)) (by rw [hca, hj]; exact hab)
  have hne : c (-1) ≠ c 1 := by
    intro h
    have hz : (2 : ZMod k) = 0 := by have he := hc.inj h; linear_combination -he
    exact zmod_two_ne_zero_of_three_le hk hz
  rcases hcons with hjone | hjminus
  · have hcb : c 1 = b := by have h := hj; rw [hjone, zero_add] at h; exact h
    have hal : G.Adj a (c (-1)) := by rw [← hca]; simpa only [neg_add_cancel] using (hc.adj (-1)).symm
    have hbr : G.Adj b (c 2) := by rw [← hcb]; simpa only [show (1 : ZMod k) + 1 = 2 by ring] using hc.adj 1
    have hra : c 2 ≠ a := by
      intro h
      have he : (2 : ZMod k) = 0 := hc.inj (h.trans hca.symm)
      exact zmod_two_ne_zero_of_three_le hk he
    have hlr : c (-1) ≠ c 2 := by
      intro h
      exact neighbors_nonadjacent I.girth hab hal (by rwa [← h] at hbr)
    apply hbad (I.edgeStar_extension_of_two_neighbours hP a b ha hb f hf hproper (c (-1)) (c 2)
      hab hal hbr (by rwa [← hcb]) hra hlr ?_ ?_ N hN hsmall)
    · intro z haz hz
      have h := hShort 0 (Or.inl hca) z (by rwa [hca]) hz
      simpa only [zero_add, zero_sub, hcb] using h
    · intro z hbz hz
      have h := hShort 1 (Or.inr hcb) z (by rwa [hcb]) hz
      have h' : z = c 2 ∨ z = a := by simpa only [show (1 : ZMod k) + 1 = 2 by ring, sub_self, hca] using h
      exact h'.symm
  · have hjm : j = -1 := by linear_combination -hjminus
    have hcb : c (-1) = b := hjm ▸ hj
    have hal : G.Adj a (c 1) := by rw [← hca]; simpa only [zero_add] using hc.adj 0
    have hbr : G.Adj b (c (-2)) := by
      rw [← hcb]
      simpa only [show (-2 : ZMod k) + 1 = -1 by ring] using (hc.adj (-2)).symm
    have hra : c (-2) ≠ a := by
      intro h
      have he := hc.inj (h.trans hca.symm)
      have hz : (2 : ZMod k) = 0 := by linear_combination -he
      exact zmod_two_ne_zero_of_three_le hk hz
    have hlr : c 1 ≠ c (-2) := by
      intro h
      exact neighbors_nonadjacent I.girth hab hal (by rwa [← h] at hbr)
    apply hbad (I.edgeStar_extension_of_two_neighbours hP a b ha hb f hf hproper (c 1) (c (-2))
      hab hal hbr (by rw [← hcb]; exact hne.symm) hra hlr ?_ ?_ N hN hsmall)
    · intro z haz hz
      have h := hShort 0 (Or.inl hca) z (by rwa [hca]) hz
      have h' : z = c 1 ∨ z = b := by simpa only [zero_add, zero_sub, hcb] using h
      exact h'.symm
    · intro z hbz hz
      have h := hShort (-1) (Or.inr hcb) z (by rwa [hcb]) hz
      simpa only [neg_add_cancel, show (-1 : ZMod k) - 1 = -2 by ring, hca] using h

end BoundaryInstance
end Thomassen
