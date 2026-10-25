/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarCuts

/-! Cutvertices in the auxiliary two-endpoint fan. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A cut side can contain both ends of any original edge. -/
lemma exists_cut_side_containing_edge (w a b : V) (hab : G.Adj a b)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, w ∈ S ∧ a ∈ S ∧ b ∈ S ∧ (∃ x ∈ S, x ≠ w) ∧ (∃ y, y ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S) := by
  by_cases haw : a = w
  · obtain ⟨S, hwS, hbS, hleft, hright, hsep⟩ := exists_cut_side_containing w b hdisc
    exact ⟨S, hwS, haw ▸ hwS, hbS, hleft, hright, hsep⟩
  · obtain ⟨S, hwS, haS, hleft, hright, hsep⟩ := exists_cut_side_containing w a hdisc
    have hbS : b ∈ S := by
      by_cases hbw : b = w
      · exact hbw ▸ hwS
      · exact (hsep hab haw hbw).1 haS
    exact ⟨S, hwS, haS, hbS, hleft, hright, hsep⟩

/-- On the other side, roots absent from that piece contribute only separator
vertices; a retained root contributes its own short-neighbour star. -/
lemma edgeStar_other_side_subset_rootStar (I : BoundaryInstance G C) (a b r : V)
    (S T : Set V) (har : a = r ∨ a ∉ T) (hbr : b = r ∨ b ∉ T)
    (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I r)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    ∀ x ∈ T, x ∈ edgeStar I a b → x ∈ rootStar I r := by
  have hone : ∀ s : V, s = r ∨ s ∉ T → ∀ x ∈ T, x ∈ rootStar I s → x ∈ rootStar I r := by
    intro s hs x hxT hx
    rcases hs with rfl | hs
    · exact hx
    · rcases hx with rfl | ⟨hadj, _⟩
      · exact (hs hxT).elim
      · rcases hedges hadj with hS | hT
        · exact hinter x ⟨hS.2, hxT⟩
        · exact (hs hT.1).elim
  intro x hxT hx
  exact hx.elim (hone a har x hxT) (hone b hbr x hxT)

namespace BoundaryInstance
variable [Fintype V]
/-- Every cutvertex of the smaller two-endpoint fan is reduced to one edge-star
piece and one already verified root-star piece. -/
theorem edgeStar_extension_of_cutvertex (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  obtain ⟨S, hwS, haS, hbS, ⟨x, hxS, hxw⟩, ⟨y, hyS⟩, hsep⟩ := exists_cut_side_containing_edge w a b hab hdisc
  let T : Set V := insert w Sᶜ
  have hwT : w ∈ T := Or.inl rfl
  have hyT : y ∈ T := Or.inr hyS
  have hyw : y ≠ w := fun h => hyS (h ▸ hwS)
  have hxT : x ∉ T := by simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hxw, false_or, not_not] using hxS
  let : Nontrivial S := ⟨⟨⟨x, hxS⟩, ⟨w, hwS⟩, fun h => hxw (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨y, hyT⟩, ⟨w, hwT⟩, fun h => hyw (congrArg Subtype.val h)⟩⟩
  obtain ⟨hcover, hinter, hedges, hsepT⟩ := cut_side_pair_properties hwS hsep
  have hSc := preconnected_cut_side hG hwS hsep
  have hTc := preconnected_cut_side hG hwT hsepT
  have hSsmall := card_induced_vertices_lt S hyS
  have hTsmall := card_induced_vertices_lt T hxT
  by_cases hwr : w = a ∨ w = b
  · have hwface : OnOuterFace I.embedding I.outer w := by rcases hwr with rfl | rfl; exact ha; exact hb
    have hsub : ∀ z ∈ rootStar I w, z ∈ edgeStar I a b := by
      intro z hz
      rcases hwr with h | h
      · exact Or.inl (h ▸ hz)
      · exact Or.inr (h ▸ hz)
    have hsepStar : ∀ z ∈ S ∩ T, z ∈ rootStar I w := by
      intro z hz
      have hzw : z = w := by rwa [hinter] at hz
      exact Or.inl hzw
    have hAr : a = w ∨ a ∉ T := by
      by_cases h : a = w
      · exact Or.inl h
      · exact Or.inr (fun haT => h (by have hz : a ∈ S ∩ T := ⟨haS, haT⟩; rwa [hinter] at hz))
    have hBr : b = w ∨ b ∉ T := by
      by_cases h : b = w
      · exact Or.inl h
      · exact Or.inr (fun hbT => h (by have hz : b ∈ S ∩ T := ⟨hbS, hbT⟩; rwa [hinter] at hz))
    exact I.edgeStar_extension_of_root_cut hP a b hab ha hb f hf hproper S T haS hbS w hwface hwT
      hsub hcover hsepStar (edgeStar_other_side_subset_rootStar I a b w S T hAr hBr hsepStar hedges)
      hedges hSc hTc hSsmall hTsmall N hN hsmall hedge
  · have haw : a ≠ w := fun h => hwr (Or.inl h.symm)
    have hbw : b ≠ w := fun h => hwr (Or.inr h.symm)
    have hstarS : ∀ z ∈ edgeStar I a b, z ∈ S := by
      have hone : ∀ r ∈ S, r ≠ w → ∀ z ∈ rootStar I r, z ∈ S := by
        intro r hrS hrw z hz
        rcases hz with rfl | ⟨hrz, _⟩
        · exact hrS
        · by_cases hzw : z = w
          · exact hzw ▸ hwS
          · exact (hsep hrz hrw hzw).1 hrS
      intro z hz
      exact hz.elim (hone a haS haw z) (hone b hbS hbw z)
    have hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ z : T, 3 ≤ (I.lists z.1).card := by
      by_cases hwface : OnOuterFace I.embedding I.outer w
      · exact Or.inl hwface
      · refine Or.inr (fun z => I.interior_lists z.1 ?_)
        intro hzface
        have hp : RIn G ({w} : Set V)ᶜ a z.1 := ((onOuterFace_connSet I.embedding I.outer).2 a ha z.1 hzface).mono_set
          (fun t ht h => hwface (h ▸ ht))
        have hzS := (rIn_side_of_avoids_cut hsep hp).1 haS
        rcases z.2 with hzw | hzout
        · exact hwface (hzw ▸ hzface)
        · exact hzout hzS
    exact I.edgeStar_extension_of_separate_cut hP a b hab ha hb f hf hproper S T w hwS hwT haS hbS
      hstarS hcover hinter hedges hSc hTc hboundary hSsmall hTsmall N hN hsmall hedge

end BoundaryInstance
end Thomassen
