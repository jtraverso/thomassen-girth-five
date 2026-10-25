/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStarExtension

/-! Complete reduction at unprescribed boundary cutvertices. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A prescribed path or cycle avoiding a cutvertex lies on one side. -/
lemma BoundaryPrecolor.cut_side_dichotomy_avoiding (P : BoundaryPrecolor G) {w : V}
    (hw : w ∉ P.vertices) (S : Set V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S)) :
    (∀ x ∈ P.vertices, x ∈ S) ∨ (∀ x ∈ P.vertices, x ∉ S) := by
  have hwalk : ∀ {a b : V} (p : G.Walk a b), w ∉ p.support →
      (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∉ S) := by
    intro a b p hp
    have hside := walk_side_of_avoids_cut hsep p hp
    by_cases ha : a ∈ S
    · exact Or.inl (fun x hx => (hside x hx).2 ha)
    · exact Or.inr (fun x hx h => ha ((hside x hx).1 h))
  cases P with
  | empty => exact Or.inl (by simp)
  | path p _ _ =>
    simpa only [BoundaryPrecolor.vertices, List.mem_toFinset] using hwalk p (fun h => hw (List.mem_toFinset.2 h))
  | cycle p _ _ =>
    simpa only [BoundaryPrecolor.vertices, List.mem_toFinset] using hwalk p (fun h => hw (List.mem_toFinset.2 h))

namespace BoundaryInstance
variable [Fintype V]

/-- Colour the side with the old prescription first; the complete auxiliary
fan induction extends its attachment colour to the empty-prescription side. -/
theorem colourable_of_unprescribed_boundary_cut_piece (I : BoundaryInstance G C)
    (hG : G.Preconnected) (w : V) (hwface : OnOuterFace I.embedding I.outer w)
    (S : Set V) (hwS : w ∈ S) (hleft : ∃ a ∈ S, a ≠ w) (hright : ∃ b, b ∉ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S))
    (hNoP : ∀ x ∈ S, x ∉ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨a, ha, haw⟩ := hleft
  obtain ⟨b, hb⟩ := hright
  let T : Set V := insert w Sᶜ
  have hwT : w ∈ T := Or.inl rfl
  have hbT : b ∈ T := Or.inr hb
  have hbw : b ≠ w := fun h => hb (h ▸ hwS)
  have haT : a ∉ T := by
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, haw, false_or, not_not] using ha
  let : Nontrivial S := ⟨⟨⟨a, ha⟩, ⟨w, hwS⟩, fun h => haw (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨b, hbT⟩, ⟨w, hwT⟩, fun h => hbw (congrArg Subtype.val h)⟩⟩
  obtain ⟨hcover, hinter, hedges, hsepT⟩ := cut_side_pair_properties hwS hsep
  have hSc := preconnected_cut_side hG hwS hsep
  have hTc := preconnected_cut_side hG hwT hsepT
  have hPT : ∀ x ∈ I.precolor.vertices, x ∈ T := fun x hx => Or.inr (fun hxS => hNoP x hxS hx)
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTc hPT)
    (card_induced_vertices_lt T haT)
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [induceConnected, inducePrecolor] using hcT
  let JS := I.induceUnprecolored S hSc hNoP
  have hwfaceS : OnOuterFace JS.embedding JS.outer ⟨w, hwS⟩ :=
    I.induceUnprecolored_on_old_face S hSc hNoP _ hwface
  obtain ⟨f, hfw, hf, hproper⟩ := JS.exists_rootStar_colours rfl ⟨w, hwS⟩
    (cT ⟨w, hwT⟩) (hT ⟨w, hwT⟩)
  obtain ⟨cS, hcS, hagreeS⟩ := JS.rootStar_extension_of_smaller (Nat.card V) hsmall rfl hSc
    ⟨w, hwS⟩ hwfaceS f hf hproper (card_induced_vertices_lt S hb)
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hcS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have hxw : x = w := by have h : x ∈ S ∩ T := ⟨hx, hy⟩; rwa [hinter] at h
    subst x
    exact (hagreeS _ (Or.inl rfl)).trans hfw

/-- Every unprescribed cutvertex on the selected face is eliminated, with no
bound on the number of short neighbours in its boundary fan. -/
theorem colourable_of_unprescribed_boundary_cutvertex (I : BoundaryInstance G C)
    (hG : G.Preconnected) (w : V) (hw : w ∉ I.precolor.vertices)
    (hwface : OnOuterFace I.embedding I.outer w)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, hwS, ⟨a, ha, haw⟩, ⟨b, hb⟩, hsep⟩ := exists_cut_side_of_delete_disconnected hdisc
  rcases I.precolor.cut_side_dichotomy_avoiding hw S hsep with hPS | hPS
  · let T : Set V := insert w Sᶜ
    have haT : a ∉ T := by
      simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, haw, false_or, not_not] using ha
    apply I.colourable_of_unprescribed_boundary_cut_piece hG w hwface T (Or.inl rfl)
      ⟨b, Or.inr hb, fun h => hb (h ▸ hwS)⟩ ⟨a, haT⟩ (cut_side_pair_properties hwS hsep).2.2.2 ?_ hsmall
    intro x hx hxP
    rcases hx with hxw | hxS
    · exact hw (hxw ▸ hxP)
    · exact hxS (hPS x hxP)
  · apply I.colourable_of_unprescribed_boundary_cut_piece hG w hwface S hwS
      ⟨a, ha, haw⟩ ⟨b, hb⟩ hsep ?_ hsmall
    intro x hx hxP
    exact hPS x hxP hx

/-- All cutvertex cases of the main boundary-extension induction are closed. -/
theorem colourable_of_cutvertex (I : BoundaryInstance G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hwP : w ∈ I.precolor.vertices
  · exact I.colourable_of_precolored_cutvertex w hwP hG hdisc hsmall
  · by_cases hwface : OnOuterFace I.embedding I.outer w
    · exact I.colourable_of_unprescribed_boundary_cutvertex hG w hwP hwface hdisc hsmall
    · exact I.colourable_of_interior_cutvertex hG w hwface hdisc hsmall

/-- A connected smallest counterexample has no cutvertex. -/
lemma delete_preconnected_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected := by
  intro w
  by_contra hdisc
  exact hbad (I.colourable_of_cutvertex hG w hdisc hsmall)

/-- The main induction closes every instance on at most two vertices. -/
lemma colourable_of_card_le_two (I : BoundaryInstance G C) (hcard : Nat.card V ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hP : ∀ x, x ∈ I.precolor.vertices
  · exact I.colourable_of_all_precolored hP
  · push Not at hP
    obtain ⟨x, hx⟩ := hP
    apply I.colourable_of_few_neighbours x hx ?_ hsmall
    have hbound : (Finset.univ.filter (G.Adj x)).card ≤ (Finset.univ.erase x : Finset V).card := by
      apply Finset.card_le_card
      intro y hy
      exact Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hy).2.ne.symm, Finset.mem_univ _⟩
    have hlist := I.outside_precolor_list_ge_two hx
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, ← Nat.card_eq_fintype_card] at hbound
    omega

/-- A smallest counterexample has an actual simple facial boundary. The
disconnected, small-cardinality and all cutvertex cases are eliminated here. -/
theorem minimal_counterexample_has_native_face_cycle (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  have hG : G.Preconnected := by
    by_contra hdisc
    exact hbad (I.colourable_of_disconnected hsmall hdisc)
  have hcard : 3 ≤ Nat.card V := by
    by_contra h
    exact hbad (I.colourable_of_card_le_two (by omega) hsmall)
  have hdelete := I.delete_preconnected_of_minimal_counterexample hG hbad hsmall
  exact ⟨hG, hcard, hdelete,
    exists_native_face_cycle_of_delete_preconnected I.embedding I.outer hG hcard hdelete⟩

end BoundaryInstance
end Thomassen
