/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CutPrecolor
public import Thomassen.CycleSeparation

/-! Strict induction at cutvertices outside the selected face. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Reachability avoiding a cutvertex preserves membership in either cut side. -/
lemma rIn_side_of_avoids_cut
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (hr : RIn G ({v} : Set V)ᶜ a b) : (a ∈ S ↔ b ∈ S) := by
  induction hr with
  | refl => exact Iff.rfl
  | @tail b c _ hbc ih => exact ih.trans (hsep hbc.1 hbc.2.1 hbc.2.2)

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Colour a cut side disjoint from the original selected face after colouring
the other side. Its original lists are all three-lists, so prescribing the cut
vertex leaves an admissible singleton path on any incident induced face. -/
theorem colourable_of_interior_cut_piece (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (v : V) (S : Set V) (hv : v ∈ S)
    (hleft : ∃ a ∈ S, a ≠ v) (hright : ∃ b, b ∉ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    (hNoFace : ∀ x ∈ S, ¬ OnOuterFace I.embedding I.outer x)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨a, ha, hav⟩ := hleft
  obtain ⟨b, hb⟩ := hright
  let T : Set V := insert v Sᶜ
  have hvT : v ∈ T := Or.inl rfl
  have hbT : b ∈ T := Or.inr hb
  have hbv : b ≠ v := fun h => hb (h ▸ hv)
  have haT : a ∉ T := by
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hav, false_or, not_not] using ha
  let : Nontrivial S := ⟨⟨⟨a, ha⟩, ⟨v, hv⟩, fun h => hav (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨b, hbT⟩, ⟨v, hvT⟩, fun h => hbv (congrArg Subtype.val h)⟩⟩
  have hsepT : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ T ↔ y ∈ T) := by
    intro x y hxy hx hy
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hx, hy, false_or] using
      not_congr (hsep hxy hx hy)
  have hSconn := preconnected_cut_side hconn hv hsep
  have hTconn := preconnected_cut_side hconn hvT hsepT
  have hPT : ∀ x ∈ I.precolor.vertices, x ∈ T := fun x hx =>
    Or.inr (fun hxS => hNoFace x hxS (I.on_outer x hx))
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTconn hPT)
    (card_induced_vertices_lt T haT)
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    simpa only [induceConnected, inducePrecolor] using hcT
  obtain ⟨w, hvw⟩ := hSconn.exists_adj_of_nontrivial (⟨v, hv⟩ : S)
  let outer : (G.induce S).Dart := ⟨(⟨v, hv⟩, w), hvw⟩
  let Q : BoundaryPrecolor (G.induce S) := .path (.nil (u := ⟨v, hv⟩)) (by simp) (by simp)
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 = v := by
    intro x
    simp only [Q, BoundaryPrecolor.vertices, Walk.support_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false, Subtype.ext_iff]
  let L : S → Finset C := fun x => if x.1 = v then {cT ⟨v, hvT⟩} else I.lists x.1
  have hThree : ∀ x : S, 3 ≤ (I.lists x.1).card :=
    fun x => I.interior_lists x.1 (hNoFace x.1 x.2)
  have hOn : OnOuterFace (inducedPlaneMap I.embedding S) outer (⟨v, hv⟩ : S) :=
    onOuterFace_self _ _
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := outer
    precolor := Q
    lists := L
    prescribed := fun _ => cT ⟨v, hvT⟩
    on_outer := by
      intro x hx
      have heq : x = ⟨v, hv⟩ := Subtype.ext ((hQv x).1 hx)
      exact heq ▸ hOn
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by simp [Q, BoundaryPrecolor.edges]
    boundary_lists := by
      intro x _ hx
      have hne : x.1 ≠ v := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hne]
      exact (by decide : 2 ≤ 3).trans (hThree x)
    interior_lists := by
      intro x hx
      have hne : x.1 ≠ v := by
        intro h
        exact hx ((Subtype.ext h : x = ⟨v, hv⟩) ▸ hOn)
      simpa only [L, ite_eq_right hne] using hThree x
    short_edges := by
      intro x y hxy hx hy
      have hxv : x.1 = v := by
        by_contra h
        simp only [L, ite_eq_right h] at hx
        have := hThree x
        omega
      have hyv : y.1 = v := by
        by_contra h
        simp only [L, ite_eq_right h] at hy
        have := hThree y
        omega
      exact (hxy.ne (Subtype.ext (hxv.trans hyv.symm))).elim }
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) J (card_induced_vertices_lt S hb)
  change ∀ x : S, cS x ∈ L x at hcS
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by
    intro x
    have hx : cS x ∈ L x := hcS x
    by_cases heq : x.1 = v
    · have hcol : cS x = cT ⟨v, hvT⟩ := Finset.mem_singleton.1
        (by simpa only [L, ite_eq_left heq] using hx)
      rw [hcol, heq]
      exact hT ⟨v, hvT⟩
    · simpa only [L, ite_eq_right heq] using hx
  refine glue_induced_colourings S T I.lists ?_ ?_ cS cT hS hT ?_
  · intro x
    exact Classical.em (x ∈ S) |>.imp_right (fun h => Or.inr h)
  · intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact Or.inl ⟨hx, hy⟩
      · have hxv : x = v := by
          by_contra hxv
          exact hy ((hsep hxy hxv (fun h => hy (h ▸ hv))).1 hx)
        exact Or.inr ⟨Or.inl hxv, Or.inr hy⟩
    · by_cases hy : y ∈ S
      · have hyv : y = v := by
          by_contra hyv
          exact hx ((hsep hxy (fun h => hx (h ▸ hv)) hyv).2 hy)
        exact Or.inr ⟨Or.inr hx, Or.inl hyv⟩
      · exact Or.inr ⟨Or.inr hx, Or.inr hy⟩
  · intro x hx hy
    rcases hy with heq | hy
    · subst x
      exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left rfl] using hcS ⟨v, hx⟩)
    · exact (hy hx).elim

/-- Every cutvertex outside the selected face is eliminated by strict boundary
extension induction, without an extra assumption on its prescribed status. -/
theorem colourable_of_interior_cutvertex (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (v : V) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, hvS, ⟨a, ha, hav⟩, ⟨b, hb⟩, hsep⟩ :=
    exists_cut_side_of_delete_disconnected hdisc
  have hroot := onOuterFace_self I.embedding I.outer
  have hface : ∀ x, OnOuterFace I.embedding I.outer x → (I.outer.fst ∈ S ↔ x ∈ S) := by
    intro x hx
    apply rIn_side_of_avoids_cut hsep
    exact ((onOuterFace_connSet I.embedding I.outer).2 _ hroot _ hx).mono_set
      (fun z hz h => hv (h ▸ hz))
  by_cases hrS : I.outer.fst ∈ S
  · let T : Set V := insert v Sᶜ
    have hbv : b ≠ v := fun h => hb (h ▸ hvS)
    have haT : a ∉ T := by
      simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hav, false_or, not_not] using ha
    have hsepT : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ T ↔ y ∈ T) := by
      intro x y hxy hx hy
      simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hx, hy, false_or] using
        not_congr (hsep hxy hx hy)
    apply I.colourable_of_interior_cut_piece hconn v T (Or.inl rfl)
      ⟨b, Or.inr hb, hbv⟩ ⟨a, haT⟩ hsepT ?_ hsmall
    intro x hx hOn
    rcases hx with heq | hx
    · exact hv (heq ▸ hOn)
    · exact hx ((hface x hOn).1 hrS)
  · apply I.colourable_of_interior_cut_piece hconn v S hvS ⟨a, ha, hav⟩ ⟨b, hb⟩ hsep ?_ hsmall
    intro x hx hOn
    exact hrS ((hface x hOn).2 hx)

/-- In a smallest counterexample, every remaining cutvertex must lie on the
selected face and outside the prescription. This isolates the boundary fan
case without assuming two-connectivity. -/
lemma cutvertex_constraints (I : BoundaryInstance G C) (hconn : G.Preconnected)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (v : V) (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected) :
    OnOuterFace I.embedding I.outer v ∧ v ∉ I.precolor.vertices := by
  constructor
  · by_contra hv
    exact hbad (I.colourable_of_interior_cutvertex hconn v hv hdisc hsmall)
  · intro hvP
    exact hbad (I.colourable_of_precolored_cutvertex v hvP hconn hdisc hsmall)

end BoundaryInstance
end Thomassen
