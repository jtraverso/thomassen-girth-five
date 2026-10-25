/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ReleasedEdge

/-! Edge cuts with the original prescription on one side. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- An edge cut retaining the prescription in one side is solved even when
its ends are not prescribed. Arbitrarily many short neighbours are permitted. -/
theorem colourable_of_edge_cut_with_one_sided_prescription (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hPP : a ∈ I.precolor.vertices ∧ b ∈ I.precolor.vertices
  · exact I.colourable_of_prescribed_edge_cut S T hab hPP.1 hPP.2 hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  · have h3 : 3 ≤ (I.lists a).card ∨ 3 ≤ (I.lists b).card := by
      by_contra h
      push Not at h
      have he := I.short_edges hab (by omega : (I.lists a).card ≤ 2) (by omega : (I.lists b).card ≤ 2)
      exact hPP (I.precolor.endpoints_of_mem_edges he)
    obtain ⟨F, hF⟩ : ∃ F : Finset C, 3 ≤ F.card := h3.elim (fun h => ⟨I.lists a, h⟩) (fun h => ⟨I.lists b, h⟩)
    have haST : a ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
    have hbST : b ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
    have haS := haST.1
    have haT := haST.2
    have hbS := hbST.1
    have hbT := hbST.2
    have hAdjS : (G.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hab
    have hAdjT : (G.induce T).Adj ⟨a, haT⟩ ⟨b, hbT⟩ := hab
    let : Nontrivial S := hAdjS.nontrivial
    let : Nontrivial T := hAdjT.nontrivial
    have hPT : ∀ x ∈ I.precolor.vertices, x ∈ T := by
      intro x hxP
      by_cases hxS : x ∈ S
      · rcases hPcap x hxS hxP with rfl | rfl
        · exact haT
        · exact hbT
      · have hx : x ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ x
        exact hx.resolve_left hxS
    obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTc.preconnected hPT) hTsmall
    have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [induceConnected, inducePrecolor] using hcT
    obtain ⟨J, hPJ, hUnchanged, hSub, haFace, hbFace⟩ :=
      I.exists_empty_induced_releasing_edge S hSc.preconnected a b haS hbS ha hb hPcap F hF
    obtain ⟨f, hfa, hfb, hf, hproper⟩ := J.exists_edgeStar_colours hPJ ⟨a, haS⟩ ⟨b, hbS⟩ hab
      (cT ⟨a, haT⟩) (cT ⟨b, hbT⟩) (hSub _ (hT _)) (hSub _ (hT _)) (cT.valid hAdjT)
    obtain ⟨cS, hcS, hgS⟩ := J.edgeStar_extension_of_smaller (Nat.card V) hsmall hPJ hSc.preconnected
      ⟨a, haS⟩ ⟨b, hbS⟩ hab haFace hbFace f hf hproper hSsmall
    have hca : cS ⟨a, haS⟩ = cT ⟨a, haT⟩ := (hgS _ (Or.inl (Or.inl rfl))).trans hfa
    have hcb : cS ⟨b, hbS⟩ = cT ⟨b, hbT⟩ := (hgS _ (Or.inr (Or.inl rfl))).trans hfb
    have hS : ∀ x : S, cS x ∈ I.lists x.1 := by
      intro x
      by_cases hxa : x.1 = a
      · have heq : x = ⟨a, haS⟩ := Subtype.ext hxa
        rw [heq, hca]
        exact hT _
      · by_cases hxb : x.1 = b
        · have heq : x = ⟨b, hbS⟩ := Subtype.ext hxb
          rw [heq, hcb]
          exact hT _
        · have hc := hcS x
          rwa [hUnchanged x hxa hxb] at hc
    refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
    · intro x
      have hx := Set.mem_univ x
      rwa [← hcover] at hx
    · intro x hx hy
      have h : x ∈ S ∩ T := ⟨hx, hy⟩
      rw [hinter] at h
      rcases h with rfl | h
      · exact hca
      · have heq : x = b := Set.mem_singleton_iff.1 h
        subst x
        exact hcb

end BoundaryInstance
end Thomassen
