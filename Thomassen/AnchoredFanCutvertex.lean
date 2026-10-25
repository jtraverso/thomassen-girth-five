/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanSpokes

/-! Cutvertices in the anchored-fan auxiliary induction. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- All cutvertices of the anchored fan are reduced. Prescribed cutvertices
keep exact old singleton colours, and unprescribed attachments use the complete
previous root-fan theorem on a genuinely smaller empty-prescription piece. -/
theorem anchoredFan_extension_of_cutvertex (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  obtain ⟨a, haP, hba⟩ := ha
  obtain ⟨S, hwS, hbS, haS, ⟨l, hlS, hlw⟩, ⟨r, hrS⟩, hsep⟩ := exists_cut_side_containing_edge w b a hba hdisc
  let T : Set V := insert w Sᶜ
  have hwT : w ∈ T := Or.inl rfl
  have hrT : r ∈ T := Or.inr hrS
  have hrw : r ≠ w := fun h => hrS (h ▸ hwS)
  have hlT : l ∉ T := by
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hlw, false_or, not_not] using hlS
  let : Nontrivial S := ⟨⟨⟨l, hlS⟩, ⟨w, hwS⟩, fun h => hlw (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨r, hrT⟩, ⟨w, hwT⟩, fun h => hrw (congrArg Subtype.val h)⟩⟩
  obtain ⟨hcover, hinter, hedges, hsepT⟩ := cut_side_pair_properties hwS hsep
  have hSc := preconnected_cut_side hG hwS hsep
  have hTc := preconnected_cut_side hG hwT hsepT
  have hSsmall := card_induced_vertices_lt S hrS
  have hTsmall := card_induced_vertices_lt T hlT
  by_cases hwP : w ∈ I.precolor.vertices
  · have hbT : b ∉ T := by
      rintro (hbw | hbout)
      · exact hbP (hbw ▸ hwP)
      · exact hbout hbS
    obtain ⟨QS, hSv, hSe⟩ := I.precolor.exists_induce_cut hwS hwP hsep
    obtain ⟨QT, hTv, hTe⟩ := I.precolor.exists_induce_cut hwT hwP hsepT
    apply I.anchoredFan_extension_of_prescribed_cut hcard b hbP hbface f hf hp S T hbS hbT
      ⟨a, haS, haP, hba⟩ hcover ?_ hedges hSc hTc QS hSv hSe QT hTv hTe hSsmall hTsmall N hN hsmall hfan
    intro x hx
    have hxw : x = w := by rwa [hinter] at hx
    exact hxw ▸ hwP
  · have hPS : ∀ x ∈ I.precolor.vertices, x ∈ S := by
      rcases I.precolor.cut_side_dichotomy_avoiding hwP S hsep with h | h
      · exact h
      · exact (h a haP haS).elim
    have hNoPT : ∀ x ∈ T, x ∉ I.precolor.vertices := by
      intro x hx hxP
      rcases hx with hxw | hxout
      · exact hwP (hxw ▸ hxP)
      · exact hxout (hPS x hxP)
    obtain ⟨cS, hcS, hgS⟩ := I.anchoredFan_on_induced hcard b hbP hbface f hf hp S hSc hbS
      ⟨a, haS, haP, hba⟩ (I.precolor.induce S hPS)
      (BoundaryPrecolor.mem_vertices_induce _ S hPS) (BoundaryPrecolor.mem_edges_induce _ S hPS) hSsmall hfan
    by_cases hbw : b = w
    · subst w
      let JT := I.induceUnprecolored T hTc hNoPT
      have hstar : ∀ x : T, x ∈ rootStar JT ⟨b, hwT⟩ ↔ x.1 ∈ rootStar I b := by
        intro x
        change (x = ⟨b, hwT⟩ ∨ G.Adj b x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
        simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
      obtain ⟨cT, hcT, hgT⟩ := JT.rootStar_extension_of_smaller N hsmall rfl hTc ⟨b, hwT⟩
        (I.induceUnprecolored_on_old_face T hTc hNoPT _ hbface) (fun x => f x.1)
        (fun x hx => hf x.1 ((hstar x).1 hx))
        (fun x hx y hy hxy => hp x.1 ((hstar x).1 hx) y.1 ((hstar y).1 hy) hxy) (hTsmall.trans hN)
      apply I.rootStar_extension_of_induced_colourings b f hf S T
        (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS hcT hgS
        (fun x hx => hgT x ((hstar x).2 hx))
      intro x hxS hxT
      have hxb : x = b := by have h : x ∈ S ∩ T := ⟨hxS, hxT⟩; rwa [hinter] at h
      subst x
      exact (hgS ⟨b, hbS⟩ (Or.inl rfl)).trans (hgT ⟨b, hwT⟩ (Or.inl rfl)).symm
    · have hstarS : ∀ x ∈ rootStar I b, x ∈ S := by
        intro x hx
        rcases hx with rfl | hx
        · exact hbS
        · by_cases hxw : x = w
          · exact hxw ▸ hwS
          · exact (hsep hx.1 hbw hxw).1 hbS
      have hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card := by
        by_cases hwface : OnOuterFace I.embedding I.outer w
        · exact Or.inl hwface
        · refine Or.inr (fun x => I.interior_lists x.1 ?_)
          intro hxface
          have hpath : RIn G ({w} : Set V)ᶜ b x.1 := ((onOuterFace_connSet I.embedding I.outer).2 b hbface x.1 hxface).mono_set
            (fun z hz h => hwface (h ▸ hz))
          have hxS := (rIn_side_of_avoids_cut hsep hpath).1 hbS
          rcases x.2 with hxw | hxout
          · exact hwface (hxw ▸ hxface)
          · exact hxout hxS
      obtain ⟨JT, hPT, hLT, hwface⟩ : ∃ J : BoundaryInstance (G.induce T) C,
          J.precolor = .empty ∧ (∀ x : T, J.lists x = I.lists x.1) ∧
          OnOuterFace J.embedding J.outer ⟨w, hwT⟩ := by
        rcases hboundary with hwface | hthree
        · exact ⟨I.induceUnprecolored T hTc hNoPT, rfl, fun _ => rfl,
            I.induceUnprecolored_on_old_face T hTc hNoPT _ hwface⟩
        · obtain ⟨z, hwz⟩ := hTc.exists_adj_of_nontrivial (⟨w, hwT⟩ : T)
          let o : (G.induce T).Dart := ⟨(⟨w, hwT⟩, z), hwz⟩
          let J := BoundaryInstance.of_three_lists (inducedPlaneMap I.embedding T) o
            (five_le_egirth_induce T I.girth) (fun x => I.lists x.1) hthree (fun x => I.prescribed x.1)
          exact ⟨J, rfl, fun _ => rfl, onOuterFace_self _ o⟩
      obtain ⟨g, hgw, hg, hgp⟩ := JT.exists_rootStar_colours hPT ⟨w, hwT⟩ (cS ⟨w, hwS⟩)
        (by rw [hLT]; exact hcS _)
      obtain ⟨cT, hcT, hgT⟩ := JT.rootStar_extension_of_smaller N hsmall hPT hTc ⟨w, hwT⟩ hwface g hg hgp (hTsmall.trans hN)
      have hwagree : cT ⟨w, hwT⟩ = cS ⟨w, hwS⟩ := (hgT _ (Or.inl rfl)).trans hgw
      have hstarT : ∀ x : T, x.1 ∈ rootStar I b → cT x = f x.1 := by
        intro x hx
        have hxw : x.1 = w := by
          have h : x.1 ∈ S ∩ T := ⟨hstarS x.1 hx, x.2⟩
          rwa [hinter] at h
        have heq : x = ⟨w, hwT⟩ := Subtype.ext hxw
        rw [heq, hwagree]
        have hstarw : w ∈ rootStar I b := by simpa only [hxw] using hx
        exact hgS ⟨w, hwS⟩ hstarw
      apply I.rootStar_extension_of_induced_colourings b f hf S T
        (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS
        (fun x => by rw [← hLT]; exact hcT x) hgS hstarT
      intro x hxS hxT
      have hxw : x = w := by have h : x ∈ S ∩ T := ⟨hxS, hxT⟩; rwa [hinter] at h
      subst x
      exact hwagree.symm

end BoundaryInstance
end Thomassen
