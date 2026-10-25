/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStar
public import Thomassen.InteriorCutReduction
public import Thomassen.CutSidePair

/-! Root-star extension through actual strict cuts. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

lemma induceUnprecolored_on_old_face (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (hP : ∀ x ∈ S, x ∉ I.precolor.vertices)
    (x : S) (hx : OnOuterFace I.embedding I.outer x.1) :
    OnOuterFace (I.induceUnprecolored S hconn hP).embedding
      (I.induceUnprecolored S hconn hP).outer x := by
  exact (exists_outer_induced_of_preconnected I.embedding I.outer S hconn).choose_spec x hx

omit [Fintype V] in
/-- Glue induced colourings while preserving every prescribed star colour. -/
lemma rootStar_extension_of_induced_colourings (I : BoundaryInstance G C) (v : V) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (S T : Set V) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x : S, cS x ∈ I.lists x.1) (hcT : ∀ x : T, cT x ∈ I.lists x.1)
    (hstarS : ∀ x : S, x.1 ∈ rootStar I v → cS x = f x.1)
    (hstarT : ∀ x : T, x.1 ∈ rootStar I v → cT x = f x.1)
    (hagree : ∀ x (hx : x ∈ S) (hy : x ∈ T), cS ⟨x, hx⟩ = cT ⟨x, hy⟩) :
    RootStarExtension I v f := by
  let L : V → Finset C := fun x => if x ∈ rootStar I v then {f x} else I.lists x
  have hS : ∀ x : S, cS x ∈ L x.1 := by
    intro x
    by_cases hx : x.1 ∈ rootStar I v
    · simp only [L, ite_eq_left hx, Finset.mem_singleton, hstarS x hx]
    · simpa only [L, ite_eq_right hx] using hcS x
  have hT : ∀ x : T, cT x ∈ L x.1 := by
    intro x
    by_cases hx : x.1 ∈ rootStar I v
    · simp only [L, ite_eq_left hx, Finset.mem_singleton, hstarT x hx]
    · simpa only [L, ite_eq_right hx] using hcT x
  obtain ⟨c, hc⟩ := glue_induced_colourings S T L hcover hedges cS cT hS hT hagree
  have hag : ∀ x ∈ rootStar I v, c x = f x := by
    intro x hx
    exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, hag⟩
  intro x
  by_cases hx : x ∈ rootStar I v
  · rw [hag x hx]
    exact hf x hx
  · simpa only [L, ite_eq_right hx] using hc x

/-- A strict cut whose separator lies in the fixed root-star is solved by
root-star induction on its two smaller actual induced vertex types. -/
theorem rootStar_extension_of_star_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ)
    (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I v)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  have hNoP : ∀ x, x ∉ I.precolor.vertices := by
    intro x
    simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true]
  let JS := I.induceUnprecolored S hSconn (fun x _ => hNoP x)
  let JT := I.induceUnprecolored T hTconn (fun x _ => hNoP x)
  have hSv : ∀ x : S, x ∈ rootStar JS ⟨v, hvS⟩ ↔ x.1 ∈ rootStar I v := by
    intro x
    change (x = ⟨v, hvS⟩ ∨ G.Adj v x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
    simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  have hTv : ∀ x : T, x ∈ rootStar JT ⟨v, hvT⟩ ↔ x.1 ∈ rootStar I v := by
    intro x
    change (x = ⟨v, hvT⟩ ∨ G.Adj v x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
    simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  obtain ⟨cS, hcS, haS⟩ := hroot S (G.induce S) JS rfl hSconn ⟨v, hvS⟩
    (I.induceUnprecolored_on_old_face S hSconn _ _ hv) (fun x => f x.1)
    (fun x hx => hf x.1 ((hSv x).1 hx))
    (fun x hx y hy hxy => hproper x.1 ((hSv x).1 hx) y.1 ((hSv y).1 hy) hxy) hSsmall
  obtain ⟨cT, hcT, haT⟩ := hroot T (G.induce T) JT rfl hTconn ⟨v, hvT⟩
    (I.induceUnprecolored_on_old_face T hTconn _ _ hv) (fun x => f x.1)
    (fun x hx => hf x.1 ((hTv x).1 hx))
    (fun x hx y hy hxy => hproper x.1 ((hTv x).1 hx) y.1 ((hTv y).1 hy) hxy) hTsmall
  apply I.rootStar_extension_of_induced_colourings v f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS hcT
    (fun x hx => haS x ((hSv x).2 hx)) (fun x hx => haT x ((hTv x).2 hx))
  intro x hx hy
  have hstar := hinter x ⟨hx, hy⟩
  exact (haS ⟨x, hx⟩ ((hSv _).2 hstar)).trans (haT ⟨x, hy⟩ ((hTv _).2 hstar)).symm

/-- Choose an empty-prescription instance on a cut piece with its attachment
vertex on the selected face. Interior attachments use the piece's three-lists. -/
lemma exists_empty_cut_instance_with_root (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (T : Set V) [Nontrivial T] (hconn : (G.induce T).Preconnected) (w : T)
    (hboundary : OnOuterFace I.embedding I.outer w.1 ∨ ∀ x : T, 3 ≤ (I.lists x.1).card) :
    ∃ J : BoundaryInstance (G.induce T) C, J.precolor = .empty ∧
      (∀ x : T, J.lists x = I.lists x.1) ∧ OnOuterFace J.embedding J.outer w := by
  rcases hboundary with hw | hthree
  · let J := I.induceUnprecolored T hconn (fun _ _ => by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
    exact ⟨J, rfl, fun _ => rfl, I.induceUnprecolored_on_old_face T hconn _ w hw⟩
  · obtain ⟨z, hwz⟩ := hconn.exists_adj_of_nontrivial w
    let o : (G.induce T).Dart := ⟨(w, z), hwz⟩
    let J := BoundaryInstance.of_three_lists (inducedPlaneMap I.embedding T) o
      (five_le_egirth_induce T I.girth) (fun x => I.lists x.1) hthree (fun x => I.prescribed x.1)
    exact ⟨J, rfl, fun _ => rfl, onOuterFace_self _ o⟩

/-- At a cut away from the root, colour the root side with its full fixed star,
then extend from the attachment vertex in the other smaller piece. -/
theorem rootStar_extension_of_root_side_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (hvS : v ∈ S) (hstarS : ∀ x ∈ rootStar I v, x ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  let JS := I.induceUnprecolored S hSconn (fun _ _ => by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
  have hSv : ∀ x : S, x ∈ rootStar JS ⟨v, hvS⟩ ↔ x.1 ∈ rootStar I v := by
    intro x
    change (x = ⟨v, hvS⟩ ∨ G.Adj v x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
    simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  obtain ⟨cS, hcS, haS⟩ := hroot S (G.induce S) JS rfl hSconn ⟨v, hvS⟩
    (I.induceUnprecolored_on_old_face S hSconn _ _ hv) (fun x => f x.1)
    (fun x hx => hf x.1 ((hSv x).1 hx))
    (fun x hx y hy hxy => hproper x.1 ((hSv x).1 hx) y.1 ((hSv y).1 hy) hxy) hSsmall
  obtain ⟨JT, hPT, hLT, hwface⟩ := I.exists_empty_cut_instance_with_root hP T hTconn ⟨w, hwT⟩ hboundary
  have hwcol : cS ⟨w, hwS⟩ ∈ JT.lists ⟨w, hwT⟩ := by rw [hLT]; exact hcS ⟨w, hwS⟩
  obtain ⟨g, hgw, hg, hgproper⟩ := JT.exists_rootStar_colours hPT ⟨w, hwT⟩ (cS ⟨w, hwS⟩) hwcol
  obtain ⟨cT, hcT, haT⟩ := hroot T (G.induce T) JT hPT hTconn ⟨w, hwT⟩ hwface g hg hgproper hTsmall
  have hwagree : cT ⟨w, hwT⟩ = cS ⟨w, hwS⟩ := (haT _ (Or.inl rfl)).trans hgw
  have hstarS' : ∀ x : S, x.1 ∈ rootStar I v → cS x = f x.1 := fun x hx => haS x ((hSv x).2 hx)
  have hstarT : ∀ x : T, x.1 ∈ rootStar I v → cT x = f x.1 := by
    intro x hx
    have heq : x.1 = w := by
      have h : x.1 ∈ S ∩ T := ⟨hstarS x.1 hx, x.2⟩
      rwa [hinter] at h
    have hxeq : x = ⟨w, hwT⟩ := Subtype.ext heq
    rw [hxeq, hwagree]
    exact hstarS' ⟨w, hwS⟩ (heq ▸ hx)
  apply I.rootStar_extension_of_induced_colourings v f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS
    (fun x => by rw [← hLT]; exact hcT x) hstarS' hstarT
  intro x hx hy
  have hxw : x = w := by have h : x ∈ S ∩ T := ⟨hx, hy⟩; rwa [hinter] at h
  subst x
  exact hwagree.symm

/-- Root-star extension survives every cutvertex by strict induction. This is
an auxiliary induction for graphs already smaller than the main instance. -/
theorem rootStar_extension_of_cutvertex (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  obtain ⟨S, hwS, hvS, ⟨a, ha, haw⟩, ⟨b, hb⟩, hsep⟩ := exists_cut_side_containing w v hdisc
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
  have hSsmall := card_induced_vertices_lt S hb
  have hTsmall := card_induced_vertices_lt T haT
  by_cases hvw : v = w
  · subst w
    apply I.rootStar_extension_of_star_cut hP v hv f hf hproper S T hvS hwT hcover
      ?_ hedges hSc hTc hSsmall hTsmall hroot
    intro x hx
    have hxv : x = v := by rwa [hinter] at hx
    exact Or.inl hxv
  · have hstarS : ∀ x ∈ rootStar I v, x ∈ S := by
      intro x hx
      rcases hx with rfl | ⟨hvx, _⟩
      · exact hvS
      · by_cases hxw : x = w
        · exact hxw ▸ hwS
        · exact (hsep hvx hvw hxw).1 hvS
    have hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card := by
      by_cases hwface : OnOuterFace I.embedding I.outer w
      · exact Or.inl hwface
      · refine Or.inr (fun x => I.interior_lists x.1 ?_)
        intro hxface
        have hpath : RIn G ({w} : Set V)ᶜ v x.1 := ((onOuterFace_connSet I.embedding I.outer).2 v hv x.1 hxface).mono_set
          (fun z hz h => hwface (h ▸ hz))
        have hxS := (rIn_side_of_avoids_cut hsep hpath).1 hvS
        rcases x.2 with hxw | hxout
        · exact hwface (hxw ▸ hxface)
        · exact hxout hxS
    exact I.rootStar_extension_of_root_side_cut hP v hv f hf hproper S T w hwS hwT hvS
      hstarS hcover hinter hedges hSc hTc hboundary hSsmall hTsmall hroot

end BoundaryInstance
end Thomassen
