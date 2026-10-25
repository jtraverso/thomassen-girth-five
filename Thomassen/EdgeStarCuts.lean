/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStar
public import Thomassen.FacialChordNormalization

/-! Edge-star extension through smaller induced pieces. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

omit [Fintype V] in
/-- Glue original list colourings while preserving the full fixed edge-star. -/
lemma edgeStar_extension_of_induced_colourings (I : BoundaryInstance G C) (a b : V) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (S T : Set V) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x : S, cS x ∈ I.lists x.1) (hcT : ∀ x : T, cT x ∈ I.lists x.1)
    (hstarS : ∀ x : S, x.1 ∈ edgeStar I a b → cS x = f x.1)
    (hstarT : ∀ x : T, x.1 ∈ edgeStar I a b → cT x = f x.1)
    (hagree : ∀ x (hx : x ∈ S) (hy : x ∈ T), cS ⟨x, hx⟩ = cT ⟨x, hy⟩) :
    EdgeStarExtension I a b f := by
  let L : V → Finset C := fun x => if x ∈ edgeStar I a b then {f x} else I.lists x
  have hS : ∀ x : S, cS x ∈ L x.1 := by
    intro x
    by_cases hx : x.1 ∈ edgeStar I a b
    · simp only [L, ite_eq_left hx, Finset.mem_singleton, hstarS x hx]
    · simpa only [L, ite_eq_right hx] using hcS x
  have hT : ∀ x : T, cT x ∈ L x.1 := by
    intro x
    by_cases hx : x.1 ∈ edgeStar I a b
    · simp only [L, ite_eq_left hx, Finset.mem_singleton, hstarT x hx]
    · simpa only [L, ite_eq_right hx] using hcT x
  obtain ⟨c, hc⟩ := glue_induced_colourings S T L hcover hedges cS cT hS hT hagree
  have hag : ∀ x ∈ edgeStar I a b, c x = f x := by
    intro x hx
    exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, hag⟩
  intro x
  by_cases hx : x ∈ edgeStar I a b
  · rw [hag x hx]
    exact hf x hx
  · simpa only [L, ite_eq_right hx] using hc x


/-- Apply the strict edge-star induction to one actual induced piece. -/
lemma edgeStar_colouring_on_smaller_induced (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S : Set V) [Nontrivial S] (haS : a ∈ S) (hbS : b ∈ S)
    (hconn : (G.induce S).Preconnected) (hSsmall : Nat.card S < Nat.card V)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ edgeStar I a b → c x = f x.1 := by
  let J := I.induceUnprecolored S hconn (fun _ _ => by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
  have hstar : ∀ x : S, x ∈ edgeStar J ⟨a, haS⟩ ⟨b, hbS⟩ ↔ x.1 ∈ edgeStar I a b := by
    intro x
    change ((x = ⟨a, haS⟩ ∨ G.Adj a x.1 ∧ (I.lists x.1).card ≤ 2) ∨
      (x = ⟨b, hbS⟩ ∨ G.Adj b x.1 ∧ (I.lists x.1).card ≤ 2)) ↔ _
    simp only [edgeStar, Set.mem_union, rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  obtain ⟨c, hc, hg⟩ := hedge S (G.induce S) J rfl hconn ⟨a, haS⟩ ⟨b, hbS⟩ hab
    (I.induceUnprecolored_on_old_face S hconn _ _ ha) (I.induceUnprecolored_on_old_face S hconn _ _ hb)
    (fun x => f x.1) (fun x hx => hf x.1 ((hstar x).1 hx))
    (fun x hx y hy hxy => hproper x.1 ((hstar x).1 hx) y.1 ((hstar y).1 hy) hxy) hSsmall
  exact ⟨c, hc, fun x hx => hg x ((hstar x).2 hx)⟩

/-- If both edge ends belong to both pieces and the separator is fixed,
apply the edge-star induction to the two strictly smaller graphs. -/
theorem edgeStar_extension_of_edge_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (haS : a ∈ S) (hbS : b ∈ S) (haT : a ∈ T) (hbT : b ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ edgeStar I a b)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  obtain ⟨cS, hcS, hgS⟩ := I.edgeStar_colouring_on_smaller_induced hP a b hab ha hb f hf hproper S haS hbS hSc hSsmall hedge
  obtain ⟨cT, hcT, hgT⟩ := I.edgeStar_colouring_on_smaller_induced hP a b hab ha hb f hf hproper T haT hbT hTc hTsmall hedge
  apply I.edgeStar_extension_of_induced_colourings a b f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS hcT hgS hgT
  intro x hx hy
  have hstar := hinter x ⟨hx, hy⟩
  exact (hgS ⟨x, hx⟩ hstar).trans (hgT ⟨x, hy⟩ hstar).symm

/-- If the other piece has a single fixed-root fan, its complete auxiliary
induction supplies all separator colours without another edge-star hypothesis. -/
theorem edgeStar_extension_of_root_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (haS : a ∈ S) (hbS : b ∈ S) (r : V) (hr : OnOuterFace I.embedding I.outer r)
    (hrT : r ∈ T) (hrootSub : ∀ x ∈ rootStar I r, x ∈ edgeStar I a b)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I r)
    (hstarT : ∀ x ∈ T, x ∈ edgeStar I a b → x ∈ rootStar I r)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  obtain ⟨cS, hcS, hgS⟩ := I.edgeStar_colouring_on_smaller_induced hP a b hab ha hb f hf hproper S haS hbS hSc hSsmall hedge
  let J := I.induceUnprecolored T hTc (fun _ _ => by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
  have hTv : ∀ x : T, x ∈ rootStar J ⟨r, hrT⟩ ↔ x.1 ∈ rootStar I r := by
    intro x
    change (x = ⟨r, hrT⟩ ∨ G.Adj r x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
    simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  obtain ⟨cT, hcT, hgT⟩ := J.rootStar_extension_of_smaller N hsmall rfl hTc ⟨r, hrT⟩
    (I.induceUnprecolored_on_old_face T hTc _ _ hr) (fun x => f x.1)
    (fun x hx => hf x.1 (hrootSub x.1 ((hTv x).1 hx)))
    (fun x hx y hy hxy => hproper x.1 (hrootSub x.1 ((hTv x).1 hx)) y.1 (hrootSub y.1 ((hTv y).1 hy)) hxy)
    (hTsmall.trans hN)
  apply I.edgeStar_extension_of_induced_colourings a b f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS hcT hgS
    (fun x hx => hgT x ((hTv x).2 (hstarT x.1 x.2 hx)))
  intro x hx hy
  have hroot := hinter x ⟨hx, hy⟩
  exact (hgS ⟨x, hx⟩ (hrootSub x hroot)).trans (hgT ⟨x, hy⟩ ((hTv ⟨x, hy⟩).2 hroot)).symm

/-- A cut away from the fixed edge leaves only its attachment colour in the
other piece. That piece is handled by the completed one-root fan induction. -/
theorem edgeStar_extension_of_separate_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (haS : a ∈ S) (hbS : b ∈ S) (hstarS : ∀ x ∈ edgeStar I a b, x ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  obtain ⟨cS, hcS, hgS⟩ := I.edgeStar_colouring_on_smaller_induced hP a b hab ha hb f hf hproper
    S haS hbS hSconn hSsmall hedge
  obtain ⟨JT, hPT, hLT, hwface⟩ := I.exists_empty_cut_instance_with_root hP T hTconn ⟨w, hwT⟩ hboundary
  have hwcol : cS ⟨w, hwS⟩ ∈ JT.lists ⟨w, hwT⟩ := by rw [hLT]; exact hcS ⟨w, hwS⟩
  obtain ⟨g, hgw, hg, hgproper⟩ := JT.exists_rootStar_colours hPT ⟨w, hwT⟩ (cS ⟨w, hwS⟩) hwcol
  obtain ⟨cT, hcT, haT⟩ := JT.rootStar_extension_of_smaller N hsmall hPT hTconn ⟨w, hwT⟩ hwface g hg hgproper (hTsmall.trans hN)
  have hwagree : cT ⟨w, hwT⟩ = cS ⟨w, hwS⟩ := (haT _ (Or.inl rfl)).trans hgw
  have hstarS' : ∀ x : S, x.1 ∈ edgeStar I a b → cS x = f x.1 := hgS
  have hstarT : ∀ x : T, x.1 ∈ edgeStar I a b → cT x = f x.1 := by
    intro x hx
    have heq : x.1 = w := by
      have h : x.1 ∈ S ∩ T := ⟨hstarS x.1 hx, x.2⟩
      rwa [hinter] at h
    have hxeq : x = ⟨w, hwT⟩ := Subtype.ext heq
    rw [hxeq, hwagree]
    exact hstarS' ⟨w, hwS⟩ (heq ▸ hx)
  apply I.edgeStar_extension_of_induced_colourings a b f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS
    (fun x => by rw [← hLT]; exact hcT x) hstarS' hstarT
  intro x hx hy
  have hxw : x = w := by have h : x ∈ S ∩ T := ⟨hx, hy⟩; rwa [hinter] at h
  subst x
  exact hwagree.symm


end BoundaryInstance
end Thomassen
