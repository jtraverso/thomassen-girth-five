/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFan

/-! Strict cuts for a fan attached to a short original prescription. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical

/-- The recursive fan obligation, with its own strictly smaller vertex bound.
The old prescription has at most three vertices and is adjacent to the root. -/
def AnchoredFanBelow (C : Type v) (n : ℕ) : Prop :=
  ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
    J.precolor.vertices.card ≤ 3 → ∀ b : W, b ∉ J.precolor.vertices →
    (∃ a ∈ J.precolor.vertices, H.Adj b a) → H.Preconnected →
    OnOuterFace J.embedding J.outer b → ∀ f : W → C,
    (∀ x ∈ rootStar J b, f x ∈ J.lists x) →
    (∀ x ∈ rootStar J b, ∀ y ∈ rootStar J b, H.Adj x y → f x ≠ f y) →
    Nat.card W < n → RootStarExtension J b f

variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

omit [Fintype V] in
/-- Restriction decreases the number of original prescribed vertices. -/
lemma induced_precolor_card_le (I : BoundaryInstance G C) (S : Set V)
    (Q : BoundaryPrecolor (G.induce S))
    (hv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ I.precolor.vertices) :
    Q.vertices.card ≤ I.precolor.vertices.card := by
  have hsub : Q.vertices.image Subtype.val ⊆ I.precolor.vertices := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact (hv y).1 hy
  have h := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h

/-- Apply the auxiliary strict induction on an exact induced prescription.
All root-star memberships and colours are transported from the original graph. -/
lemma anchoredFan_on_induced (I : BoundaryInstance G C) (hcard : I.precolor.vertices.card ≤ 3)
    (b : V) (hbP : b ∉ I.precolor.vertices) (hbface : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hp : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    (S : Set V) [Nontrivial S] (hSc : (G.induce S).Preconnected) (hbS : b ∈ S)
    (ha : ∃ a ∈ S, a ∈ I.precolor.vertices ∧ G.Adj b a)
    (Q : BoundaryPrecolor (G.induce S))
    (hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hQe : ∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (hSsmall : Nat.card S < Nat.card V) (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) :
    ∃ cS : (G.induce S).Coloring C, (∀ x : S, cS x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ rootStar I b → cS x = f x.1 := by
  let J := I.inducePrecolor S hSc Q hQv hQe
  have hstar : ∀ x : S, x ∈ rootStar J ⟨b, hbS⟩ ↔ x.1 ∈ rootStar I b := by
    intro x
    change (x = ⟨b, hbS⟩ ∨ G.Adj b x.1 ∧ (I.lists x.1).card ≤ 2) ↔ _
    simp only [rootStar, Set.mem_ofPred_eq, Subtype.ext_iff]
  have hface : OnOuterFace J.embedding J.outer ⟨b, hbS⟩ :=
    (exists_outer_induced_of_preconnected I.embedding I.outer S hSc).choose_spec _ hbface
  obtain ⟨a, haS, haP, hba⟩ := ha
  obtain ⟨c, hc, hag⟩ := hfan S (G.induce S) J ((I.induced_precolor_card_le S Q hQv).trans hcard)
    ⟨b, hbS⟩ (fun h => hbP ((hQv _).1 h)) ⟨⟨a, haS⟩, (hQv _).2 haP, hba⟩ hSc hface
    (fun x => f x.1) (fun x hx => hf x.1 ((hstar x).1 hx))
    (fun x hx y hy hxy => hp x.1 ((hstar x).1 hx) y.1 ((hstar y).1 hy) hxy) hSsmall
  exact ⟨c, hc, fun x hx => hag x ((hstar x).2 hx)⟩

/-- An auxiliary spoke piece containing no private original prescription is
solved by the already verified two-endpoint fan theorem. The fixed spoke is
short in the original instance, so no extra fixed colours are invented. -/
lemma rootStar_on_released_spoke_piece (I : BoundaryInstance G C)
    (b x : V) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (hxface : OnOuterFace I.embedding I.outer x)
    (hb3 : 3 ≤ (I.lists b).card) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (T : Set V) [Nontrivial T] (hTc : (G.induce T).Preconnected) (hbT : b ∈ T) (hxT : x ∈ T)
    (hPcap : ∀ y ∈ T, y ∈ I.precolor.vertices → y = b ∨ y = x)
    (N : ℕ) (hTsmall : Nat.card T < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) :
    ∃ cT : (G.induce T).Coloring C, (∀ y : T, cT y ∈ I.lists y.1) ∧
      ∀ y : T, y.1 ∈ rootStar I b → cT y = f y.1 := by
  obtain ⟨J, hJP, hsame, hsub, hbJ, hxJ⟩ := I.exists_empty_induced_releasing_edge T hTc b x hbT hxT
    hbface hxface hPcap (I.lists b) hb3
  have hxstar : x ∈ rootStar I b := Or.inr ⟨hbx, hxs⟩
  have hstar : ∀ y : T, y ∈ edgeStar J ⟨b, hbT⟩ ⟨x, hxT⟩ → y.1 ∈ rootStar I b := by
    intro y hy
    rcases hy with (hy | hy) | (hy | hy)
    · exact Or.inl (congrArg Subtype.val hy)
    · exact Or.inr ⟨hy.1, (Finset.card_le_card (hsub y)).trans hy.2⟩
    · exact congrArg Subtype.val hy ▸ hxstar
    · have he := I.short_edges hy.1 hxs ((Finset.card_le_card (hsub y)).trans hy.2)
      rcases hPcap y.1 y.2 (I.precolor.endpoints_of_mem_edges he).2 with hyb | hyx
      · exact Or.inl hyb
      · exact (hy.1.ne (Subtype.ext hyx.symm)).elim
  obtain ⟨c, hc, hag⟩ := J.edgeStar_extension_of_smaller N hsmall hJP hTc ⟨b, hbT⟩ ⟨x, hxT⟩ hbx hbJ hxJ
    (fun y => f y.1) (fun y hy => hsub y (hf y.1 (hstar y hy)))
    (fun y hy z hz hyz => hp y.1 (hstar y hy) z.1 (hstar z hz) hyz) hTsmall
  have holdstar : ∀ y : T, y.1 ∈ rootStar I b → y ∈ edgeStar J ⟨b, hbT⟩ ⟨x, hxT⟩ := by
    intro y hy
    by_cases hyb : y.1 = b
    · exact Or.inl (Or.inl (Subtype.ext hyb))
    · by_cases hyx : y.1 = x
      · exact Or.inr (Or.inl (Subtype.ext hyx))
      · exact Or.inl (Or.inr ⟨hy.resolve_left hyb |>.1, by
          rw [hsame y hyb hyx]
          exact (hy.resolve_left hyb).2⟩)
  have hagree : ∀ y : T, y.1 ∈ rootStar I b → c y = f y.1 := fun y hy => hag y (holdstar y hy)
  refine ⟨c, ?_, hagree⟩
  intro y
  by_cases hyb : y.1 = b
  · rw [hagree y (Or.inl hyb)]
    exact hf y.1 (Or.inl hyb)
  · by_cases hyx : y.1 = x
    · have hy : y.1 ∈ rootStar I b := hyx ▸ hxstar
      rw [hagree y hy]
      exact hf y.1 hy
    · have h := hc y
      rwa [hsame y hyb hyx] at h

omit [Fintype V] in
/-- A nonempty prescription on at most three vertices is an actual path of
at most two edges; girth five rules out the cycle constructor. -/
lemma exists_short_prescribed_path (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (hne : ∃ x, x ∈ I.precolor.vertices) :
    ∃ a t, ∃ p : G.Walk a t, ∃ hp : p.IsPath, ∃ hn : p.support.toFinset.card ≤ 6,
      I.precolor = .path p hp hn ∧ p.length ≤ 2 := by
  cases hP : I.precolor with
  | empty => simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, exists_false] at hne
  | path p hp hn =>
    refine ⟨_, _, p, hp, hn, rfl, ?_⟩
    simp only [hP, BoundaryPrecolor.vertices, List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hcard
    omega
  | cycle p hp hn =>
    have hlen := five_le_egirth_iff.1 I.girth _ p hp
    simp only [hP, BoundaryPrecolor.vertices, cycle_support_card_eq_length p hp] at hcard
    omega

/-- Split through prescribed separator vertices, keeping the root in one
piece. The other piece uses the main induction and the original singleton
colours; the auxiliary fan hypothesis is invoked only on the smaller root piece. -/
theorem anchoredFan_extension_of_prescribed_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hp : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (hbS : b ∈ S) (hbT : b ∉ T)
    (ha : ∃ a ∈ S, a ∈ I.precolor.vertices ∧ G.Adj b a)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ I.precolor.vertices)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (QS : BoundaryPrecolor (G.induce S))
    (hSv : ∀ x : S, x ∈ QS.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hSe : ∀ x y : S, s(x, y) ∈ QS.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (QT : BoundaryPrecolor (G.induce T))
    (hTv : ∀ x : T, x ∈ QT.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hTe : ∀ x y : T, s(x, y) ∈ QT.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  obtain ⟨cS, hcS, hgS⟩ := I.anchoredFan_on_induced hcard b hbP hbface f hf hp S hSc hbS ha QS hSv hSe hSsmall hfan
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.inducePrecolor T hTc QT hTv hTe) (hTsmall.trans hN)
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcT
  have hstarT : ∀ x : T, x.1 ∈ rootStar I b → cT x = f x.1 := by
    intro x hx
    have hxP : x.1 ∈ I.precolor.vertices := by
      rcases hx with hxb | hx
      · exact (hbT (hxb ▸ x.2)).elim
      · rcases hedges hx.1 with h | h
        · exact hinter x.1 ⟨h.2, x.2⟩
        · exact (hbT h.1).elim
    have hc : cT x = I.prescribed x.1 := Finset.mem_singleton.1
      (by simpa only [I.singleton x.1 hxP] using hT x)
    have hfx : f x.1 = I.prescribed x.1 := Finset.mem_singleton.1
      (by simpa only [I.singleton x.1 hxP] using hf x.1 hx)
    exact hc.trans hfx.symm
  apply I.rootStar_extension_of_induced_colourings b f hf S T
    (fun x => by have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT hcS hT hgS hstarT
  intro x hxS hxT
  have hxP := hinter x ⟨hxS, hxT⟩
  have hs : cS ⟨x, hxS⟩ = I.prescribed x := Finset.mem_singleton.1
    (by simpa only [I.singleton x hxP] using hcS ⟨x, hxS⟩)
  have ht : cT ⟨x, hxT⟩ = I.prescribed x := Finset.mem_singleton.1
    (by simpa only [I.singleton x hxP] using hT ⟨x, hxT⟩)
  exact hs.trans ht.symm

/-- A spoke cut meeting the prescription is handled recursively on its two
exact prescribed branches. No original singleton is released in this case. -/
theorem anchoredFan_extension_of_prescribed_spoke_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (hxP : x ∈ I.precolor.vertices) (hbx : G.Adj b x)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  have hbST : b ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hxST : x ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
  let : Nontrivial S := (show (G.induce S).Adj ⟨b, hbST.1⟩ ⟨x, hxST.1⟩ from hbx).nontrivial
  let : Nontrivial T := (show (G.induce T).Adj ⟨b, hbST.2⟩ ⟨x, hxST.2⟩ from hbx).nontrivial
  obtain ⟨a, t, p, hpath, hn, hP, _⟩ := I.exists_short_prescribed_path hcard ⟨x, hxP⟩
  obtain ⟨QS, hSv, hSe⟩ := exists_induce_path_two_cut I.precolor p hpath hn hP hxST.1 hxP b hbP
    (fun {_ _} hxy hxx hxb hyx hyb => edge_cut_side_constancy S T b x hinter hedges hxy hxb hxx hyb hyx)
  obtain ⟨QT, hTv, hTe⟩ := exists_induce_path_two_cut I.precolor p hpath hn hP hxST.2 hxP b hbP
    (fun {_ _} hxy hxx hxb hyx hyb => edge_cut_side_constancy T S b x (by rwa [Set.inter_comm])
      (fun {_ _} h => (hedges h).symm) hxy hxb hxx hyb hyx)
  obtain ⟨cS, hcS, hgS⟩ := I.anchoredFan_on_induced hcard b hbP hbface f hf hp S hSc.preconnected hbST.1
    ⟨x, hxST.1, hxP, hbx⟩ QS hSv hSe hSsmall hfan
  obtain ⟨cT, hcT, hgT⟩ := I.anchoredFan_on_induced hcard b hbP hbface f hf hp T hTc.preconnected hbST.2
    ⟨x, hxST.2, hxP, hbx⟩ QT hTv hTe hTsmall hfan
  apply I.rootStar_extension_of_induced_colourings b f hf S T
    (fun y => by have h := Set.mem_univ y; rwa [← hcover] at h) hedges cS cT hcS hcT hgS hgT
  intro y hyS hyT
  have hy : y ∈ S ∩ T := ⟨hyS, hyT⟩
  rw [hinter] at hy
  have hystar : y ∈ rootStar I b := hy.elim (fun h => Or.inl h)
    (fun h => Or.inr ⟨Set.mem_singleton_iff.1 h ▸ hbx,
      by simp [Set.mem_singleton_iff.1 h, I.singleton x hxP]⟩)
  exact (hgS ⟨y, hyS⟩ hystar).trans (hgT ⟨y, hyT⟩ hystar).symm

end BoundaryInstance
end Thomassen
