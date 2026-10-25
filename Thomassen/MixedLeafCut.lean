/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ReleasedLeaf

/-! Complete mixed-edge-cut reduction with one private prescribed leaf. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A mixed edge cut is closed when one piece has only one private prescribed
vertex, adjacent to the prescribed separator end. Prescriptions elsewhere in the
other piece retain their exact native path and original singleton lists. -/
theorem colourable_of_mixed_leaf_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b t : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    (htP : t ∈ I.precolor.vertices) (hat : G.Adj a t)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = t)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
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
  obtain ⟨QT, hQTverts, hQTedges⟩ := exists_induce_path_two_cut I.precolor p hp hn hP haT haP b hbP
    (edge_cut_side_constancy T S a b (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm))
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T)
    (I.inducePrecolor T hTc.preconnected QT hQTverts hQTedges) hTsmall
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcT
  have hcaP : cT ⟨a, haT⟩ = I.prescribed a := by
    have h := hT ⟨a, haT⟩
    rwa [I.singleton a haP, Finset.mem_singleton] at h
  have hF : 3 ≤ (I.lists b).card := by
    by_contra h
    have he := I.short_edges hab (by simp [I.singleton a haP]) (by omega)
    exact hbP (I.precolor.endpoints_of_mem_edges he).2
  obtain ⟨J, hPJ, hUnchanged, hSub, haFace, hbFace⟩ :=
    I.exists_empty_induced_releasing_leaf S hSc.preconnected a b t haS hbS ha hb haP htP hat
      (fun h => hbP (h ▸ htP)) (fun x hx hxP => (hPcap x hx hxP).imp_right Or.inr) (I.lists b) hF
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
        rw [hUnchanged x hxa hxb] at hc
        by_cases hxt : x.1 = t
        · rw [ite_eq_left hxt, Finset.mem_insert, Finset.mem_singleton] at hc
          have hadj : (G.induce S).Adj ⟨a, haS⟩ x := by change G.Adj a x.1; rwa [hxt]
          have hne : cS x ≠ I.prescribed a := by
            rw [← hcaP, ← hca]
            exact (cS.valid hadj).symm
          have hct : cS x = I.prescribed t := hc.resolve_right hne
          rw [hxt, I.singleton t htP, Finset.mem_singleton]
          exact hct
        · rwa [ite_eq_right hxt] at hc
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
