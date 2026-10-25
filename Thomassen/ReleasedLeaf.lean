/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedPathPrecolor

/-! Releasing one prescribed leaf while fixing an adjacent separator root. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- The private prescribed leaf gets the two-list consisting of its old colour
and its prescribed neighbour's colour. Fixing that neighbour later forces the
leaf's original colour. The empty instance satisfies every short-edge condition. -/
lemma exists_empty_induced_releasing_leaf (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (a b t : V) (haS : a ∈ S) (hbS : b ∈ S)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (htP : t ∈ I.precolor.vertices)
    (hat : G.Adj a t) (htb : t ≠ b)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b ∨ x = t)
    (F : Finset C) (hF : 3 ≤ F.card) :
    ∃ J : BoundaryInstance (G.induce S) C, J.precolor = .empty ∧
      (∀ x : S, x.1 ≠ a → x.1 ≠ b → J.lists x =
        if x.1 = t then {I.prescribed t, I.prescribed a} else I.lists x.1) ∧
      (∀ x : S, I.lists x.1 ⊆ J.lists x) ∧
      OnOuterFace J.embedding J.outer ⟨a, haS⟩ ∧ OnOuterFace J.embedding J.outer ⟨b, hbS⟩ := by
  obtain ⟨o, ho⟩ := exists_outer_induced_of_preconnected I.embedding I.outer S hconn
  have hta : t ≠ a := hat.ne.symm
  have hcol : I.prescribed t ≠ I.prescribed a := (I.proper_on_precolored_vertices haP htP hat).symm
  let L : S → Finset C := fun x => if x.1 = a ∨ x.1 = b then I.lists x.1 ∪ F
    else if x.1 = t then {I.prescribed t, I.prescribed a} else I.lists x.1
  have hroot : ∀ x : S, x.1 = a ∨ x.1 = b → 3 ≤ (L x).card := by
    intro x hx
    simp only [L, ite_eq_left hx]
    exact hF.trans (Finset.card_le_card Finset.subset_union_right)
  have hleaf : ∀ x : S, x.1 = t → L x = {I.prescribed t, I.prescribed a} := by
    intro x hx
    simp [L, hx, hta, htb]
  have hsub : ∀ x : S, I.lists x.1 ⊆ L x := by
    intro x
    by_cases hr : x.1 = a ∨ x.1 = b
    · simp only [L, ite_eq_left hr]
      exact Finset.subset_union_left
    · by_cases ht : x.1 = t
      · rw [hleaf x ht, ht, I.singleton t htP]
        exact Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)
      · simp only [L, ite_eq_right hr, ite_eq_right ht]
        intro c hc
        exact hc
  have hNoP : ∀ x : S, x.1 ≠ a → x.1 ≠ b → x.1 ≠ t → x.1 ∉ I.precolor.vertices := by
    intro x hxa hxb hxt hxP
    exact (hPcap x.1 x.2 hxP).elim hxa (fun h => h.elim hxb hxt)
  have holdshort : ∀ x : S, ¬ (x.1 = a ∨ x.1 = b) → (L x).card ≤ 2 → (I.lists x.1).card ≤ 2 := by
    intro x hr hx
    by_cases ht : x.1 = t
    · simp [ht, I.singleton t htP]
    · simpa only [L, ite_eq_right hr, ite_eq_right ht] using hx
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := o
    precolor := .empty
    lists := L
    prescribed := fun x => I.prescribed x.1
    on_outer := by simp
    singleton := by simp
    proper_precolor := by simp
    boundary_lists := by
      intro x _ _
      by_cases hr : x.1 = a ∨ x.1 = b
      · exact (by decide : 2 ≤ 3).trans (hroot x hr)
      · by_cases ht : x.1 = t
        · rw [hleaf x ht, Finset.card_pair hcol]
        · simpa only [L, ite_eq_right hr, ite_eq_right ht] using
            I.outside_precolor_list_ge_two (hNoP x (not_or.1 hr).1 (not_or.1 hr).2 ht)
    interior_lists := by
      intro x hx
      by_cases hr : x.1 = a ∨ x.1 = b
      · exact hroot x hr
      · have ht : x.1 ≠ t := fun ht => hx (ho x (ht ▸ I.on_outer t htP))
        simpa only [L, ite_eq_right hr, ite_eq_right ht] using
          I.interior_lists x.1 (fun h => hx (ho x h))
    short_edges := by
      intro x y hxy hx hy
      have hxr : ¬ (x.1 = a ∨ x.1 = b) := fun h => by have h := hroot x h; omega
      have hyr : ¬ (y.1 = a ∨ y.1 = b) := fun h => by have h := hroot y h; omega
      have he := I.short_edges hxy (holdshort x hxr hx) (holdshort y hyr hy)
      have hends := I.precolor.endpoints_of_mem_edges he
      have hxt : x.1 = t := (hPcap x.1 x.2 hends.1).resolve_left (not_or.1 hxr).1
        |>.resolve_left (not_or.1 hxr).2
      have hyt : y.1 = t := (hPcap y.1 y.2 hends.2).resolve_left (not_or.1 hyr).1
        |>.resolve_left (not_or.1 hyr).2
      exact (hxy.ne (Subtype.ext (hxt.trans hyt.symm))).elim }
  refine ⟨J, rfl, ?_, hsub, ho _ ha, ho _ hb⟩
  intro x hxa hxb
  exact ite_eq_right (not_or.2 ⟨hxa, hxb⟩)

end BoundaryInstance
end Thomassen
