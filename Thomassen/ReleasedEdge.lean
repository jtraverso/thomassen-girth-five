/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarChoice

/-! Releasing singleton separator lists before prescribing their actual colours. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- If only the separator ends are originally prescribed in an induced piece,
enlarge their lists to three colours and retain every other original list.
Fixing the actual separator colours afterwards restores the original lists. -/
lemma exists_empty_induced_releasing_edge (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (a b : V) (haS : a ∈ S) (hbS : b ∈ S)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b)
    (F : Finset C) (hF : 3 ≤ F.card) :
    ∃ J : BoundaryInstance (G.induce S) C, J.precolor = .empty ∧
      (∀ x : S, x.1 ≠ a → x.1 ≠ b → J.lists x = I.lists x.1) ∧
      (∀ x : S, I.lists x.1 ⊆ J.lists x) ∧
      OnOuterFace J.embedding J.outer ⟨a, haS⟩ ∧ OnOuterFace J.embedding J.outer ⟨b, hbS⟩ := by
  obtain ⟨o, ho⟩ := exists_outer_induced_of_preconnected I.embedding I.outer S hconn
  let L : S → Finset C := fun x => if x.1 = a ∨ x.1 = b then I.lists x.1 ∪ F else I.lists x.1
  have hsub : ∀ x : S, I.lists x.1 ⊆ L x := by
    intro x
    by_cases hx : x.1 = a ∨ x.1 = b
    · simp only [L, ite_eq_left hx]
      exact Finset.subset_union_left
    · simp only [L, ite_eq_right hx]
      intro t ht
      exact ht
  have hroot : ∀ x : S, x.1 = a ∨ x.1 = b → 3 ≤ (L x).card := by
    intro x hx
    simp only [L, ite_eq_left hx]
    exact hF.trans (Finset.card_le_card Finset.subset_union_right)
  have hNoP : ∀ x : S, x.1 ≠ a → x.1 ≠ b → x.1 ∉ I.precolor.vertices := by
    intro x hxa hxb hxP
    exact (hPcap x.1 x.2 hxP).elim hxa hxb
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
      by_cases hx : x.1 = a ∨ x.1 = b
      · exact (by decide : 2 ≤ 3).trans (hroot x hx)
      · simp only [not_or] at hx
        simpa only [L, ite_eq_right (not_or.2 hx)] using I.outside_precolor_list_ge_two (hNoP x hx.1 hx.2)
    interior_lists := by
      intro x hx
      by_cases hr : x.1 = a ∨ x.1 = b
      · exact hroot x hr
      · have hold : ¬ OnOuterFace I.embedding I.outer x.1 := fun h => hx (ho x h)
        simpa only [L, ite_eq_right hr] using I.interior_lists x.1 hold
    short_edges := by
      intro x y hxy hx hy
      have hxroot : ¬ (x.1 = a ∨ x.1 = b) := fun h => by have h3 := hroot x h; omega
      have hyroot : ¬ (y.1 = a ∨ y.1 = b) := fun h => by have h3 := hroot y h; omega
      have hxold : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxroot] using hx
      have hyold : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyroot] using hy
      have hxP := (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxold hyold)).1
      exact (hNoP x (not_or.1 hxroot).1 (not_or.1 hxroot).2 hxP).elim }
  refine ⟨J, rfl, ?_, hsub, ho _ ha, ho _ hb⟩
  intro x hxa hxb
  exact ite_eq_right (not_or.2 ⟨hxa, hxb⟩)

end BoundaryInstance
end Thomassen
