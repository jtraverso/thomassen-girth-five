/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedPathOrder

/-! Root fans retaining the entire original prescription. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance

/-- Star colours compatible with original lists extend to a proper colouring
of the union with the original prescription, preserving every singleton. -/
lemma exists_prescribed_rootStar_colours (I : BoundaryInstance G C) (b : V) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y) :
    ∃ g : V → C, (∀ x ∈ rootStar I b, g x = f x) ∧
      (∀ x ∈ I.precolor.vertices, g x = I.prescribed x) ∧
      (∀ x, x ∈ I.precolor.vertices ∨ x ∈ rootStar I b → g x ∈ I.lists x) ∧
      (∀ x, x ∈ I.precolor.vertices ∨ x ∈ rootStar I b →
        ∀ y, y ∈ I.precolor.vertices ∨ y ∈ rootStar I b → G.Adj x y → g x ≠ g y) := by
  let g : V → C := fun x => if x ∈ rootStar I b then f x else I.prescribed x
  have hstar : ∀ x ∈ rootStar I b, g x = f x := fun x hx => ite_eq_left hx
  have hP : ∀ x ∈ I.precolor.vertices, g x = I.prescribed x := by
    intro x hxP
    by_cases hx : x ∈ rootStar I b
    · rw [hstar x hx]
      exact Finset.mem_singleton.1 (by simpa only [I.singleton x hxP] using hf x hx)
    · exact ite_eq_right hx
  have hcross : ∀ x ∈ rootStar I b, ∀ y ∈ I.precolor.vertices,
      G.Adj x y → g x ≠ g y := by
    intro x hx y hyP hxy
    by_cases hy : y ∈ rootStar I b
    · rw [hstar x hx, hstar y hy]
      exact hproper x hx y hy hxy
    · have hxP : x ∈ I.precolor.vertices := by
        rcases hx with rfl | hx
        · exact (hy (Or.inr ⟨hxy, by simp [I.singleton y hyP]⟩)).elim
        · exact (I.precolor.endpoints_of_mem_edges
            (I.short_edges hxy hx.2 (by simp [I.singleton y hyP]))).1
      rw [hP x hxP, hP y hyP]
      exact I.proper_on_precolored_vertices hxP hyP hxy
  refine ⟨g, hstar, hP, ?_, ?_⟩
  · intro x hx
    rcases hx with hxP | hx
    · rw [hP x hxP, I.singleton x hxP]
      exact Finset.mem_singleton_self _
    · rw [hstar x hx]
      exact hf x hx
  · intro x hx y hy hxy
    rcases hx with hxP | hx <;> rcases hy with hyP | hy
    · rw [hP x hxP, hP y hyP]
      exact I.proper_on_precolored_vertices hxP hyP hxy
    · exact (hcross y hy x hxP hxy.symm).symm
    · exact hcross x hx y hyP hxy
    · rw [hstar x hx, hstar y hy]
      exact hproper x hx y hy hxy

/-- If the union of the old prescription and fixed root fan is a native
induced path on at most six vertices, the strict main induction extends it.
Every original singleton and every fixed short-neighbour colour is retained. -/
theorem rootStar_extension_of_prescribed_path (I : BoundaryInstance G C)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    {a t : V} (q : G.Walk a t) (hq : q.IsPath) (hlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ I.precolor.vertices ∨ x ∈ rootStar I b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I b f := by
  obtain ⟨g, hgstar, hgP, hgmem, hgproper⟩ := I.exists_prescribed_rootStar_colours b f hf hproper
  let A : Set V := {x | x ∈ I.precolor.vertices ∨ x ∈ rootStar I b}
  have hface : ∀ x ∈ A, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases hx with hxP | rfl | hx
    · exact I.on_outer x hxP
    · exact hb
    · by_contra h
      have h3 := I.interior_lists x h
      omega
  have hbound : q.support.toFinset.card ≤ 6 := by
    calc
      _ ≤ q.support.length := List.toFinset_card_le q.support
      _ = q.length + 1 := q.length_support
      _ ≤ 6 := by omega
  let Q : BoundaryPrecolor G := .path q hq hbound
  have hQv : ∀ x, x ∈ Q.vertices ↔ x ∈ A := fun x => List.mem_toFinset.trans (hexact x)
  let L : V → Finset C := fun x => if x ∈ A then {g x} else I.lists x
  have hNoShort : ∀ x, x ∉ A → (I.lists x).card ≤ 2 → ∀ y ∈ A, ¬ G.Adj x y := by
    intro x hx hxs y hy hxy
    rcases hy with hyP | rfl | hy
    · exact hx (Or.inl (I.precolor.endpoints_of_mem_edges
        (I.short_edges hxy hxs (by simp [I.singleton y hyP]))).1)
    · exact hx (Or.inr (Or.inr ⟨hxy.symm, hxs⟩))
    · exact hx (Or.inl (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxs hy.2)).1)
  let J : BoundaryInstance G C := {
    girth := I.girth
    embedding := I.embedding
    outer := I.outer
    precolor := Q
    lists := L
    prescribed := g
    on_outer := fun x hx => hface x ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact hgproper x ((hQv x).1 hends.1) y ((hQv y).1 hends.2) (Q.adj_of_mem_edges he)
    boundary_lists := by
      intro x _ hx
      have hn : x ∉ A := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hn]
      exact I.outside_precolor_list_ge_two (fun h => hn (Or.inl h))
    interior_lists := by
      intro x hx
      have hn : x ∉ A := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hn] using I.interior_lists x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x ∈ A <;> by_cases hyQ : y ∈ A
      · exact List.mem_toFinset.2 (hch.mem_edges ((hexact x).2 hxQ) ((hexact y).2 hyQ) hxy)
      · exact (hNoShort y hyQ (by simpa only [L, ite_eq_right hyQ] using hy) x hxQ hxy.symm).elim
      · exact (hNoShort x hxQ (by simpa only [L, ite_eq_right hxQ] using hx) y hyQ hxy).elim
      · have he := I.short_edges hxy (by simpa only [L, ite_eq_right hxQ] using hx)
          (by simpa only [L, ite_eq_right hyQ] using hy)
        exact (hxQ (Or.inl (I.precolor.endpoints_of_mem_edges he).1)).elim }
  obtain ⟨c, hc⟩ := hsmall V G J hN
  change ∀ x, c x ∈ L x at hc
  have hagree : ∀ x ∈ A, c x = g x := fun x hx => Finset.mem_singleton.1
    (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, fun x hx => (hagree x (Or.inr hx)).trans (hgstar x hx)⟩
  intro x
  by_cases hx : x ∈ A
  · rw [hagree x hx]
    exact hgmem x hx
  · simpa only [L, ite_eq_right hx] using hc x

end BoundaryInstance
end Thomassen
