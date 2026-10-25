/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorThreePathUniqueness

/-! Retain a native prescription and colour all newly short attached leaves. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A connected deletion can expose arbitrarily many short neighbours of
the old prescription. If these neighbours are independent and avoid its two
ends, they can all be fixed as pendant vertices and extended on strictly
smaller actual face pieces. No bound on the number of leaves is required. -/
theorem colourable_of_residual_short_leaves (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {s t : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hrlen : r.length ≤ 4)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (hPA : ∀ x ∈ I.precolor.vertices, x ∉ A)
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (hResP : ∀ x ∈ I.precolor.vertices, residual G I.lists A f x = {I.prescribed x})
    (hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f x).card)
    (hIndependent : ∀ x, x ∉ A → x ∉ I.precolor.vertices → ∀ y, y ∉ A → y ∉ I.precolor.vertices →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → ¬ G.Adj x y)
    (hEnds : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (residual G I.lists A f x).card ≤ 2 →
      ¬ G.Adj x s ∧ ¬ G.Adj x t)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  let P : Set V := {x | x ∈ r.support}
  let R : Set V := {x | x ∉ A ∧ x ∉ I.precolor.vertices ∧ (residual G I.lists A f x).card ≤ 2 ∧
    ∃ y ∈ P, G.Adj x y}
  let Q : Set V := P ∪ R
  have hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y :=
    fun x hx y hy => hIndependent x hx.1 hx.2.1 y hy.1 hy.2.1 hx.2.2.1 hy.2.2.1
  have hRunique : ∀ x ∈ R, ∀ y ∈ r.support, ∀ z ∈ r.support, G.Adj x y → G.Adj x z → y=z := by
    intro x hx y hy z hz hxy hxz
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hy
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    have hEndsX := hEnds x hx.1 hx.2.1 hx.2.2.1
    have hi0 : i ≠ 0 := fun h => hEndsX.1 (by simpa only [← hi,h,Walk.getVert_zero] using hxy)
    have hj0 : j ≠ 0 := fun h => hEndsX.1 (by simpa only [← hj,h,Walk.getVert_zero] using hxz)
    have hin : i ≠ r.length := fun h => hEndsX.2 (by simpa only [← hi,h,Walk.getVert_length] using hxy)
    have hjn : j ≠ r.length := fun h => hEndsX.2 (by simpa only [← hj,h,Walk.getVert_length] using hxz)
    have hxR : x ∉ r.support := fun h => hx.2.1 ((hPv x).2 h)
    have hij : i=j := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · have hg := path_neighbour_indices_gap I.girth r hr hxR i j h hjl (by rwa [hi]) (by rwa [hj])
        omega
      · have hg := path_neighbour_indices_gap I.girth r hr hxR j i h hil (by rwa [hj]) (by rwa [hi])
        omega
    exact hi.symm.trans ((congrArg r.getVert hij).trans hj)
  have hRcol : ∀ x ∈ R, ∃ col ∈ residual G I.lists A f x, ∀ y ∈ P, G.Adj x y → col ≠ I.prescribed y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hx.2.2.2
    obtain ⟨col,hcol,hcoly⟩ := Finset.exists_mem_ne (s := residual G I.lists A f x)
      (by have h2 := hTwo x hx.1 hx.2.1; omega) (I.prescribed y)
    refine ⟨col,hcol,?_⟩
    intro z hz hxz
    rw [← hRunique x hx y hy z hz hxy hxz]
    exact hcoly
  let g : V → C := fun x => if hx : x ∈ R then (hRcol x hx).choose else I.prescribed x
  have hgP : ∀ x ∈ P, g x = I.prescribed x := by
    intro x hx
    exact dite_eq_right (fun h => h.2.1 ((hPv x).2 hx))
  have hgR : ∀ x ∈ R, g x ∈ residual G I.lists A f x ∧
      ∀ y ∈ P, G.Adj x y → g x ≠ I.prescribed y := by
    intro x hx
    simpa only [g,dite_eq_left hx] using (hRcol x hx).choose_spec
  have hg : ∀ x ∈ Q, g x ∈ residual G I.lists A f x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hgP x hx,hResP x ((hPv x).2 hx)]; exact Finset.mem_singleton_self _
    · exact (hgR x hx).1
  have hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hgP x hx,hgP y hy]
      exact I.proper_on_precolored_vertices ((hPv x).2 hx) ((hPv y).2 hy) hxy
    · rw [hgP x hx]
      exact ((hgR y hy).2 x hx hxy.symm).symm
    · rw [hgP y hy]
      exact (hgR x hx).2 y hy hxy
    · exact (hRind x hx y hy hxy).elim
  have hrch : r.IsChordless := by
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    have hxP := (hPv x).2 hx
    have hyP := (hPv y).2 hy
    have he := I.short_edges hxy (by rw [I.singleton x hxP,Finset.card_singleton]; omega)
      (by rw [I.singleton y hyP,Finset.card_singleton]; omega)
    simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using he
  apply I.colourable_of_connected_residual_prescription hG p hp hface hroot
    (fun x hx => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx)
    A ha hA f hf hproper Q
    (connSet_adjoin_attached_vertices P R (walk_support_connSet r)
      (by intro x hx; obtain ⟨y,hy,hxy⟩ := hx.2.2.2; exact ⟨y,hy,hxy⟩))
    (by intro x hx; rcases hx with hx | hx; exact hPA x ((hPv x).2 hx); exact hx.1)
    (by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl (I.on_outer x ((hPv x).2 hx))
      · by_cases hxF : OnOuterFace I.embedding I.outer x
        · exact Or.inl hxF
        · obtain ⟨y,hy,hyx⟩ := short_residual_neighbor I.lists A f x (I.interior_lists x hxF) hx.2.2.1
          exact Or.inr ⟨y,hy,hyx.symm⟩)
    (by
      intro x y w hw hs
      exact short_path_with_pendant_vertices_paths_short r hr (by omega)
        (fun h => by have he := hr.getVert_injOn (Nat.zero_le _) (Nat.le_refl _) (by simpa only [Walk.getVert_zero,Walk.getVert_length] using h); omega)
        (fun hx hy hxy => hrch.mem_edges hx hy hxy) R hRind hRunique
        (fun x hx => hEnds x hx.1 hx.2.1 hx.2.2.1) w hw hs)
    (by
      intro x hx
      rcases hx with hx | hx
      · rw [hResP x ((hPv x).2 hx),Finset.card_singleton]; omega
      · exact hx.2.2.1)
    g hg hgp
    (fun x hx hxQ => hTwo x hx (fun h => hxQ (Or.inl ((hPv x).1 h))))
    (by
      intro x hx y hy hxy hxs hys
      by_cases hxP : x ∈ I.precolor.vertices <;> by_cases hyP : y ∈ I.precolor.vertices
      · exact ⟨Or.inl ((hPv x).1 hxP),Or.inl ((hPv y).1 hyP)⟩
      · exact ⟨Or.inl ((hPv x).1 hxP),Or.inr ⟨hy,hyP,hys,x,(hPv x).1 hxP,hxy.symm⟩⟩
      · exact ⟨Or.inr ⟨hx,hxP,hxs,y,(hPv y).1 hyP,hxy⟩,Or.inl ((hPv y).1 hyP)⟩
      · exact (hIndependent x hx hxP y hy hyP hxs hys hxy).elim)
    hsmall

end Thomassen.BoundaryInstance
