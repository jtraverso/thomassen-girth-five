/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SingleBoundaryComplement

/-! Residual extension when the newly prescribed vertices are independent leaves. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A connected boundary deletion is solved when new short-list vertices are
independent, each has at most one old prescribed neighbour, and none attaches
to an endpoint of the old path. Their colours and the complete residual
prescription are constructed internally, with no bound on their number. -/
theorem colourable_of_pendant_residual_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbt : b ≠ t)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (hAP : ∀ x ∈ I.precolor.vertices, x ∉ A)
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (hPcolour : ∀ x ∈ I.precolor.vertices, I.prescribed x ∈ residual G I.lists A f x)
    (hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f x).card)
    (N : Set V)
    (hN : ∀ x, x ∈ N ↔ x ∉ A ∧ x ∉ I.precolor.vertices ∧ (residual G I.lists A f x).card ≤ 2)
    (hNadj : ∀ x ∈ N, ∃ y ∈ A, G.Adj x y)
    (hNind : ∀ x ∈ N, ∀ y ∈ N, ¬ G.Adj x y)
    (hNunique : ∀ x ∈ N, ∀ y ∈ I.precolor.vertices, ∀ z ∈ I.precolor.vertices,
      G.Adj x y → G.Adj x z → y = z)
    (hNends : ∀ x ∈ N, ¬ G.Adj x b ∧ ¬ G.Adj x t)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let P : Set V := {x | x ∈ r.support}
  let L := residual G I.lists A f
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ P := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]; rfl
  have hlen : r.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at hn
    omega
  have hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges := by
    intro x y hx hy hxy
    have he := I.short_edges hxy (by simp [I.singleton x ((hPv x).2 hx)])
      (by simp [I.singleton y ((hPv y).2 hy)])
    simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using he
  let R : Set V := {x | x ∈ N ∧ ∃ y ∈ P, G.Adj x y}
  let Q : Set V := P ∪ R
  have hRcol : ∀ x ∈ R, ∃ col ∈ L x, ∀ y ∈ P, G.Adj x y → col ≠ I.prescribed y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hx.2
    have hxN := (hN x).1 hx.1
    obtain ⟨col,hcol,hne⟩ := Finset.exists_mem_ne (s := L x)
      (by have h2 : 2 ≤ (L x).card := hTwo x hxN.1 hxN.2.1; omega) (I.prescribed y)
    refine ⟨col,hcol,fun z hz hxz => ?_⟩
    exact (hNunique x hx.1 y ((hPv y).2 hy) z ((hPv z).2 hz) hxy hxz) ▸ hne
  let g : V → C := fun x => if hx : x ∈ R then (hRcol x hx).choose else I.prescribed x
  have hgR : ∀ x ∈ R, g x ∈ L x ∧ ∀ y ∈ P, G.Adj x y → g x ≠ I.prescribed y := by
    intro x hx
    simpa only [g,dite_eq_left hx] using (hRcol x hx).choose_spec
  have hgP : ∀ x ∈ P, g x = I.prescribed x := by
    intro x hx
    exact dite_eq_right (fun h => ((hN x).1 h.1).2.1 ((hPv x).2 hx))
  have hg : ∀ x ∈ Q, g x ∈ L x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hgP x hx]; exact hPcolour x ((hPv x).2 hx)
    · exact (hgR x hx).1
  have hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hgP x hx,hgP y hy]
      exact I.proper_on_precolored_vertices ((hPv x).2 hx) ((hPv y).2 hy) hxy
    · rw [hgP x hx]; exact ((hgR y hy).2 x hx hxy.symm).symm
    · rw [hgP y hy]; exact (hgR x hx).2 y hy hxy
    · exact (hNind x hx.1 y hy.1 hxy).elim
  apply I.colourable_of_connected_residual_prescription hG p hp hface hroot
    (fun x hx => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx)
    A ha hA f hf hproper Q
    (connSet_adjoin_attached_vertices P R (walk_support_connSet r) (fun _ hx => hx.2))
    (by intro x hx; rcases hx with hx | hx
        · exact hAP x ((hPv x).2 hx)
        · exact ((hN x).1 hx.1).1)
    (by intro x hx; rcases hx with hx | hx
        · exact Or.inl (I.on_outer x ((hPv x).2 hx))
        · exact Or.inr (hNadj x hx.1))
    (fun q hq hsub => short_path_with_pendant_vertices_paths_short r hr hlen hbt hedges R
      (fun _ hx _ hy => hNind _ hx.1 _ hy.1)
      (fun x hx y hy z hz => hNunique x hx.1 y ((hPv y).2 hy) z ((hPv z).2 hz))
      (fun _ hx => hNends _ hx.1) q hq hsub)
    (by intro x hx; rcases hx with hx | hx
        · exact (Finset.card_le_card (residual_subset G I.lists A f x)).trans
            (by simp only [I.singleton x ((hPv x).2 hx),Finset.card_singleton]; omega)
        · exact ((hN x).1 hx.1).2.2)
    g hg hgp
    (by intro x hx hxQ; apply hTwo x hx
        exact fun h => hxQ (Or.inl ((hPv x).1 h)))
    (by intro x hx y hy hxy hxs hys
        by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
        · exact ⟨Or.inl hxP,Or.inl hyP⟩
        · exact ⟨Or.inl hxP,Or.inr ⟨(hN y).2 ⟨hy,fun h => hyP ((hPv y).1 h),hys⟩,x,hxP,hxy.symm⟩⟩
        · exact ⟨Or.inr ⟨(hN x).2 ⟨hx,fun h => hxP ((hPv x).1 h),hxs⟩,y,hyP,hxy⟩,Or.inl hyP⟩
        · exact (hNind x ((hN x).2 ⟨hx,fun h => hxP ((hPv x).1 h),hxs⟩)
            y ((hN y).2 ⟨hy,fun h => hyP ((hPv y).1 h),hys⟩) hxy).elim)
    hsmall

end Thomassen.BoundaryInstance
