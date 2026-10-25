/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ThreeVertexPathClosure

/-! Fixing bounded nontrivial stars at the current main induction cardinality. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A nontrivial root star on at most three vertices extends at the current
vertex cardinality by the proved small-prescription case. Its own calls to
the main induction remain strictly smaller. -/
theorem rootStar_extension_of_nontrivial_small_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hqlen : q.length ≤ 2) (hqpos : 0 < q.length) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ rootStar I v)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : RootStarExtension I v f := by
  have hface : ∀ x ∈ rootStar I v, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases hx with rfl | hx
    · exact hv
    · by_contra h
      have h3 := I.interior_lists x h
      omega
  have hbound : q.support.toFinset.card ≤ 6 := by
    calc
      _ ≤ q.support.length := List.toFinset_card_le q.support
      _ = q.length + 1 := q.length_support
      _ ≤ 6 := by omega
  let Q : BoundaryPrecolor G := .path q hq hbound
  have hQv : ∀ x, x ∈ Q.vertices ↔ x ∈ rootStar I v := by
    intro x
    exact List.mem_toFinset.trans (hexact x)
  let L : V → Finset C := fun x => if x ∈ rootStar I v then {f x} else I.lists x
  have hNoShort : ∀ x, x ∉ rootStar I v → (I.lists x).card ≤ 2 →
      ∀ y ∈ rootStar I v, ¬ G.Adj x y := by
    intro x hx hxshort y hy hxy
    rcases hy with rfl | hy
    · exact hx (Or.inr ⟨hxy.symm, hxshort⟩)
    · have he := I.short_edges hxy hxshort hy.2
      simp only [hP, BoundaryPrecolor.edges_empty, Finset.notMem_empty] at he
  let J : BoundaryInstance G C := {
    girth := I.girth
    embedding := I.embedding
    outer := I.outer
    precolor := Q
    lists := L
    prescribed := f
    on_outer := fun x hx => hface x ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact hproper x ((hQv x).1 hends.1) y ((hQv y).1 hends.2) (Q.adj_of_mem_edges he)
    boundary_lists := by
      intro x _ hx
      have hn : x ∉ rootStar I v := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hn]
      exact I.outside_precolor_list_ge_two (by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
    interior_lists := by
      intro x hx
      have hn : x ∉ rootStar I v := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hn] using I.interior_lists x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x ∈ rootStar I v <;> by_cases hyQ : y ∈ rootStar I v
      · exact List.mem_toFinset.2 (hch.mem_edges ((hexact x).2 hxQ) ((hexact y).2 hyQ) hxy)
      · exact (hNoShort y hyQ (by simpa only [L, ite_eq_right hyQ] using hy) x hxQ hxy.symm).elim
      · exact (hNoShort x hxQ (by simpa only [L, ite_eq_right hxQ] using hx) y hyQ hxy).elim
      · have he := I.short_edges hxy
          (by simpa only [L, ite_eq_right hxQ] using hx) (by simpa only [L, ite_eq_right hyQ] using hy)
        simp only [hP, BoundaryPrecolor.edges_empty, Finset.notMem_empty] at he }
  obtain ⟨c, hc⟩ := J.colourable_of_nontrivial_prescribed_path_at_most_three q hq hbound rfl hqpos
    (by rw [List.toFinset_card_of_nodup hq.support_nodup,Walk.length_support]; omega) hsmall
  change ∀ x, c x ∈ L x at hc
  have hagree : ∀ x ∈ rootStar I v, c x = f x := by
    intro x hx
    exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, hagree⟩
  intro x
  by_cases hx : x ∈ rootStar I v
  · rw [hagree x hx]
    exact hf x hx
  · simpa only [L, ite_eq_right hx] using hc x


/-- When all short neighbours of the root are among two distinct neighbours,
the full star is a native path of at most three vertices. -/
theorem rootStar_extension_of_two_neighbours_current (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (l r : V) (hl : G.Adj v l) (hr : G.Adj v r) (hlr : l ≠ r)
    (hbound : ∀ z, G.Adj v z → (I.lists z).card ≤ 2 → z = l ∨ z = r)
    (hHasShort : ∃ z, G.Adj v z ∧ (I.lists z).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : RootStarExtension I v f := by
  have hstar : ∀ z, z ∈ rootStar I v ↔ z = v ∨
      (z = l ∧ (I.lists l).card ≤ 2) ∨ (z = r ∧ (I.lists r).card ≤ 2) := by
    intro z
    constructor
    · rintro (rfl | ⟨hz, hs⟩)
      · exact Or.inl rfl
      · rcases hbound z hz hs with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, hs⟩)
        · exact Or.inr (Or.inr ⟨rfl, hs⟩)
    · rintro (rfl | ⟨rfl, hs⟩ | ⟨rfl, hs⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hl, hs⟩
      · exact Or.inr ⟨hr, hs⟩
  have hq : ∃ a b, ∃ q : G.Walk a b, q.IsPath ∧ q.length ≤ 2 ∧
      ∀ z, z ∈ q.support ↔ z ∈ rootStar I v := by
    by_cases hls : (I.lists l).card ≤ 2 <;> by_cases hrs : (I.lists r).card ≤ 2
    · refine ⟨l, r, .cons hl.symm (.cons hr .nil), ?_, by simp, ?_⟩
      · apply Walk.IsPath.mk'
        simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons,
          List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
          and_true, not_false_eq_true]
        exact ⟨⟨hl.ne.symm, hlr⟩, hr.ne⟩
      · intro z
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
          hstar, hls, hrs, and_true]
        tauto
    · refine ⟨v, l, hl.toWalk, hl.isPath_toWalk, by simp, ?_⟩
      intro z
      simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false,
        hstar, hls, hrs, and_true, and_false, or_false]
    · refine ⟨v, r, hr.toWalk, hr.isPath_toWalk, by simp, ?_⟩
      intro z
      simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false,
        hstar, hls, hrs, and_true, and_false, false_or]
    · refine ⟨v, v, .nil, by simp, by simp, ?_⟩
      intro z
      simp only [Walk.support_nil, List.mem_singleton, hstar, hls, hrs,
        and_false, or_false]
  obtain ⟨a, b, q, hpath, hlen, hexact⟩ := hq
  have hqpos : 0 < q.length := by
    by_contra h
    obtain ⟨z,hvz,hzs⟩ := hHasShort
    obtain ⟨i,hiv,hi⟩ := Walk.mem_support_iff_exists_getVert.1 ((hexact v).2 (Or.inl rfl))
    obtain ⟨j,hjz,hj⟩ := Walk.mem_support_iff_exists_getVert.1 ((hexact z).2 (Or.inr ⟨hvz,hzs⟩))
    have he : i=j := by omega
    exact hvz.ne (hiv.symm.trans ((congrArg q.getVert he).trans hjz))
  exact I.rootStar_extension_of_nontrivial_small_path hP v hv f hf hproper q hpath hlen hqpos
    (short_path_isChordless I.girth q hpath (by omega)) hexact hsmall

end Thomassen.BoundaryInstance
