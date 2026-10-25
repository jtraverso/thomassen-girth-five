/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AugmentedPathColouring

/-! Prescribing a root and its short-list neighbours. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The root together with all of its neighbours whose original lists are short. -/
def rootStar (I : BoundaryInstance G C) (v : V) : Set V :=
  {x | x = v ∨ G.Adj v x ∧ (I.lists x).card ≤ 2}

/-- A colouring of the whole original instance extending the given star colours. -/
def RootStarExtension (I : BoundaryInstance G C) (v : V) (f : V → C) : Prop :=
  ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ ∀ x ∈ rootStar I v, c x = f x

namespace BoundaryInstance

/-- In an empty-prescription instance, any allowed colour at the root extends
independently to its old short-list neighbours. -/
lemma exists_rootStar_colours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (t : C) (ht : t ∈ I.lists v) :
    ∃ f : V → C, f v = t ∧ (∀ x ∈ rootStar I v, f x ∈ I.lists x) ∧
      (∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y) := by
  have hchoose : ∀ x, G.Adj v x → (I.lists x).card ≤ 2 → ∃ c ∈ I.lists x, c ≠ t := by
    intro x _ _
    apply Finset.exists_mem_ne (s := I.lists x) _ t
    have h := I.outside_precolor_list_ge_two (x := x) (by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
    omega
  let f : V → C := fun x => if hx : x = v then t else
    if ha : G.Adj v x ∧ (I.lists x).card ≤ 2 then (hchoose x ha.1 ha.2).choose else I.prescribed x
  have hfv : f v = t := by simp only [f, dite_eq_left rfl]
  have hfn : ∀ x (hx : G.Adj v x ∧ (I.lists x).card ≤ 2), f x = (hchoose x hx.1 hx.2).choose := by
    intro x hx
    simp only [f, dite_eq_right hx.1.ne.symm, dite_eq_left hx]
  refine ⟨f, hfv, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact hfv ▸ ht
    · rw [hfn x hx]
      exact (hchoose x hx.1 hx.2).choose_spec.1
  · intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy.ne rfl).elim
    · rw [hfv, hfn y hy]
      exact (hchoose y hy.1 hy.2).choose_spec.2.symm
    · rw [hfn x hx, hfv]
      exact (hchoose x hx.1 hx.2).choose_spec.2
    · exact (neighbors_nonadjacent I.girth hx.1 hy.1 hxy).elim

/-- If the prescribed star is a native induced path of at most six vertices,
all changed-list conditions hold. The induction bound is explicitly strict. -/
theorem rootStar_extension_of_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hqlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ rootStar I v)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I v f := by
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
  obtain ⟨c, hc⟩ := hsmall V G J hN
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

variable [Finite V]

/-- When all short neighbours of the root are among two distinct neighbours,
the full star is a native path of at most three vertices. -/
theorem rootStar_extension_of_two_neighbours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (l r : V) (hl : G.Adj v l) (hr : G.Adj v r) (hlr : l ≠ r)
    (hbound : ∀ z, G.Adj v z → (I.lists z).card ≤ 2 → z = l ∨ z = r)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) : RootStarExtension I v f := by
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
  exact I.rootStar_extension_of_path hP v hv f hf hproper q hpath (by omega)
    (short_path_isChordless I.girth q hpath (by omega)) hexact N hN hsmall

end BoundaryInstance
end Thomassen
