/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStarExtension

/-! Fixing an edge and its old short-list neighbours. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Both ends of an edge, together with all their original short-list neighbours. -/
def edgeStar (I : BoundaryInstance G C) (a b : V) : Set V := rootStar I a ∪ rootStar I b

/-- An original list colouring fixing all the specified edge-star colours. -/
def EdgeStarExtension (I : BoundaryInstance G C) (a b : V) (f : V → C) : Prop :=
  ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ ∀ x ∈ edgeStar I a b, c x = f x

namespace BoundaryInstance

/-- A native induced path prescription checks every changed-list condition.
The main induction is used only below its explicit cardinality bound. -/
theorem edgeStar_extension_of_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    {s t : V} (q : G.Walk s t) (hq : q.IsPath) (hqlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ edgeStar I a b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : EdgeStarExtension I a b f := by
  have hface : ∀ x ∈ edgeStar I a b, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases hx with hx | hx <;> rcases hx with rfl | hx
    · exact ha
    · by_contra h
      have h3 := I.interior_lists x h
      omega
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
  have hQv : ∀ x, x ∈ Q.vertices ↔ x ∈ edgeStar I a b := by
    intro x
    exact List.mem_toFinset.trans (hexact x)
  let L : V → Finset C := fun x => if x ∈ edgeStar I a b then {f x} else I.lists x
  have hNoShort : ∀ x, x ∉ edgeStar I a b → (I.lists x).card ≤ 2 →
      ∀ y ∈ edgeStar I a b, ¬ G.Adj x y := by
    intro x hx hxshort y hy hxy
    rcases hy with hy | hy <;> rcases hy with rfl | hy
    · exact hx (Or.inl (Or.inr ⟨hxy.symm, hxshort⟩))
    · have he := I.short_edges hxy hxshort hy.2
      simp only [hP, BoundaryPrecolor.edges_empty, Finset.notMem_empty] at he
    · exact hx (Or.inr (Or.inr ⟨hxy.symm, hxshort⟩))
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
      have hn : x ∉ edgeStar I a b := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hn]
      exact I.outside_precolor_list_ge_two (by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
    interior_lists := by
      intro x hx
      have hn : x ∉ edgeStar I a b := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hn] using I.interior_lists x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x ∈ edgeStar I a b <;> by_cases hyQ : y ∈ edgeStar I a b
      · exact List.mem_toFinset.2 (hch.mem_edges ((hexact x).2 hxQ) ((hexact y).2 hyQ) hxy)
      · exact (hNoShort y hyQ (by simpa only [L, ite_eq_right hyQ] using hy) x hxQ hxy.symm).elim
      · exact (hNoShort x hxQ (by simpa only [L, ite_eq_right hxQ] using hx) y hyQ hxy).elim
      · have he := I.short_edges hxy
          (by simpa only [L, ite_eq_right hxQ] using hx) (by simpa only [L, ite_eq_right hyQ] using hy)
        simp only [hP, BoundaryPrecolor.edges_empty, Finset.notMem_empty] at he }
  obtain ⟨c, hc⟩ := hsmall V G J hN
  change ∀ x, c x ∈ L x at hc
  have hagree : ∀ x ∈ edgeStar I a b, c x = f x := by
    intro x hx
    exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, hagree⟩
  intro x
  by_cases hx : x ∈ edgeStar I a b
  · rw [hagree x hx]
    exact hf x hx
  · simpa only [L, ite_eq_right hx] using hc x

variable [Finite V]

/-- When every external short neighbour lies on the two free ends of a
three-edge boundary path, the whole fixed edge-star is a native induced path. -/
theorem edgeStar_extension_of_two_neighbours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (l r : V) (hab : G.Adj a b) (hal : G.Adj a l) (hbr : G.Adj b r)
    (hlb : l ≠ b) (hra : r ≠ a) (hlr : l ≠ r)
    (hboundA : ∀ z, G.Adj a z → (I.lists z).card ≤ 2 → z = b ∨ z = l)
    (hboundB : ∀ z, G.Adj b z → (I.lists z).card ≤ 2 → z = a ∨ z = r)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) : EdgeStarExtension I a b f := by
  have hstar : ∀ z, z ∈ edgeStar I a b ↔ z = a ∨ z = b ∨
      (z = l ∧ (I.lists l).card ≤ 2) ∨ (z = r ∧ (I.lists r).card ≤ 2) := by
    intro z
    constructor
    · rintro ((rfl | ⟨hz, hs⟩) | (rfl | ⟨hz, hs⟩))
      · exact Or.inl rfl
      · rcases hboundA z hz hs with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, hs⟩))
      · exact Or.inr (Or.inl rfl)
      · rcases hboundB z hz hs with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, hs⟩))
    · rintro (rfl | rfl | ⟨rfl, hs⟩ | ⟨rfl, hs⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨hal, hs⟩)
      · exact Or.inr (Or.inr ⟨hbr, hs⟩)
  have hq : ∃ s t, ∃ q : G.Walk s t, q.IsPath ∧ q.length ≤ 3 ∧
      ∀ z, z ∈ q.support ↔ z ∈ edgeStar I a b := by
    by_cases hls : (I.lists l).card ≤ 2 <;> by_cases hrs : (I.lists r).card ≤ 2
    · refine ⟨l, r, .cons hal.symm (.cons hab (.cons hbr .nil)), ?_, by simp, ?_⟩
      · apply Walk.IsPath.mk'
        simp [Walk.support_cons, Walk.support_nil, hal.ne, hab.ne, hbr.ne, hlb, hra, hlr, Ne.symm]
      · intro z
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
          hstar, hls, hrs, and_true]
        tauto
    · refine ⟨l, b, .cons hal.symm (.cons hab .nil), ?_, by simp, ?_⟩
      · apply Walk.IsPath.mk'
        simp [Walk.support_cons, Walk.support_nil, hal.ne, hab.ne, hlb, Ne.symm]
      · intro z
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
          hstar, hls, hrs, and_true, and_false]
        tauto
    · refine ⟨a, r, .cons hab (.cons hbr .nil), ?_, by simp, ?_⟩
      · apply Walk.IsPath.mk'
        simp [Walk.support_cons, Walk.support_nil, hab.ne, hbr.ne, hra, Ne.symm]
      · intro z
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
          hstar, hls, hrs, and_true, and_false, false_or]
    · refine ⟨a, b, hab.toWalk, hab.isPath_toWalk, by simp, ?_⟩
      intro z
      simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false,
        hstar, hls, hrs, and_false]
  obtain ⟨s, t, q, hpath, hlen, hexact⟩ := hq
  exact I.edgeStar_extension_of_path hP a b ha hb f hf hproper q hpath (by omega)
    (short_path_isChordless I.girth q hpath hlen) hexact N hN hsmall

end BoundaryInstance
end Thomassen
