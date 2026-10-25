/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedTwoPathClassification

/-! Compatible short-path prescriptions with arbitrarily many short leaves. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Extend a short induced path whose two ends have old short lists, with
all remaining new vertices on one edge. Old short neighbours of the internal
edge become independent leaves; old short ends have no such neighbours. -/
theorem colourable_induced_with_compatible_short_ended_path (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected) {a b : V} (q : G.Walk a b)
    (hq : q.IsPath) (hlen : q.length ≤ 5) (hch : q.IsChordless)
    (hQS : ∀ x ∈ q.support, x ∈ S)
    (hOldP : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (u w : V) (huw : G.Adj u w)
    (hnew : ∀ x ∈ q.support, x ∈ I.precolor.vertices ∨ (I.lists x).card ≤ 2 ∨ x = u ∨ x = w)
    (hab : a ≠ b) (haShort : (I.lists a).card ≤ 2) (hbShort : (I.lists b).card ≤ 2)
    (f : V → C) (hf : ∀ x ∈ q.support, f x ∈ I.lists x)
    (hproper : ∀ x ∈ q.support, ∀ y ∈ q.support, G.Adj x y → f x ≠ f y)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace M o x)
    (hOldFace : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → OnOuterFace M o x)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ q.support → c x = f x.1 := by
  let P : Set V := {x | x ∈ q.support}
  let R : Set V := {x | x ∈ S ∧ x ∉ q.support ∧ (I.lists x).card ≤ 2 ∧ (∃ y ∈ q.support, G.Adj x y)}
  let Q : Set V := P ∪ R
  have hRnotP : ∀ x ∈ R, x ∉ I.precolor.vertices := fun x hx h => hx.2.1 (hOldP x hx.1 h)
  have hRnotAdjP : ∀ x ∈ R, ∀ y ∈ I.precolor.vertices, ¬ G.Adj x y :=
    fun x hx y hy => I.short_not_adj_precolored (hRnotP x hx) hy hx.2.2.1
  have hRnotAdjShort : ∀ x ∈ R, ∀ y, (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact hRnotP x hx (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hx.2.2.1 hy)).1
  have hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact hRnotP x hx (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hx.2.2.1 hy.2.2.1)).1
  have hRunique : ∀ x ∈ R, ∀ y ∈ q.support, ∀ z ∈ q.support,
      G.Adj x y → G.Adj x z → y = z := by
    intro x hx y hy z hz hxy hxz
    have hyN : y = u ∨ y = w := ((hnew y hy).resolve_left (fun h => hRnotAdjP x hx y h hxy)).resolve_left
      (fun h => hRnotAdjShort x hx y h hxy)
    have hzN : z = u ∨ z = w := ((hnew z hz).resolve_left (fun h => hRnotAdjP x hx z h hxz)).resolve_left
      (fun h => hRnotAdjShort x hx z h hxz)
    rcases hyN with hyu | hyw <;> rcases hzN with hzu | hzw
    · exact hyu.trans hzu.symm
    · exact (neighbors_nonadjacent I.girth (hyu ▸ hxy) (hzw ▸ hxz) huw).elim
    · exact (neighbors_nonadjacent I.girth (hyw ▸ hxy) (hzu ▸ hxz) huw.symm).elim
    · exact hyw.trans hzw.symm
  have hRattach : ∀ x ∈ R, ∃ y ∈ q.support, G.Adj x y := fun _ hx => hx.2.2.2
  let attach : V → V := fun x => if hx : x ∈ R then (hRattach x hx).choose else a
  have hattach : ∀ x ∈ R, attach x ∈ q.support ∧ G.Adj x (attach x) := by
    intro x hx
    simpa only [attach,dite_eq_left hx] using (hRattach x hx).choose_spec
  have hRcol : ∀ x ∈ R, ∃ col ∈ I.lists x, col ≠ f (attach x) := by
    intro x hx
    exact Finset.exists_mem_ne (by have := I.outside_precolor_list_ge_two (hRnotP x hx); omega) (f (attach x))
  let g : V → C := fun x => if x ∈ q.support then f x else
    if hx : x ∈ R then (hRcol x hx).choose else I.prescribed x
  have hgP : ∀ x ∈ q.support, g x = f x := fun x hx => ite_eq_left hx
  have hgR : ∀ x ∈ R, g x ∈ I.lists x ∧ g x ≠ f (attach x) := by
    intro x hx
    simpa only [g,ite_eq_right hx.2.1,dite_eq_left hx] using (hRcol x hx).choose_spec
  have hgmem : ∀ x ∈ Q, g x ∈ I.lists x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hgP x hx]; exact hf x hx
    · exact (hgR x hx).1
  have hgproper : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y := by
    have hcross : ∀ x ∈ R, ∀ y ∈ q.support, G.Adj x y → g x ≠ g y := by
      intro x hx y hy hxy
      have hya : y = attach x := hRunique x hx y hy (attach x) (hattach x hx).1 hxy (hattach x hx).2
      rw [hgP y hy,hya]
      exact (hgR x hx).2
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hgP x hx,hgP y hy]; exact hproper x hx y hy hxy
    · exact (hcross y hy x hx hxy.symm).symm
    · exact hcross x hx y hy hxy
    · exact (hRind x hx y hy hxy).elim
  have hQconn : ConnSet G Q := connSet_adjoin_attached_vertices P R (walk_support_connSet q)
    (fun x hx => ⟨attach x,(hattach x hx).1,(hattach x hx).2⟩)
  have hQsub : Q ⊆ S := by
    intro x hx; rcases hx with hx | hx
    · exact hQS x hx
    · exact hx.1
  have hQface : ∀ x : S, x.1 ∈ Q → OnOuterFace M o x := by
    intro x hx
    rcases hx with hx | hx
    · exact hface x hx
    · apply hOldFace
      by_contra h
      have h3 := I.interior_lists x.1 h
      have h2 := hx.2.2.1
      omega
  have hNoShort : ∀ x ∈ S, x ∉ Q → (I.lists x).card ≤ 2 → ∀ y ∈ Q, ¬ G.Adj x y := by
    intro x hxS hxQ hxs y hy hxy
    have hxP : x ∉ I.precolor.vertices := fun h => hxQ (Or.inl (hOldP x hxS h))
    rcases hy with hy | hy
    · exact hxQ (Or.inr ⟨hxS,fun h => hxQ (Or.inl h),hxs,⟨y,hy,hxy⟩⟩)
    · exact hxP (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxs hy.2.2.1)).1
  let L : S → Finset C := fun x => if x.1 ∈ Q then {g x.1} else I.lists x.1
  let J : ConnectedPrescription (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := M
    outer := o
    vertices := {x : S | x.1 ∈ Q}
    connected := connSet_induce_of_subset Q S hQconn hQsub
    paths_short := by
      intro x y w hw hs
      have hm := short_path_with_pendant_vertices_paths_short q hq hlen hab
        (fun hx hy hxy => hch.mem_edges hx hy hxy) R hRind hRunique
        (fun x hx => ⟨hRnotAdjShort x hx a haShort,hRnotAdjShort x hx b hbShort⟩)
        (w.map (Embedding.induce S).toHom) (hw.map Subtype.val_injective) (by
          intro z hz
          rw [Walk.support_map] at hz
          obtain ⟨v,hv,he⟩ := List.mem_map.1 hz
          change v.1 = z at he
          exact he ▸ hs v hv)
      simpa only [Walk.length_map] using hm
    lists := L
    prescribed := fun x => g x.1
    on_outer := hQface
    singleton := fun x hx => ite_eq_left (show x.1 ∈ Q from hx)
    proper := fun {x y} hx hy hxy => hgproper x.1 hx y.1 hy hxy
    boundary_lists := by
      intro x _ hx
      have hn : x.1 ∉ Q := hx
      simp only [L,ite_eq_right hn]
      exact I.outside_precolor_list_ge_two (fun h => hn (Or.inl (hOldP x.1 x.2 h)))
    interior_lists := by
      intro x hx
      have hn : x.1 ∉ Q := fun h => hx (hQface x h)
      simpa only [L,ite_eq_right hn] using I.interior_lists x.1 (fun h => hx (hOldFace x h))
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x.1 ∈ Q <;> by_cases hyQ : y.1 ∈ Q
      · exact ⟨hxQ,hyQ⟩
      · exact (hNoShort y.1 y.2 hyQ (by simpa only [L,ite_eq_right hyQ] using hy) x.1 hxQ hxy.symm).elim
      · exact (hNoShort x.1 x.2 hxQ (by simpa only [L,ite_eq_right hxQ] using hx) y.1 hyQ hxy).elim
      · have he := I.short_edges (x := x.1) (y := y.1) hxy (by simpa only [L,ite_eq_right hxQ] using hx)
          (by simpa only [L,ite_eq_right hyQ] using hy)
        exact (hxQ (Or.inl (hOldP x.1 x.2 (I.precolor.endpoints_of_mem_edges he).1))).elim }
  obtain ⟨c,hc⟩ := connectedPrescription_extension_of_smaller (Nat.card V) hsmall J hconn hSsmall
  change ∀ x : S, c x ∈ L x at hc
  have hfixed : ∀ x : S, x.1 ∈ Q → c x = g x.1 := fun x hx =>
    Finset.mem_singleton.1 (by simpa only [L,ite_eq_left hx] using hc x)
  refine ⟨c,?_,fun x hx => (hfixed x (Or.inl hx)).trans (hgP x.1 hx)⟩
  intro x
  by_cases hx : x.1 ∈ Q
  · rw [hfixed x hx]; exact hgmem x.1 hx
  · simpa only [L,ite_eq_right hx] using hc x

end Thomassen.BoundaryInstance
