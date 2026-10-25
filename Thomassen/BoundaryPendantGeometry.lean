/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortFaceNeighbours

/-! Connected prescriptions obtained by attaching independent pendant vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The support of a native walk is connected. -/
lemma walk_support_connSet {a b : V} (p : G.Walk a b) : ConnSet G {x | x ∈ p.support} := by
  induction p with
  | @nil a =>
    convert connSet_singleton G a using 1
    ext x; simp
  | @cons a b t hab p ih =>
    convert ih.insert_adj p.start_mem_support hab using 1
    ext x; simp

/-- Attaching any number of vertices, each adjacent to a connected set,
preserves connectedness of the prescribed union. -/
lemma connSet_adjoin_attached_vertices (P R : Set V) (hP : ConnSet G P)
    (hR : ∀ x ∈ R, ∃ y ∈ P, G.Adj x y) : ConnSet G (P ∪ R) := by
  obtain ⟨a,ha⟩ := hP.1
  have hsub : P ⊆ P ∪ R := Set.subset_union_left
  have hreach : ∀ x ∈ P ∪ R, RIn G (P ∪ R) a x := by
    intro x hx
    rcases hx with hx | hx
    · exact (hP.2 a ha x hx).mono_set hsub
    · obtain ⟨y,hy,hxy⟩ := hR x hx
      exact ((hP.2 a ha y hy).mono_set hsub).tail hxy.symm (hsub hy) (Or.inr hx)
  exact ⟨⟨a,Or.inl ha⟩,fun x hx y hy => (hreach x hx).symm.trans (hreach y hy)⟩

/-- If a prescribed induced path contains all cycle vertices except `a`,
its initial endpoint is adjacent to `a`. The two cycle neighbours cannot both
be the unique prescribed neighbour of that endpoint. -/
lemma path_endpoint_adjacent_to_single_cycle_complement {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k) {a b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (_ha : a ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges) :
    G.Adj b a := by
  obtain ⟨i,hi⟩ := (hcover b).2 (Or.inr r.start_mem_support)
  have hplus : G.Adj b (c (i+1)) := by rw [← hi]; exact hc.adj i
  have hminus : G.Adj b (c (i-1)) := by
    rw [← hi]
    simpa only [sub_add_cancel] using (hc.adj (i-1)).symm
  rcases (hcover (c (i+1))).1 (Set.mem_range_self _) with hpa | hp
  · exact hpa ▸ hplus
  · rcases (hcover (c (i-1))).1 (Set.mem_range_self _) with hma | hm
    · exact hma ▸ hminus
    · have hp' := hr.eq_snd_of_mem_edges (hedges r.start_mem_support hp hplus)
      have hm' := hr.eq_snd_of_mem_edges (hedges r.start_mem_support hm hminus)
      have he := hc.inj (hp'.trans hm'.symm)
      have hz : (2 : ZMod k) = 0 := by linear_combination he
      exact (zmod_two_ne_zero_of_three_le hk hz).elim

/-- A short prescribed path with independent leaves attached only to its
internal vertices has no simple prescribed path on more than six vertices.
The four internal old vertices form the entire possible branching core. -/
lemma short_path_with_pendant_vertices_paths_short [Fintype V] {a b : V}
    (r : G.Walk a b) (hr : r.IsPath) (hlen : r.length ≤ 5) (hab : a ≠ b)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges)
    (R : Set V)
    (hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y)
    (hRunique : ∀ x ∈ R, ∀ y ∈ r.support, ∀ z ∈ r.support,
      G.Adj x y → G.Adj x z → y = z)
    (hRends : ∀ x ∈ R, ¬ G.Adj x a ∧ ¬ G.Adj x b)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath)
    (hsub : ∀ z ∈ q.support, z ∈ {z | z ∈ r.support} ∪ R) : q.length ≤ 5 := by
  let B := (r.support.toFinset.erase a).erase b
  have hb : b ∈ r.support.toFinset.erase a := Finset.mem_erase.2
    ⟨hab.symm,List.mem_toFinset.2 r.end_mem_support⟩
  have hcard : B.card ≤ 4 := by
    have h0 := Finset.card_erase_add_one (List.mem_toFinset.2 r.start_mem_support)
    have h1 := Finset.card_erase_add_one hb
    have h2 : r.support.toFinset.card = r.length+1 := by
      rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support]
    change (r.support.toFinset.erase a).card + 1 = r.support.toFinset.card at h0
    change B.card + 1 = (r.support.toFinset.erase a).card at h1
    omega
  apply path_length_le_five_of_small_core ({z | z ∈ r.support} ∪ R) B hcard ?_ q hq hsub
  intro z hz hzB s hs t ht hzs hzt
  rcases hz with hz | hz
  · have hzends : z = a ∨ z = b := by
      by_contra h
      push Not at h
      exact hzB (Finset.mem_erase.2 ⟨h.2,Finset.mem_erase.2 ⟨h.1,List.mem_toFinset.2 hz⟩⟩)
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · rcases hzends with rfl | rfl
      · exact (hr.eq_snd_of_mem_edges (hedges r.start_mem_support hs hzs)).trans
          (hr.eq_snd_of_mem_edges (hedges r.start_mem_support ht hzt)).symm
      · exact (hr.reverse.eq_snd_of_mem_edges (by
          simpa only [Walk.edges_reverse,List.mem_reverse] using hedges r.end_mem_support hs hzs)).trans
            (hr.reverse.eq_snd_of_mem_edges (by
              simpa only [Walk.edges_reverse,List.mem_reverse] using hedges r.end_mem_support ht hzt)).symm
    · rcases hzends with rfl | rfl
      · exact ((hRends t ht).1 hzt.symm).elim
      · exact ((hRends t ht).2 hzt.symm).elim
    · rcases hzends with rfl | rfl
      · exact ((hRends s hs).1 hzs.symm).elim
      · exact ((hRends s hs).2 hzs.symm).elim
    · rcases hzends with rfl | rfl
      · exact ((hRends s hs).1 hzs.symm).elim
      · exact ((hRends s hs).2 hzs.symm).elim
  · rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact hRunique z hz s hs t ht hzs hzt
    · exact (hRind z hz t ht hzt).elim
    · exact (hRind z hz s hs hzs).elim
    · exact (hRind z hz s hs hzs).elim

end Thomassen
