/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedNeighbourUniqueness

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- A path of at most four edges with independent pendant attachments has
all simple paths of length at most five if its initial endpoint has no leaves.
Only the remaining path vertices can belong to the branching core. -/
lemma four_edge_path_with_pendant_vertices_paths_short [Fintype V] {a b : V}
    (r : G.Walk a b) (hr : r.IsPath) (hlen : r.length ≤ 4)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges)
    (R : Set V)
    (hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y)
    (hRunique : ∀ x ∈ R, ∀ y ∈ r.support, ∀ z ∈ r.support,
      G.Adj x y → G.Adj x z → y = z)
    (hRstart : ∀ x ∈ R, ¬ G.Adj x a)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath)
    (hsub : ∀ z ∈ q.support, z ∈ {z | z ∈ r.support} ∪ R) : q.length ≤ 5 := by
  let B := r.support.toFinset.erase a
  have hcard : B.card ≤ 4 := by
    have h0 := Finset.card_erase_add_one (List.mem_toFinset.2 r.start_mem_support)
    have h1 : r.support.toFinset.card = r.length+1 := by
      rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support]
    change B.card + 1 = r.support.toFinset.card at h0
    omega
  apply path_length_le_five_of_small_core ({z | z ∈ r.support} ∪ R) B hcard ?_ q hq hsub
  intro z hz hzB s hs t ht hzs hzt
  rcases hz with hz | hz
  · have hza : z = a := by
      by_contra h
      exact hzB (Finset.mem_erase.2 ⟨h,List.mem_toFinset.2 hz⟩)
    subst z
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hr.eq_snd_of_mem_edges (hedges r.start_mem_support hs hzs)).trans
        (hr.eq_snd_of_mem_edges (hedges r.start_mem_support ht hzt)).symm
    · exact (hRstart t ht hzt.symm).elim
    · exact (hRstart s hs hzs.symm).elim
    · exact (hRstart s hs hzs.symm).elim
  · rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact hRunique z hz s hs t ht hzs hzt
    · exact (hRind z hz t ht hzt).elim
    · exact (hRind z hz s hs hzs).elim
    · exact (hRind z hz s hs hzs).elim

end Thomassen
