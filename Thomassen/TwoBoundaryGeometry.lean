/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PendantResidualReduction

/-! The two-vertex complement of a contiguous prescribed boundary path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- An external cycle edge can meet a simple path in the cycle graph only at
an endpoint: an internal path vertex already uses its two cycle neighbours. -/
lemma cycle_path_attachment_is_endpoint (hc : IsCycleMap G c) {b t x y : V}
    (r : G.Walk b t) (hr : r.IsPath) (hx : x ∈ r.support) (hy : y ∉ r.support)
    (hrange : ∀ z ∈ r.support, z ∈ Set.range c)
    (hedges : ∀ {z w}, z ∈ r.support → w ∈ r.support → G.Adj z w →
      (cyclicSubgraph G c).Adj z w)
    (hxy : (cyclicSubgraph G c).Adj x y) : x = b ∨ x = t := by
  obtain ⟨n,hnx,hn⟩ := Walk.mem_support_iff_exists_getVert.1 hx
  by_cases hn0 : n = 0
  · exact Or.inl (by simpa only [hn0,Walk.getVert_zero] using hnx.symm)
  · by_cases hnl : n = r.length
    · exact Or.inr (by simpa only [hnl,Walk.getVert_length] using hnx.symm)
    · obtain ⟨i,hi⟩ := hrange x hx
      have hprev : (cyclicSubgraph G c).Adj x (r.getVert (n-1)) := by
        rw [← hnx]
        apply hedges (r.getVert_mem_support _) (r.getVert_mem_support _)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
          (r.adj_getVert_succ (by omega : n-1 < r.length)).symm
      have hnext : (cyclicSubgraph G c).Adj x (r.getVert (n+1)) := by
        rw [← hnx]
        exact hedges (r.getVert_mem_support _) (r.getVert_mem_support _) (r.adj_getVert_succ (by omega))
      have hne : r.getVert (n-1) ≠ r.getVert (n+1) := by
        intro h
        have he := hr.getVert_injOn (by change n-1 ≤ r.length; omega)
          (by change n+1 ≤ r.length; omega) h
        omega
      have ht : y = r.getVert (n-1) ∨ y = r.getVert (n+1) :=
        cyclicSubgraph_third_neighbour hc i (by rwa [hi]) (by rwa [hi]) (by rwa [hi]) hne
      rcases ht with h | h
      all_goals exact (hy (h ▸ r.getVert_mem_support _)).elim

/-- An endpoint of an induced path lying on a cycle has a neighbour in the
cycle complement. This applies to either endpoint and any complement size. -/
lemma path_endpoint_has_cycle_complement_neighbour [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {b t : V} (r : G.Walk b t) (hr : r.IsPath)
    (A : Set V) (hcover : ∀ x, x ∈ Set.range c ↔ x ∈ A ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges) :
    ∃ x ∈ A, G.Adj b x := by
  obtain ⟨i,hi⟩ := (hcover b).2 (Or.inr r.start_mem_support)
  have hplus : G.Adj b (c (i+1)) := by rw [← hi]; exact hc.adj i
  have hminus : G.Adj b (c (i-1)) := by
    rw [← hi]
    simpa only [sub_add_cancel] using (hc.adj (i-1)).symm
  rcases (hcover (c (i+1))).1 (Set.mem_range_self _) with hpA | hp
  · exact ⟨_,hpA,hplus⟩
  · rcases (hcover (c (i-1))).1 (Set.mem_range_self _) with hmA | hm
    · exact ⟨_,hmA,hminus⟩
    · have he := hc.inj ((hr.eq_snd_of_mem_edges (hedges r.start_mem_support hp hplus)).trans
        (hr.eq_snd_of_mem_edges (hedges r.start_mem_support hm hminus)).symm)
      have hz : (2 : ZMod k) = 0 := by linear_combination he
      exact (zmod_two_ne_zero_of_three_le hk hz).elim

/-- If two vertices form the entire cycle complement of a path and are not
adjacent, each is adjacent to both path endpoints. -/
lemma cycle_complement_vertex_adjacent_both_path_ends [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (ha : a ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y)
    (had : ¬ G.Adj a d) : G.Adj a b ∧ G.Adj a t := by
  obtain ⟨i,hi⟩ := (hcover a).2 (Or.inl rfl)
  have hplus : G.Adj a (c (i+1)) := by rw [← hi]; exact hc.adj i
  have hminus : G.Adj a (c (i-1)) := by
    rw [← hi]
    simpa only [sub_add_cancel] using (hc.adj (i-1)).symm
  have hp : c (i+1) ∈ r.support := by
    rcases (hcover _).1 (Set.mem_range_self (i+1)) with h | h | h
    · exact (hplus.ne h.symm).elim
    · exact (had (h ▸ hplus)).elim
    · exact h
  have hm : c (i-1) ∈ r.support := by
    rcases (hcover _).1 (Set.mem_range_self (i-1)) with h | h | h
    · exact (hminus.ne h.symm).elim
    · exact (had (h ▸ hminus)).elim
    · exact h
  have hrange : ∀ x ∈ r.support, x ∈ Set.range c := fun x hx => (hcover x).2 (Or.inr (Or.inr hx))
  have hpends := cycle_path_attachment_is_endpoint hc r hr hp ha hrange hedges
    (by rw [← hi]; exact (cycleForward hc i).adj.symm)
  have hmends := cycle_path_attachment_is_endpoint hc r hr hm ha hrange hedges
    (by rw [← hi]; exact (cycleBackward hc i).adj.symm)
  have hne : c (i+1) ≠ c (i-1) := by
    intro h
    have he := hc.inj h
    have hz : (2 : ZMod k) = 0 := by linear_combination he
    exact zmod_two_ne_zero_of_three_le hk hz
  rcases hpends with hpends | hpends <;> rcases hmends with hmends | hmends
  · exact (hne (hpends.trans hmends.symm)).elim
  · exact ⟨hpends ▸ hplus,hmends ▸ hminus⟩
  · exact ⟨hmends ▸ hminus,hpends ▸ hplus⟩
  · exact (hne (hpends.trans hmends.symm)).elim

/-- Exactly two vertices outside a nontrivial prescribed cycle path must be
consecutive in girth at least five. Otherwise the two free vertices and both
path endpoints form a forbidden four-cycle. -/
theorem two_cycle_complement_adjacent [NeZero k] (hg : 5 ≤ G.egirth)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (ha : a ∉ r.support) (hd : d ∉ r.support)
    (had : a ≠ d) (hbt : b ≠ t)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y) : G.Adj a d := by
  by_contra h
  obtain ⟨hab,hat⟩ := cycle_complement_vertex_adjacent_both_path_ends hc hk r hr ha hcover hedges h
  obtain ⟨hdb,hdt⟩ := cycle_complement_vertex_adjacent_both_path_ends hc hk r hr hd
    (by intro x; rw [hcover]; tauto) hedges (fun h' => h h'.symm)
  exact had (common_neighbor_unique hg hbt hab.symm hat.symm hdb.symm hdt.symm)

/-- Each end of the complementary cycle edge has exactly one prescribed
neighbour. Extra original-graph edges are checked against the cycle graph. -/
lemma cycle_complement_edge_endpoint_unique_path_neighbour [NeZero k]
    (hc : IsCycleMap G c) (hk : 3 ≤ k) {a d b t : V} (r : G.Walk b t)
    (_ha : a ∉ r.support) (hd : d ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support)
    (had : (cyclicSubgraph G c).Adj a d)
    (hch : ∀ x ∈ r.support, G.Adj a x → (cyclicSubgraph G c).Adj a x) :
    ∃ z ∈ r.support, G.Adj a z ∧ ∀ x ∈ r.support, G.Adj a x → x = z := by
  obtain ⟨i,hi⟩ := (hcover a).2 (Or.inl rfl)
  have hplus : G.Adj a (c (i+1)) := by rw [← hi]; exact hc.adj i
  have hminus : G.Adj a (c (i-1)) := by
    rw [← hi]
    simpa only [sub_add_cancel] using (hc.adj (i-1)).symm
  have hne : c (i+1) ≠ c (i-1) := by
    intro h
    have he := hc.inj h
    have hz : (2 : ZMod k) = 0 := by linear_combination he
    exact zmod_two_ne_zero_of_three_le hk hz
  have hex : ∃ z ∈ r.support, G.Adj a z := by
    rcases (hcover _).1 (Set.mem_range_self (i+1)) with h | h | h
    · exact (hplus.ne h.symm).elim
    · rcases (hcover _).1 (Set.mem_range_self (i-1)) with h' | h' | h'
      · exact (hminus.ne h'.symm).elim
      · exact (hne (h.trans h'.symm)).elim
      · exact ⟨_,h',hminus⟩
    · exact ⟨_,h,hplus⟩
  obtain ⟨z,hz,haz⟩ := hex
  refine ⟨z,hz,haz,?_⟩
  intro x hx hax
  have hdz : d ≠ z := fun h => hd (h ▸ hz)
  have hx' : x = d ∨ x = z := cyclicSubgraph_third_neighbour hc i
    (by rwa [hi]) (by rw [hi]; exact hch z hz haz) (by rw [hi]; exact hch x hx hax) hdz
  exact hx'.resolve_left (fun h => hd (h ▸ hx))

end Thomassen
