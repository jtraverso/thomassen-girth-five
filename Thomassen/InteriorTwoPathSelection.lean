/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OptionalShortEnds

/-! Selecting an actual smallest facial prefix for an interior two-edge path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Before the final face vertex, adjacency in a chordless native facial
cycle forces consecutive natural indices, with no cyclic wrap ambiguity. -/
lemma chordless_cycle_prefix_adjacent_indices (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (i j : ℕ) (hi : i + 1 < p.length) (hj : j + 1 < p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) : j = i + 1 ∨ i = j + 1 := by
  have hci := walkCycleVertices_nat_le p (by omega : i ≤ p.length)
  have hcj := walkCycleVertices_nat_le p (by omega : j ≤ p.length)
  have he := (walkCycleVertices_edges p hp _ _).2
    (hch.mem_edges (p.getVert_mem_support i) (p.getVert_mem_support j) hadj)
  rw [← hci, ← hcj] at he
  rcases (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) (i : ZMod p.length) _).1 he with h | h
  · left
    have heq : (j : ZMod p.length) = ((i + 1 : ℕ) : ZMod p.length) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (walk_isCycleMap p hp).inj h
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (by omega : j < p.length), ZMod.val_natCast_of_lt hi] using hv
  · right
    have heq : (i : ZMod p.length) = ((j + 1 : ℕ) : ZMod p.length) := by
      have h' := (walk_isCycleMap p hp).inj h
      push_cast
      linear_combination -h'
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (by omega : i < p.length), ZMod.val_natCast_of_lt hj] using hv

/-- Select the first other neighbour of the interior vertex on the specified
facial arc. Girth forces distance at least three, and minimality eliminates
every incidence to an internal vertex of the selected arc. -/
lemma first_interior_two_path_neighbour (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace M outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n)) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧ G.Adj z (p.getVert j) ∧
      ∀ t, 0 < t → t < j → ¬ G.Adj z (p.getVert t) := by
  have hex : ∃ j : ℕ, 0 < j ∧ j ≤ n ∧ G.Adj z (p.getVert j) := ⟨n, by omega, le_rfl, hzn⟩
  let j := Nat.find hex
  have hspec : 0 < j ∧ j ≤ n ∧ G.Adj z (p.getVert j) := Nat.find_spec hex
  have hmin : ∀ t, 0 < t → t < j → ¬ G.Adj z (p.getVert t) := by
    intro t ht htj hzt
    exact Nat.find_min hex htj ⟨ht, by omega, hzt⟩
  have hf : ∀ t, OnOuterFace M outer (p.getVert t) := fun t =>
    native_facial_cycle_vertices_on_outer M outer p hp hface hroot _ (p.getVert_mem_support t)
  have hj1 : j ≠ 1 := by
    intro hj
    have hzp1 : G.Adj z (p.getVert 1) := by simpa only [hj] using hspec.2.2
    exact neighbors_nonadjacent hg hza hzp1 (by simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length))
  have hj2 : j ≠ 2 := by
    intro hj
    have hzp2 : G.Adj z (p.getVert 2) := by simpa only [hj] using hspec.2.2
    have hap2 : a ≠ p.getVert 2 := by
      intro h
      have h' : p.getVert 0 = p.getVert 2 := by simpa only [Walk.getVert_zero] using h
      have he := hp.getVert_injOn' (show 0 ∈ {t | t ≤ p.length - 1} from Nat.zero_le _)
        (show 2 ∈ {t | t ≤ p.length - 1} from by change 2 ≤ p.length - 1; omega) h'
      omega
    have heq : z = p.getVert 1 := common_neighbor_unique hg hap2 hza.symm hzp2.symm
      (by simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length))
      (p.adj_getVert_succ (by omega : 1 < p.length)).symm
    exact hz (heq ▸ hf 1)
  exact ⟨j, by omega, hspec.2.1, hspec.2.2, hmin⟩

end Thomassen
