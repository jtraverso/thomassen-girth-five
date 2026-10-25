/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CompatibleShortEndedPath

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- For a path of at most five edges, girth excludes all chords spanning two
or three edges. Only the explicitly excluded longer chords need checking. -/
lemma five_edge_path_isChordless_of_no_long_chords (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 5)
    (hfar : ∀ i j : ℕ, i+4 ≤ j → j ≤ q.length → ¬ G.Adj (q.getVert i) (q.getVert j)) : q.IsChordless := by
  apply Walk.isChordless_iff_forall_mem_edges.2
  intro x y hx hy hxy
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
  obtain ⟨j, hjy, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hy
  subst x
  subst y
  have hnear : ∀ i j : ℕ, i ≤ q.length → j ≤ q.length → i ≤ j →
      G.Adj (q.getVert i) (q.getVert j) → s(q.getVert i, q.getVert j) ∈ q.edges := by
    intro i j hi hj hij hxy
    rcases (by omega : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 ∨ j = i + 5) with h | h | h | h | h | h
    · exact (hxy.ne (congrArg q.getVert h.symm)).elim
    · apply q.mk_mem_edges_iff_exists.2
      exact ⟨i, by omega, by rw [h]⟩
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h02 : G.Adj (q.getVert i) (q.getVert (i + 2)) := by rwa [h] at hxy
      exact (neighbors_nonadjacent hg h01 h02 (by simpa only [Nat.add_assoc] using h12)).elim
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h23 := q.adj_getVert_succ (by omega : i + 2 < q.length)
      have hne : q.getVert i ≠ q.getVert (i + 2) := fun heq => by
        have hidx := hp.getVert_injOn hi (by change i + 2 ≤ q.length; omega) heq
        omega
      have h03 : G.Adj (q.getVert i) (q.getVert (i + 3)) := by rwa [h] at hxy
      have heq := common_neighbor_unique hg hne h01
        (by simpa only [Nat.add_assoc] using h12.symm) h03
        (by simpa only [Nat.add_assoc] using h23)
      have hidx := hp.getVert_injOn (by change i + 1 ≤ q.length; omega)
        (by change i + 3 ≤ q.length; omega) heq
      omega
    · exact (hfar i j (by omega) hj hxy).elim
    · exact (hfar i j (by omega) hj hxy).elim
  rcases le_total i j with h | h
  · exact hnear i j hi hj h hxy
  · simpa only [Sym2.eq_swap] using hnear j i hj hi h hxy.symm

end Thomassen
