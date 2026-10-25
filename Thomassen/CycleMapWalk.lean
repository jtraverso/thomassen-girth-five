/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Native cycles preserving the order of an indexed cycle map. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Convert an indexed cycle into a native simple cycle, preserving every
vertex in its original order, including the final repeated initial vertex. -/
lemma exists_walk_of_cycleMap {k : ℕ} (hk : 3 ≤ k) {c : ZMod k → V}
    (hc : IsCycleMap G c) :
    ∃ p : G.Walk (c 0) (c 0), p.IsCycle ∧ p.length = k ∧
      ∀ i ≤ k, p.getVert i = c (i : ZMod k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  let e := ZMod.finEquiv (n + 3)
  let f : cycleGraph (n + 3) →g G := {
    toFun := fun i => c (-(e i))
    map_rel' := by
      intro i j hij
      change i - j = 1 ∨ j - i = 1 at hij
      rcases hij with h | h
      · have he : e i - e j = 1 := by simpa only [map_sub, map_one] using congrArg e h
        change G.Adj (c (-(e i))) (c (-(e j)))
        have hj : -(e j) = -(e i) + 1 := by linear_combination he
        rw [hj]
        exact hc.adj _
      · have he : e j - e i = 1 := by simpa only [map_sub, map_one] using congrArg e h
        change G.Adj (c (-(e i))) (c (-(e j)))
        have hi : -(e i) = -(e j) + 1 := by linear_combination he
        rw [hi]
        exact (hc.adj _).symm }
  have hf : Function.Injective f := by
    intro i j hij
    exact e.injective (neg_injective (hc.inj hij))
  have hzero : f 0 = c 0 := by change c (-(e 0)) = c 0; rw [map_zero, neg_zero]
  let p := ((cycleGraph.cycle n).map f).copy hzero hzero
  refine ⟨p, (Walk.isCycle_copy _ _).2 ((cycleGraph.isCycle_cycle).map hf), ?_, ?_⟩
  · simp only [p, Walk.length_copy, Walk.length_map, cycleGraph.length_cycle]
  · intro i hi
    simp only [p, Walk.getVert_copy, Walk.getVert_map]
    rw [cycleGraph.getVert_cycle hi]
    change c (-(e ⟨(n + 3 - i) % (n + 3), _⟩)) = c (i : ZMod (n + 3))
    have heq : e ⟨(n + 3 - i) % (n + 3), Nat.mod_lt _ (by omega)⟩ = ((n + 3 - i : ℕ) : ZMod (n + 3)) := by
      change (⟨(n + 3 - i) % (n + 3), _⟩ : Fin (n + 3)) = _
      rfl
    rw [heq, Nat.cast_sub hi, ZMod.natCast_self, zero_sub, neg_neg]

end Thomassen
