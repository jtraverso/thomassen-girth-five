/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedEndpointDeletion

/-! Changing the initial vertex of an actual native facial cycle. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Every forward cycle dart belongs to the original actual face orbit. -/
lemma facial_cycle_forward_sameCycle (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) (i : ZMod k) :
    SameCycle M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
      (toDart cyclicSubgraph_le (cycleForward hc i)) := by
  have hstep : ∀ n : ℕ, SameCycle M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
      (toDart cyclicSubgraph_le (cycleForward hc (n : ZMod k))) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero] using SameCycle.refl M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
    | succ n ih =>
      have hf := hface ((n : ZMod k) + 1) (Set.mem_univ _)
      rw [add_sub_cancel_right] at hf
      have hn : SameCycle M.facePerm (toDart cyclicSubgraph_le (cycleForward hc (n : ZMod k)))
          (toDart cyclicSubgraph_le (cycleForward hc ((n : ZMod k) + 1))) := by
        rw [← hf]
        exact (SameCycle.refl _ _).apply_right
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans hn
  simpa only [ZMod.natCast_zmod_val] using hstep i.val

/-- A native cycle with the exact order of an indexed facial cycle inherits
its original face corners and exact first dart. -/
lemma ordered_native_cycle_isFacial (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length = k) (horder : ∀ i ≤ k, p.getVert i = c (i : ZMod k)) :
    IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧
      walkArcRoot p hp = toDart cyclicSubgraph_le (cycleForward hc 0) := by
  subst k
  have heq : walkCycleVertices p = c := by
    funext i
    change p.getVert i.val = c i
    simpa only [ZMod.natCast_zmod_val] using horder i.val (Nat.le_of_lt (ZMod.val_lt i))
  subst c
  exact ⟨hface, rfl⟩

/-- Rebase the old actual facial cycle at any chosen native position, without
changing its orientation. Every new native vertex and the old face orbit are
retained explicitly. -/
theorem exists_rebased_native_face_cycle (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (s : ℕ) (hs : s < p.length) :
    ∃ q : G.Walk (p.getVert s) (p.getVert s), ∃ hq : q.IsCycle,
      q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s + i : ℕ) : ZMod p.length)) ∧
      IsFacialCycleAlong M (walk_isCycleMap q hq) Set.univ ∧
      SameCycle M.facePerm outer (walkArcRoot q hq) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let c : ZMod p.length → V := fun i => walkCycleVertices p ((s : ZMod p.length) + i)
  have hc : IsCycleMap G c := {
    inj := fun x y h => add_left_cancel ((walk_isCycleMap p hp).inj h)
    adj := fun i => by simpa only [c, add_assoc] using (walk_isCycleMap p hp).adj ((s : ZMod p.length) + i) }
  have hdart : ∀ i : ZMod p.length, toDart cyclicSubgraph_le (cycleForward hc i) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) ((s : ZMod p.length) + i)) := by
    intro i
    apply (Dart.ext_iff _ _).2
    exact Prod.ext rfl (by change walkCycleVertices p ((s : ZMod p.length) + (i + 1)) = walkCycleVertices p (((s : ZMod p.length) + i) + 1); rw [add_assoc])
  have hfc : IsFacialCycleAlong M hc Set.univ := by
    intro i _
    rw [hdart, hdart, show (s : ZMod p.length) + (i - 1) = ((s : ZMod p.length) + i) - 1 by ring]
    exact hface ((s : ZMod p.length) + i) (Set.mem_univ _)
  obtain ⟨r, hr, hrl, hro⟩ := exists_walk_of_cycleMap hlen hc
  have hzero : c 0 = p.getVert s := by
    change walkCycleVertices p ((s : ZMod p.length) + 0) = _
    rw [add_zero, walkCycleVertices_nat_le p (by omega)]
  let q := r.copy hzero hzero
  have hq : q.IsCycle := (Walk.isCycle_copy _ _).2 hr
  have hql : q.length = p.length := by simpa only [q, Walk.length_copy] using hrl
  have hqo : ∀ i ≤ p.length, q.getVert i = c (i : ZMod p.length) := by
    simpa only [q, Walk.getVert_copy] using hro
  obtain ⟨hqface, hqroot⟩ := ordered_native_cycle_isFacial M hc hfc q hq hql hqo
  refine ⟨q, hq, hql, ?_, hqface, ?_⟩
  · intro i hi
    simpa only [c, Nat.cast_add] using hqo i hi
  · rw [hqroot, hdart, add_zero]
    exact hroot.trans (facial_cycle_forward_sameCycle M (walk_isCycleMap p hp) hface (s : ZMod p.length))

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The chordlessness reduction applies to every native representative of the
selected face, including representatives obtained by rebasing the initial dart. -/
lemma native_face_cycle_chordless_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : p.IsChordless := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hf := native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot
  apply Walk.isChordless_iff_forall_mem_edges.2
  intro x y hx hy hxy
  obtain ⟨i, hi⟩ := (walkCycleVertices_range p hp).symm ▸ (show x ∈ {z | z ∈ p.support} from hx)
  obtain ⟨j, hj⟩ := (walkCycleVertices_range p hp).symm ▸ (show y ∈ {z | z ∈ p.support} from hy)
  have hcon := I.boundary_adj_consecutive_of_minimal_counterexample hG (walk_isCycleMap p hp) hlen hface hbad hsmall i j
    (by rw [hi]; exact hf x hx) (by rw [hj]; exact hf y hy) (by rw [hi, hj]; exact hxy)
  apply (walkCycleVertices_edges p hp x y).1
  rw [← hi, ← hj]
  apply (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) i _).2
  exact hcon.elim (fun h => Or.inl (congrArg (walkCycleVertices p) h))
    (fun h => Or.inr (congrArg (walkCycleVertices p) (by linear_combination -h)))

end BoundaryInstance
end Thomassen
