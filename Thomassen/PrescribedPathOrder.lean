/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortPrescriptionChord

/-! A prescribed native path follows one contiguous oriented facial arc. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- A path using cycle edges cannot change direction: doing so would repeat
its preceding vertex. The result records every original native vertex in order. -/
lemma path_cycle_order_of_first_step (hc : IsCycleMap G c) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hedges : ∀ n, n < p.length → (cyclicSubgraph G c).Adj (p.getVert n) (p.getVert (n + 1)))
    (i e : ZMod k) (he : e = 1 ∨ e = -1)
    (hzero : p.getVert 0 = c i) (hone : p.getVert 1 = c (i + e)) :
    ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simpa using hzero
  | one => intro _; simpa using hone
  | more n ih ih' =>
    intro hn
    have hprev := ih (by omega)
    have hcurrent := ih' (by omega)
    have hedge := hedges (n + 1) (by omega)
    rw [hcurrent] at hedge
    have hnext : p.getVert (n + 2) = c (i + ((n + 1 : ℕ) : ZMod k) * e + e) ∨
        p.getVert (n + 2) = c (i + ((n + 1 : ℕ) : ZMod k) * e - e) := by
      have h := (cyclicSubgraph_adj_at_iff hc _ _).1 hedge
      rcases he with rfl | rfl
      · exact h
      · simpa only [← sub_eq_add_neg, sub_neg_eq_add] using h.symm
    have hback : p.getVert (n + 2) ≠ c (i + ((n + 1 : ℕ) : ZMod k) * e - e) := by
      intro h
      have ha : i + ((n + 1 : ℕ) : ZMod k) * e - e = i + (n : ZMod k) * e := by push_cast; ring
      rw [ha, ← hprev] at h
      have hne := hp.getVert_injOn (show n + 2 ∈ {j | j ≤ p.length} from hn)
        (show n ∈ {j | j ≤ p.length} from (show n ≤ p.length by omega)) h
      omega
    have hforward := hnext.resolve_right hback
    convert hforward using 2
    push_cast
    ring

/-- Every native simple path in an indexed cycle is one oriented interval. -/
lemma path_cycle_order (hc : IsCycleMap G c) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hedges : ∀ n, n < p.length → (cyclicSubgraph G c).Adj (p.getVert n) (p.getVert (n + 1)))
    (i : ZMod k) (hstart : a = c i) :
    ∃ e : ZMod k, (e = 1 ∨ e = -1) ∧
      ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  by_cases hlen : p.length = 0
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simpa using hstart
  · have hfirst := hedges 0 (by omega)
    simp only [Walk.getVert_zero, zero_add, hstart] at hfirst
    rcases (cyclicSubgraph_adj_at_iff hc i _).1 hfirst with hforward | hbackward
    · exact ⟨1, Or.inl rfl, path_cycle_order_of_first_step hc p hp hedges i 1 (Or.inl rfl)
        (by simpa using hstart) hforward⟩
    · exact ⟨-1, Or.inr rfl, path_cycle_order_of_first_step hc p hp hedges i (-1) (Or.inr rfl)
        (by simpa using hstart) (by simpa only [← sub_eq_add_neg] using hbackward)⟩

namespace BoundaryInstance
variable {C : Type v} [Fintype V] [NeZero k]

/-- In a smallest counterexample the original prescribed path is a contiguous
arc of the actual facial cycle, in one of its two directions. No placement or
corner equations for a spliced path are silently assumed. -/
theorem prescribed_path_follows_facial_cycle (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support) :
    ∃ i e : ZMod k, (e = 1 ∨ e = -1) ∧
      ∀ n, n ≤ p.length → p.getVert n = c (i + (n : ZMod k) * e) := by
  have hget : ∀ n, p.getVert n ∈ I.precolor.vertices := fun n => (hP _).2 (p.getVert_mem_support n)
  obtain ⟨i, hi⟩ := hrange a (I.on_outer a ((hP a).2 p.start_mem_support))
  have hedges : ∀ n, n < p.length →
      (cyclicSubgraph G c).Adj (p.getVert n) (p.getVert (n + 1)) := by
    intro n hn
    obtain ⟨j, hj⟩ := hrange _ (I.on_outer _ (hget n))
    obtain ⟨l, hl⟩ := hrange _ (I.on_outer _ (hget (n + 1)))
    have hcon := I.prescribed_adj_consecutive_of_minimal_counterexample hc hk hface hG hbad hsmall j l
      (hj ▸ hget n) (hl ▸ hget (n + 1)) (by rw [hj, hl]; exact p.adj_getVert_succ hn)
    rw [← hj, ← hl]
    apply (cyclicSubgraph_adj_at_iff hc j _).2
    exact hcon.elim (fun h => Or.inl (congrArg c h)) (fun h => Or.inr (congrArg c (by linear_combination -h)))
  obtain ⟨e, he, horder⟩ := path_cycle_order hc p hp hedges i hi.symm
  exact ⟨i, e, he, horder⟩

end BoundaryInstance
end Thomassen
