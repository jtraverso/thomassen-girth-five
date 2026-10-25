/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FacialChordNormalization
public import Thomassen.FacialSixReduction

/-! A prescribed cycle reduces to the already closed facial-cycle case. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- The only neighbours of an indexed cycle vertex in its cycle graph are
its successor and predecessor. -/
lemma cyclicSubgraph_adj_at_iff {k : ℕ} {c : ZMod k → V} (hc : IsCycleMap G c)
    (i : ZMod k) (y : V) :
    (cyclicSubgraph G c).Adj (c i) y ↔ y = c (i + 1) ∨ y = c (i - 1) := by
  constructor
  · rintro ⟨_, j, ⟨hij, hy⟩ | ⟨hij, hy⟩⟩
    · have he := hc.inj hij
      subst j
      exact Or.inl hy
    · have he := hc.inj hij
      right
      rw [hy, he, add_sub_cancel_right]
  · rintro (rfl | rfl)
    · exact (cycleForward hc i).adj
    · exact (cycleBackward hc i).adj

/-- A simple cycle contained in the cycle edges of another indexed simple
cycle must visit every vertex of that cycle. -/
lemma cycle_range_eq_of_cycle_edges {k l : ℕ} [NeZero k] [NeZero l]
    {c : ZMod k → V} {d : ZMod l → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d)
    (hl : 3 ≤ l) (hsub : Set.range d ⊆ Set.range c)
    (hedges : ∀ i : ZMod l, (cyclicSubgraph G c).Adj (d i) (d (i + 1))) :
    Set.range d = Set.range c := by
  have hclosed : ∀ i : ZMod k, c i ∈ Set.range d → c (i + 1) ∈ Set.range d := by
    intro i hi
    obtain ⟨t, ht⟩ := hi
    have hplus := (cyclicSubgraph_adj_at_iff hc i (d (t + 1))).1 (by rw [← ht]; exact hedges t)
    have hminus := (cyclicSubgraph_adj_at_iff hc i (d (t - 1))).1 (by
      rw [← ht]
      simpa only [sub_add_cancel] using (hedges (t - 1)).symm)
    have hne : d (t + 1) ≠ d (t - 1) := by
      intro heq
      have hz : (2 : ZMod l) = 0 := by have he := hd.inj heq; linear_combination he
      exact zmod_two_ne_zero_of_three_le hl hz
    rcases hplus with h | h
    · exact ⟨t + 1, h⟩
    · have hminus' := hminus.resolve_right (fun h' => hne (h.trans h'.symm))
      exact ⟨t - 1, hminus'⟩
  obtain ⟨i, hi⟩ := hsub (Set.mem_range_self (0 : ZMod l))
  have hseed : c i ∈ Set.range d := ⟨0, hi.symm⟩
  have hstep : ∀ n : ℕ, c (i + (n : ZMod k)) ∈ Set.range d := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using hseed
    | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hclosed (i + (n : ZMod k)) ih
  apply Set.Subset.antisymm hsub
  rintro x ⟨j, rfl⟩
  have h := hstep (j - i).val
  simpa only [ZMod.natCast_zmod_val, add_sub_cancel] using h

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The complete prescribed-cycle case of the main induction: a nonfacial
prescribed cycle supplies a forbidden prescribed chord; otherwise the previous
facial five/six-cycle reduction applies. -/
theorem colourable_of_prescribed_cycle (I : BoundaryInstance G C)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG, _, _, b, q, hq, _, hqface, hqArc, _⟩ :=
    I.minimal_counterexample_has_native_face_cycle hbad hsmall
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  let : NeZero q.length := ⟨by have := hq.three_le_length; omega⟩
  let c := walkCycleVertices q
  let d := walkCycleVertices p
  have hc := walk_isCycleMap q hq
  have hd := walk_isCycleMap p hp
  have hsub : Set.range d ⊆ Set.range c := by
    intro x hx
    have hxp : x ∈ p.support := by rwa [walkCycleVertices_range p hp] at hx
    have hxface := I.on_outer x ((hP x).2 hxp)
    rw [walkCycleVertices_range q hq]
    exact (hqface x).2 hxface
  have hedges : ∀ t : ZMod p.length, (cyclicSubgraph G c).Adj (d t) (d (t + 1)) := by
    intro t
    obtain ⟨i, hi⟩ := hsub (Set.mem_range_self t)
    obtain ⟨j, hj⟩ := hsub (Set.mem_range_self (t + 1))
    have hiP : c i ∈ I.precolor.vertices := by
      apply (hP _).2
      rw [hi]
      exact p.getVert_mem_support _
    have hjP : c j ∈ I.precolor.vertices := by
      apply (hP _).2
      rw [hj]
      exact p.getVert_mem_support _
    have hxy : G.Adj (c i) (c j) := by rw [hi, hj]; exact hd.adj t
    have hcons := I.prescribed_adj_consecutive_of_minimal_counterexample hc hq.three_le_length
      hqArc hG hbad hsmall i j hiP hjP hxy
    rw [← hi, ← hj]
    refine ⟨hxy, ?_⟩
    rcases hcons with h | h
    · exact ⟨i, Or.inl ⟨rfl, congrArg c h⟩⟩
    · exact ⟨j, Or.inr ⟨congrArg c h, rfl⟩⟩
  have heq := cycle_range_eq_of_cycle_edges hc hd hp.three_le_length hsub hedges
  have hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support := by
    intro x
    rw [← hqface x]
    have heq' : {x | x ∈ p.support} = {x | x ∈ q.support} := by
      simpa only [walkCycleVertices_range p hp, walkCycleVertices_range q hq] using heq
    exact (Set.ext_iff.1 heq' x).symm
  exact hbad (I.colourable_of_facial_short_cycle hG p hp hbound hP hface hsmall)

end BoundaryInstance
end Thomassen
