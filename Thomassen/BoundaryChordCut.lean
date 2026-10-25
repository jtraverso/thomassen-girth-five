/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FaceOrbitCycle

/-! Actual chord cuts obtained directly from a simple facial boundary. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V}

/-- Follow the first `j` edges of the old boundary and close with a chord. -/
def prefixCycleVertex (c : ZMod k → V) (j : ℕ) : ZMod (j + 1) → V :=
  fun i => c (i.val : ZMod k)

omit [NeZero k] in
lemma prefixCycleVertex_zero (j : ℕ) : prefixCycleVertex c j 0 = c 0 := by
  simp only [prefixCycleVertex, ZMod.val_zero, Nat.cast_zero]

omit [NeZero k] in
lemma prefixCycleVertex_last (j : ℕ) : prefixCycleVertex c j (-1) = c (j : ZMod k) := by
  simp only [prefixCycleVertex, ZMod.val_neg_one]

omit [NeZero k] in
lemma prefixCycleVertex_injective (hc : IsCycleMap G c) (j : ℕ) (hj : j < k) :
    Function.Injective (prefixCycleVertex c j) := by
  intro i t heq
  have heq' := congrArg ZMod.val (hc.inj heq)
  have hi : i.val < k := (ZMod.val_lt i).trans_le (by omega)
  have ht : t.val < k := (ZMod.val_lt t).trans_le (by omega)
  simp only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt ht] at heq'
  exact ZMod.val_injective _ heq'

omit [NeZero k] in
lemma prefixCycleVertex_next (j : ℕ) (hj : 1 ≤ j) (i : ZMod (j + 1))
    (hi : i.val < j) : prefixCycleVertex c j (i + 1) = c ((i.val : ZMod k) + 1) := by
  let : Fact (1 < j + 1) := ⟨by omega⟩
  simp only [prefixCycleVertex, ZMod.val_add, ZMod.val_one,
    Nat.mod_eq_of_lt (by omega : i.val + 1 < j + 1), Nat.cast_add, Nat.cast_one]

omit [NeZero k] in
lemma prefixCycleVertex_prev (j : ℕ) (i : ZMod (j + 1)) (hi : 0 < i.val) :
    prefixCycleVertex c j (i - 1) = c ((i.val : ZMod k) - 1) := by
  have hcast : ((i.val : ℕ) : ZMod (j + 1)) = i := ZMod.natCast_zmod_val i
  have hprev : (((i.val - 1 : ℕ) : ZMod (j + 1))) = i - 1 := by
    rw [Nat.cast_sub hi, hcast, Nat.cast_one]
  rw [prefixCycleVertex, ← hprev, ZMod.val_natCast_of_lt (by have := ZMod.val_lt i; omega)]
  rw [Nat.cast_sub hi, Nat.cast_one]

omit [NeZero k] in
lemma prefixCycleVertex_isCycleMap (hc : IsCycleMap G c) (j : ℕ)
    (hj : 2 ≤ j) (hjk : j < k) (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    IsCycleMap G (prefixCycleVertex c j) := by
  refine ⟨prefixCycleVertex_injective hc j hjk, ?_⟩
  intro i
  by_cases hi : i.val < j
  · rw [prefixCycleVertex_next j (by omega) i hi]
    exact hc.adj _
  · have hival : i.val = j := by have := ZMod.val_lt i; omega
    have hnext : i + 1 = 0 := by
      rw [← ZMod.natCast_zmod_val i, hival]
      simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (j + 1)
    simpa only [prefixCycleVertex, hival, hnext, ZMod.val_zero, Nat.cast_zero] using hchord

omit [NeZero k] in
/-- Every internal corner of the chord cycle is an unchanged original corner. -/
lemma prefixCycleVertex_isFacialArc (M : PlaneMap G) (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) (j : ℕ) (hj : 2 ≤ j) (hjk : j < k)
    (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    IsFacialCycleArc M (prefixCycleVertex_isCycleMap hc j hj hjk hchord) := by
  let hp := prefixCycleVertex_isCycleMap hc j hj hjk hchord
  have hd : ∀ i : ZMod (j + 1), i.val < j →
      toDart cyclicSubgraph_le (cycleForward hp i) =
        toDart cyclicSubgraph_le (cycleForward hc (i.val : ZMod k)) := by
    intro i hi
    apply (Dart.ext_iff _ _).2
    exact Prod.ext rfl (prefixCycleVertex_next j (by omega) i hi)
  intro i hi0 hilast
  have hinot0 : i ≠ 0 := fun heq => hi0 (heq ▸ rfl)
  have hinotlast : i ≠ -1 := fun heq => hilast (heq ▸ rfl)
  have hipos : 0 < i.val := by
    by_contra h
    exact hinot0 (ZMod.val_injective _ (by simpa only [ZMod.val_zero] using (by omega : i.val = 0)))
  have hilt : i.val < j := by
    have hiv := ZMod.val_lt i
    by_contra h
    have hival : i.val = j := by omega
    exact hinotlast (ZMod.val_injective _ (by simpa only [ZMod.val_neg_one, Nat.add_sub_cancel] using hival))
  have hiprev : (i - 1).val = i.val - 1 := by
    have heq : (((i.val - 1 : ℕ) : ZMod (j + 1))) = i - 1 := by
      rw [Nat.cast_sub hipos, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [← heq, ZMod.val_natCast_of_lt (by have := ZMod.val_lt i; omega)]
  rw [hd i hilt, hd (i - 1) (by omega), hiprev, Nat.cast_sub hipos, Nat.cast_one]
  exact hface (i.val : ZMod k) (Set.mem_univ _)

variable [Fintype V]

omit [NeZero k] in
/-- A chord of the actual full facial boundary gives a genuine strict cut.
All retained old face vertices lie on a selected face of each piece. -/
theorem full_face_chord_separation (M : PlaneMap G) (hc : IsCycleMap G c) (_hk : 3 ≤ k)
    (hface : IsFacialCycleAlong M hc Set.univ) (hG : G.Preconnected)
    (j : ℕ) (hj : 2 ≤ j) (hjk : j + 2 ≤ k) (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {c 0, c (j : ZMod k)} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 →
          OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 →
          OnOuterFace (inducedPlaneMap M T) o x) := by
  let hp := prefixCycleVertex_isCycleMap hc j hj (by omega) hchord
  have hroot : toDart cyclicSubgraph_le (cycleForward hp 0) =
      toDart cyclicSubgraph_le (cycleForward hc 0) := by
    apply (Dart.ext_iff _ _).2
    refine Prod.ext (prefixCycleVertex_zero j) ?_
    change prefixCycleVertex c j (0 + 1) = c (0 + 1)
    simpa only [ZMod.val_zero, Nat.cast_zero] using prefixCycleVertex_next (c := c) j (by omega) 0 (by simp only [ZMod.val_zero]; omega)
  have houtside : ∃ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hp 0)) x ∧
      x ∉ Set.range (prefixCycleVertex c j) := by
    refine ⟨c ((j + 1 : ℕ) : ZMod k), ?_, ?_⟩
    · rw [hroot]
      -- Iterating the original corners keeps every original cycle dart on this face.
      have hs : ∀ n : ℕ, SameCycle M.facePerm
          (toDart cyclicSubgraph_le (cycleForward hc 0))
          (toDart cyclicSubgraph_le (cycleForward hc (n : ZMod k))) := by
        intro n
        induction n with
        | zero => simpa only [Nat.cast_zero] using SameCycle.refl M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
        | succ n ih =>
          have hf := hface ((n : ZMod k) + 1) (Set.mem_univ _)
          rw [add_sub_cancel_right] at hf
          have hstep : SameCycle M.facePerm
              (toDart cyclicSubgraph_le (cycleForward hc (n : ZMod k)))
              (toDart cyclicSubgraph_le (cycleForward hc ((n : ZMod k) + 1))) := by
            rw [← hf]
            exact (SameCycle.refl _ _).apply_right
          simpa only [Nat.cast_add, Nat.cast_one] using ih.trans hstep
      exact ⟨_, hs (j + 1), rfl⟩
    · rintro ⟨i, hi⟩
      have heq := congrArg ZMod.val (hc.inj hi)
      have hival : i.val < k := (ZMod.val_lt i).trans_le (by omega)
      simp only [ZMod.val_natCast_of_lt hival, ZMod.val_natCast_of_lt (by omega : j + 1 < k)] at heq
      have hiv := ZMod.val_lt i
      omega
  obtain ⟨S, T, hSsmall, hTsmall, hcov, hinter, hedges, hSc, hTc, _, _, _, _⟩ :=
    facial_arc_chord_separation M hp (by omega)
      (prefixCycleVertex_isFacialArc M hc hface j hj (by omega) hchord) hG houtside
  have hinter' : S ∩ T = {c 0, c (j : ZMod k)} := by
    simpa only [prefixCycleVertex_zero, prefixCycleVertex_last] using hinter
  have h0 : c 0 ∈ S ∩ T := by rw [hinter']; exact Or.inl rfl
  have hj' : c (j : ZMod k) ∈ S ∩ T := by rw [hinter']; exact Or.inr rfl
  have hAdjS : (G.induce S).Adj ⟨c 0, h0.1⟩ ⟨c (j : ZMod k), hj'.1⟩ := hchord.symm
  let : Nontrivial S := hAdjS.nontrivial
  have hAdjT : (G.induce T).Adj ⟨c 0, h0.2⟩ ⟨c (j : ZMod k), hj'.2⟩ := hchord.symm
  let : Nontrivial T := hAdjT.nontrivial
  refine ⟨S, T, hSsmall, hTsmall, hcov, ?_, hedges, hSc, hTc,
    exists_outer_induced_of_preconnected M _ S hSc.preconnected,
    exists_outer_induced_of_preconnected M _ T hTc.preconnected⟩
  simpa only [prefixCycleVertex_zero, prefixCycleVertex_last] using hinter

end Thomassen
