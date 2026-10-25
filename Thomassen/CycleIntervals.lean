/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ArcPathSeparation

/-! Actual connected cycle intervals for the short interior-path cut. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V}

/-- The vertices of a consecutive segment of the actual indexed cycle. -/
def cycleInterval (c : ZMod k → V) (start length : ℕ) : Set V :=
  {x | ∃ i : ℕ, i ≤ length ∧ c ((start + i : ℕ) : ZMod k) = x}

omit [NeZero k] in
lemma cycleInterval_zero (start : ℕ) : cycleInterval c start 0 = {c (start : ZMod k)} := by
  ext x
  simp [cycleInterval, eq_comm]

omit [NeZero k] in
lemma cycleInterval_succ (start length : ℕ) :
    cycleInterval c start (length + 1) =
      insert (c ((start + (length + 1) : ℕ) : ZMod k)) (cycleInterval c start length) := by
  ext x
  constructor
  · rintro ⟨i, hi, hix⟩
    by_cases heq : i = length + 1
    · exact Or.inl (hix.symm.trans (congrArg (fun j : ℕ => c ((start + j : ℕ) : ZMod k)) heq))
    · exact Or.inr ⟨i, by omega, hix⟩
  · rintro (h | ⟨i, hi, hix⟩)
    · exact ⟨length + 1, le_rfl, h.symm⟩
    · exact ⟨i, by omega, hix⟩

omit [NeZero k] in
/-- These are connected sets in the cycle graph itself, not only in G. -/
lemma cycleInterval_connSet (hc : IsCycleMap G c) (start length : ℕ) :
    ConnSet (cyclicSubgraph G c) (cycleInterval c start length) := by
  induction length with
  | zero => rw [cycleInterval_zero]; exact connSet_singleton _ _
  | succ n ih =>
    rw [cycleInterval_succ]
    apply ih.insert_adj (b := c ((start + n : ℕ) : ZMod k)) ⟨n, le_rfl, rfl⟩
    have h := (cycleForward hc ((start + n : ℕ) : ZMod k)).adj.symm
    simpa only [cycleForward, Nat.cast_add, Nat.cast_one, add_assoc] using h

omit [NeZero k] in
lemma cycleInterval_subset (start length : ℕ) : cycleInterval c start length ⊆ Set.range c :=
  fun _ ⟨i, _, h⟩ => ⟨((start + i : ℕ) : ZMod k), h⟩

/-- Splitting the cycle into an open old arc and a closed returning path gives
an exact partition. Only the genuine cycle indices are used. -/
lemma cycleInterval_partition (hc : IsCycleMap G c) {n m : ℕ} (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hk : k = n + m) :
    Set.range c \ cycleInterval c 1 (n - 2) = cycleInterval c n m := by
  have hSmall : ∀ i ≤ n - 2, 0 < 1 + i ∧ 1 + i < n ∧ 1 + i < k := by
    intro i hi
    omega
  have hDisj : Disjoint (cycleInterval c 1 (n - 2)) (cycleInterval c n m) := by
    rw [Set.disjoint_left]
    rintro x ⟨i, hi, hix⟩ ⟨j, hj, hjx⟩
    have heq := congrArg ZMod.val (hc.inj (hix.trans hjx.symm))
    rw [ZMod.val_natCast_of_lt (hSmall i hi).2.2, ZMod.val_natCast] at heq
    by_cases hjlast : n + j = k
    · rw [hjlast, Nat.mod_self] at heq
      omega
    · rw [Nat.mod_eq_of_lt (by omega : n + j < k)] at heq
      omega
  ext x
  constructor
  · rintro ⟨⟨i, rfl⟩, hxA⟩
    by_cases hzero : i.val = 0
    · refine ⟨m, le_rfl, ?_⟩
      rw [← hk, ZMod.natCast_self]
      exact congrArg c (ZMod.val_injective k (by simpa using hzero.symm))
    · by_cases hlt : i.val < n
      · exact (hxA ⟨i.val - 1, by omega, by
          rw [show 1 + (i.val - 1) = i.val by omega, ZMod.natCast_zmod_val]⟩).elim
      · exact ⟨i.val - n, by have := ZMod.val_lt i; omega, by
          rw [Nat.add_sub_of_le (by omega : n ≤ i.val), ZMod.natCast_zmod_val]⟩
  · intro hx
    exact ⟨cycleInterval_subset n m hx, fun hA => Set.disjoint_left.1 hDisj hA hx⟩

omit [NeZero k] in
/-- Girth excludes all nonconsecutive edges in a returning path of at most
three edges. This discharges the separator chord condition geometrically. -/
lemma cycleInterval_short_complete (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (start length : ℕ) (hlen : length ≤ 3)
    {x y : V} (hx : x ∈ cycleInterval c start length) (hy : y ∈ cycleInterval c start length)
    (hxy : G.Adj x y) : (cyclicSubgraph G c).Adj x y := by
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  have hnear : ∀ i j : ℕ, i ≤ length → j ≤ length → i ≤ j →
      G.Adj (c ((start + i : ℕ) : ZMod k)) (c ((start + j : ℕ) : ZMod k)) →
      (cyclicSubgraph G c).Adj (c ((start + i : ℕ) : ZMod k)) (c ((start + j : ℕ) : ZMod k)) := by
    intro i j hi hj hij hxy
    rcases (by omega : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3) with h | h | h | h
    · subst j
      exact (hxy.ne rfl).elim
    · subst j
      have he := (cycleForward hc ((start + i : ℕ) : ZMod k)).adj
      simpa only [cycleForward, Nat.cast_add, Nat.cast_one, add_assoc] using he
    · exact (cycle_no_chord_two hg hc ((start + i : ℕ) : ZMod k)
        (by simpa only [h, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hxy)).elim
    · exact (cycle_no_chord_three hg hc hk ((start + i : ℕ) : ZMod k)
        (by simpa only [h, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hxy)).elim
  rcases le_total i j with h | h
  · exact hnear i j hi hj h hxy
  · exact (hnear j i hj hi h hxy.symm).symm

variable [Fintype V]

/-- Concrete path cut with a separator of at most three edges. The arc and
separator are explicit consecutive cycle intervals. Girth supplies the absence
of extra separator chords; their connectivity and exact partition are proved. -/
theorem short_arc_path_separation (M : PlaneMap G) (hg : 5 ≤ G.egirth)
    (hc : IsCycleMap G c) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hk : k = n + m) (hArc : IsFacialCycleAlong M hc (cycleInterval c 1 (n - 2)))
    (hconn : G.Preconnected)
    (houtside : ∃ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x ∧
      x ∉ Set.range c) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = cycleInterval c n m ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ Set.range c, x ∈ S) ∧
      (∀ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x →
        x ∉ cycleInterval c 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ Set.range c) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 ∨
          x.1 ∈ cycleInterval c n m → OnOuterFace N o x) := by
  have h3 : 3 ≤ k := by omega
  have hpart := cycleInterval_partition hc hn hm hk
  have hZeroB : c 0 ∈ Set.range c \ cycleInterval c 1 (n - 2) := by
    rw [hpart]
    refine ⟨m, le_rfl, ?_⟩
    rw [← hk, ZMod.natCast_self]
  have hlast : ((k - 1 : ℕ) : ZMod k) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hBackB : c (-1) ∈ Set.range c \ cycleInterval c 1 (n - 2) := by
    rw [hpart]
    exact ⟨m - 1, by omega, by rw [show n + (m - 1) = k - 1 by omega, hlast]⟩
  have hJB : c (n : ZMod k) ∈ Set.range c \ cycleInterval c 1 (n - 2) := by
    rw [hpart]
    exact ⟨0, by omega, by rw [Nat.add_zero]⟩
  have hJA : c ((n : ZMod k) - 1) ∈ cycleInterval c 1 (n - 2) := by
    refine ⟨n - 2, le_rfl, ?_⟩
    rw [show 1 + (n - 2) = n - 1 by omega, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSconn, hTconn,
    hSC, hkeep, hSface, hTface⟩ := facial_arc_path_separation M hc h3
      (cycleInterval c 1 (n - 2)) (cycleInterval_subset 1 (n - 2)) hArc
      (cycleInterval_connSet hc 1 (n - 2))
      (by rw [hpart]; exact cycleInterval_connSet hc n m)
      (fun {_ _} hx hy hxy => cycleInterval_short_complete hg hc h3 n m hm3
        (hpart ▸ hx) (hpart ▸ hy) hxy)
      hZeroB.2 ⟨0, by omega, by simp⟩ hBackB.2 n hJB.2 hJA hconn houtside
  refine ⟨S, T, hSsmall, hTsmall, hcover, hinter.trans hpart, hedges, hSconn, hTconn,
    hSC, hkeep, hSface, ?_⟩
  simpa only [hpart] using hTface

end Thomassen
