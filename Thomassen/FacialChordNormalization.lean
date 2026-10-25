/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryCutReduction
public import Thomassen.EdgeCutReduction

/-! Chords at arbitrary positions in the actual facial boundary. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V} [Fintype V]

/-- Rotating the indexed boundary allows the strict chord cut at any two
nonconsecutive boundary positions. -/
theorem full_face_chord_separation_at (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong M hc Set.univ) (hG : G.Preconnected)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {c i, c j} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected := by
  let d : ZMod k → V := fun t => c (i + t)
  have hd : IsCycleMap G d := {
    inj := fun x y h => add_left_cancel (hc.inj h)
    adj := fun t => by simpa only [d, add_assoc] using hc.adj (i + t) }
  have hdart : ∀ t : ZMod k, toDart cyclicSubgraph_le (cycleForward hd t) =
      toDart cyclicSubgraph_le (cycleForward hc (i + t)) := by
    intro t
    apply (Dart.ext_iff _ _).2
    exact Prod.ext rfl (by change c (i + (t + 1)) = c (i + t + 1); rw [add_assoc])
  have hfd : IsFacialCycleAlong M hd Set.univ := by
    intro t _
    rw [hdart, hdart, show i + (t - 1) = (i + t) - 1 by ring]
    exact hface (i + t) (Set.mem_univ _)
  let t : ZMod k := j - i
  have htv : t.val < k := ZMod.val_lt t
  have ht0 : t.val ≠ 0 := by
    intro hv
    have ht : t = 0 := by rw [← ZMod.natCast_zmod_val t, hv, Nat.cast_zero]
    have hij : i = j := by change j - i = 0 at ht; linear_combination -ht
    exact hadj.ne (congrArg c hij)
  have ht1 : t.val ≠ 1 := by
    intro hv
    have ht : t = 1 := by rw [← ZMod.natCast_zmod_val t, hv, Nat.cast_one]
    apply hforward
    change j - i = 1 at ht
    linear_combination ht
  have htm : t.val ≠ k - 1 := by
    intro hv
    have ht : t = -1 := by
      rw [← ZMod.natCast_zmod_val t, hv, Nat.cast_sub (by omega : 1 ≤ k),
        ZMod.natCast_self, Nat.cast_one, zero_sub]
    apply hbackward
    change j - i = -1 at ht
    linear_combination -ht
  have hd0 : d 0 = c i := by simp only [d, add_zero]
  have hdt : d (t.val : ZMod k) = c j := by simp only [d, ZMod.natCast_zmod_val, t, add_sub_cancel]
  obtain ⟨S, T, hS, hT, hcov, hinter, hedges, hSc, hTc, _, _⟩ :=
    full_face_chord_separation M hd hk hfd hG t.val (by omega) (by omega)
      (by rw [hdt, hd0]; exact hadj.symm)
  exact ⟨S, T, hS, hT, hcov, by simpa only [hd0, hdt] using hinter, hedges, hSc, hTc⟩

namespace BoundaryInstance
variable {C : Type v}

/-- Every chord with both ends prescribed is eliminated directly on the
actual simple facial boundary, without a supplied arc or separator witness. -/
theorem colourable_of_prescribed_boundary_chord (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hG : G.Preconnected) (i j : ZMod k) (hadj : G.Adj (c i) (c j))
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hS, hT, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
  exact I.colourable_of_prescribed_edge_cut S T hadj hiP hjP hcover hinter hedges hSc hTc hS hT hsmall

/-- All original edges between prescribed vertices follow the simple outer
cycle of a smallest counterexample. -/
lemma prescribed_adj_consecutive_of_minimal_counterexample (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∈ I.precolor.vertices)
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  by_contra h
  push Not at h
  exact hbad (I.colourable_of_prescribed_boundary_chord hc hk hface hG i j hadj h.1 h.2 hiP hjP hsmall)

end BoundaryInstance
end Thomassen
