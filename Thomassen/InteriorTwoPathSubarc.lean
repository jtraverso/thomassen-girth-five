/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FacialCycleRebase

/-! Prescription-free two-path cuts on arbitrary old facial subarcs. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Rebased native face intervals are exactly the corresponding old shifted
intervals, with all index and length casts accounted for. -/
lemma rebased_native_cycleInterval {a b : V} (p : G.Walk a a) (q : G.Walk b b)
    (s l : ℕ) (hlen : q.length = p.length)
    (horder : ∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s + i : ℕ) : ZMod p.length))
    (hl : 1 + l ≤ p.length) :
    cycleInterval (walkCycleVertices q) 1 l = cycleInterval (walkCycleVertices p) (s + 1) l := by
  ext x
  constructor <;> rintro ⟨i, hi, hix⟩ <;> refine ⟨i, hi, ?_⟩
  · rw [walkCycleVertices_nat_le q (by omega : 1 + i ≤ q.length), horder (1 + i) (by omega)] at hix
    simpa only [Nat.add_assoc] using hix
  · rw [walkCycleVertices_nat_le q (by omega : 1 + i ≤ q.length), horder (1 + i) (by omega)]
    simpa only [Nat.add_assoc] using hix

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The prescription-free two-edge reduction applies to any specified old
facial subarc. Rebasing, exact arc transport and chordlessness of the new native
representative are proved internally under the strict main induction. -/
theorem colourable_of_interior_two_path_free_subarc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hzs : G.Adj z (p.getVert s)) (hzn : G.Adj z (p.getVert n))
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨q, hq, hqlen, horder, hqface, hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot s (by omega)
  have hqch := I.native_face_cycle_chordless_of_minimal_counterexample hG q hq hqface hqroot hbad hsmall
  have hqn : q.getVert (n - s) = p.getVert n := by
    rw [horder (n - s) (by omega), Nat.add_sub_of_le (by omega : s ≤ n)]
    exact walkCycleVertices_nat_le p (by omega)
  have hPq : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices q) 1 (n - s - 2) := by
    intro x hx
    rw [rebased_native_cycleInterval p q s (n - s - 2) hqlen horder (by omega)]
    exact hPoutside x hx
  exact hbad (I.colourable_of_interior_two_path_free_arc hG q hq hqch hqface hqroot (n - s) (by omega) (by omega)
    z hz hzs (by rwa [hqn]) hPq hsmall)

/-- In a smallest counterexample, an interior vertex has at most one
neighbour on a specified closed facial arc whose open part avoids the original
prescription. Adjacent incidences violate girth; separated incidences give the
completed two-path subarc reduction. -/
lemma interior_neighbours_unique_on_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (n : ℕ) (hnp : n + 2 ≤ p.length)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (z : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n)
    (hzi : G.Adj z (p.getVert i)) (hzj : G.Adj z (p.getVert j)) : i = j := by
  have hdo : ∀ s t, s < t → t ≤ n → G.Adj z (p.getVert s) → G.Adj z (p.getVert t) → False := by
    intro s t hst htn hzs hzt
    by_cases hnear : t = s + 1
    · exact neighbors_nonadjacent I.girth hzs hzt (by rw [hnear]; exact p.adj_getVert_succ (by omega))
    · apply hbad (I.colourable_of_interior_two_path_free_subarc hG p hp hface hroot s t (by omega) (by omega) z hz hzs hzt ?_ hsmall)
      intro x hxP hxArc
      obtain ⟨r, hr, hrx⟩ := hxArc
      apply hPoutside x hxP
      refine ⟨s + r, by omega, ?_⟩
      have heq : 1 + (s + r) = (s + 1) + r := by omega
      simpa only [heq] using hrx
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hdo i j hij hj hzi hzj).elim
  · exact hij
  · exact (hdo j i hji hi hzj hzi).elim

end BoundaryInstance
end Thomassen
