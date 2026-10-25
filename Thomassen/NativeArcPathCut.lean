/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleIntervals

/-! Native short-path separators from an actual closed walk. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

lemma walkCycleVertices_nat_le (p : G.Walk a a) {i : ℕ} (hi : i ≤ p.length) :
    walkCycleVertices p (i : ZMod p.length) = p.getVert i := by
  by_cases hlt : i < p.length
  · simp only [walkCycleVertices, ZMod.val_natCast_of_lt hlt]
  · have heq : i = p.length := by omega
    simp only [heq, ZMod.natCast_self, walkCycleVertices, ZMod.val_zero,
      Walk.getVert_zero, Walk.getVert_length]

/-- The closed indexed interval is exactly the support of the native suffix. -/
lemma walk_drop_support_cycleInterval (p : G.Walk a a) (n m : ℕ) (hlen : p.length = n + m) :
    cycleInterval (walkCycleVertices p) n m = {x | x ∈ (p.drop n).support} := by
  ext x
  constructor
  · rintro ⟨i, hi, hix⟩
    apply Walk.mem_support_iff_exists_getVert.2
    refine ⟨i, ?_, by rw [Walk.drop_length, hlen]; omega⟩
    rw [Walk.drop_getVert]
    rwa [walkCycleVertices_nat_le p (by omega : n + i ≤ p.length)] at hix
  · intro hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    have him : i ≤ m := by rw [Walk.drop_length, hlen] at hi; omega
    refine ⟨i, him, ?_⟩
    rw [walkCycleVertices_nat_le p (by omega : n + i ≤ p.length)]
    rwa [Walk.drop_getVert] at hix

variable [Fintype V]

/-- Cut a facial arc and its native closing path of one, two or three edges.
The separator is exactly the support of that path. Its vertices and the old
remaining boundary lie on one actual outer face of the exterior piece. -/
theorem native_short_arc_path_cut (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong M (walk_isCycleMap p hp) (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle M.facePerm outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace M outer x ∧ x ∉ p.support) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ (p.drop n).support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ p.support, x ∈ S) ∧
      (∀ x, OnOuterFace M outer x → x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ (p.drop n).support → OnOuterFace N o x) := by
  let : NeZero p.length := ⟨by omega⟩
  have hOld : ∀ x, OnOuterFace M outer x ↔ OnOuterFace M (walkArcRoot p hp) x := by
    intro x
    constructor
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hroot.symm.trans hd, hdx⟩
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hroot.trans hd, hdx⟩
  have hw : ∃ x, OnOuterFace M (walkArcRoot p hp) x ∧ x ∉ Set.range (walkCycleVertices p) := by
    obtain ⟨x, hx, hxout⟩ := houtside
    refine ⟨x, (hOld x).1 hx, ?_⟩
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using hxout
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSconn, hTconn,
    hSC, hkeep, hSface, hTface⟩ :=
    short_arc_path_separation M hg (walk_isCycleMap p hp) hn hm hm3 hlen hArc hconn hw
  refine ⟨S, T, hSsmall, hTsmall, hcover,
    hinter.trans (walk_drop_support_cycleInterval p n m hlen), hedges, hSconn, hTconn,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hSC x (by rwa [walkCycleVertices_range p hp])
  · intro x hx hxA
    exact hkeep x ((hOld x).1 hx) hxA
  · simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using hSface
  · obtain ⟨N, o, hface⟩ := hTface
    refine ⟨N, o, ?_⟩
    intro x hx
    apply hface x
    rcases hx with hx | hx
    · exact Or.inl ((hOld x.1).1 hx)
    · exact Or.inr (by rwa [walk_drop_support_cycleInterval p n m hlen])

end Thomassen
