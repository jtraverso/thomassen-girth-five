/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AugmentedPathColouring

/-! Actual facial cuts with additional prescribed short-list neighbours. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Strict induction at an actual facial cut, including one additional
short-list boundary neighbours. The capture condition remains explicit. -/
theorem colourable_of_native_short_path_with_one_short_end (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) {x : V} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxArc : x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxa : G.Adj x (p.getVert n)) (hxq : x ∉ (p.drop n).support)
    (hxshort : (I.lists x).card ≤ 2)
    (hashort : (I.lists a).card ≤ 2)
    (hCaptureArc : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2),
      z ≠ x → (I.lists z).card ≤ 2 →
      ∀ w ∈ (p.drop n).support, ¬ G.Adj z w)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, _, hTconn,
    hSC, hkeep, ⟨oS, hSface⟩, _⟩ :=
    native_short_arc_path_cut I.embedding I.outer I.girth hconn p hp n m hn hm hm3 hlen hArc hroot houtside
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ T :=
    fun x hx => hkeep x (I.on_outer x hx) (hPoutside x hx)
  have hOldCycle : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → x.1 ∈ p.support := by
    intro x hxFace
    by_cases hxA : x.1 ∈ cycleInterval (walkCycleVertices p) 1 (n - 2)
    · have hxC := cycleInterval_subset 1 (n - 2) hxA
      rwa [walkCycleVertices_range p hp] at hxC
    · have hxT := hkeep x.1 hxFace hxA
      have h : x.1 ∈ S ∩ T := ⟨x.2, hxT⟩
      rw [hinter] at h
      exact (Walk.isSubwalk_drop p n).support_subset h
  have hArcCycle : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), z ∈ p.support := by
    intro z hz
    have h := cycleInterval_subset 1 (n - 2) hz
    rwa [walkCycleVertices_range p hp] at h
  apply I.colourable_of_short_path_with_one_short_end S T (p.drop n) (hp.isPath_drop (by omega))
    (by rw [Walk.drop_length, hlen]; omega) (by rw [Walk.drop_length, hlen]; omega)
    hxa hxq (hSC x (hArcCycle x hxArc)) 
    hxshort hashort
    hcover hinter hedges hTconn hP oS ?_ ?_ ?_ hSsmall hTsmall hsmall
  · intro z hz
    apply (hSface z).2
    rcases hz with hz | hz
    · exact (Walk.isSubwalk_drop p n).support_subset hz
    · rw [hz]
      exact hArcCycle x hxArc
  · intro z hz
    apply I.interior_lists
    intro hzOld
    exact hz ((hSface z).2 (hOldCycle z hzOld))
  · intro z hzS hzq hzx hzShort w hw
    have hzArc : z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
      by_cases hzFace : OnOuterFace I.embedding I.outer z
      · by_contra hzArc
        have hzT := hkeep z hzFace hzArc
        have h : z ∈ S ∩ T := ⟨hzS, hzT⟩
        rw [hinter] at h
        exact hzq h
      · have h := I.interior_lists z hzFace
        omega
    exact hCaptureArc z hzArc hzx hzShort w hw

/-- Strict induction at an actual facial cut, including two additional
short-list boundary neighbours. The capture condition remains explicit. -/
theorem colourable_of_native_short_path_with_two_short_ends (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) {x y : V} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm2 : m ≤ 2) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxArc : x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxa : G.Adj x (p.getVert n)) (hxq : x ∉ (p.drop n).support)
    (hxshort : (I.lists x).card ≤ 2)
    (hyArc : y ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hby : G.Adj a y) (hyq : y ∉ (p.drop n).support) (hyshort : (I.lists y).card ≤ 2)
    (hCaptureArc : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2),
      z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ (p.drop n).support, ¬ G.Adj z w)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, _, hTconn,
    hSC, hkeep, ⟨oS, hSface⟩, _⟩ :=
    native_short_arc_path_cut I.embedding I.outer I.girth hconn p hp n m hn hm (by omega) hlen hArc hroot houtside
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ T :=
    fun x hx => hkeep x (I.on_outer x hx) (hPoutside x hx)
  have hOldCycle : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → x.1 ∈ p.support := by
    intro x hxFace
    by_cases hxA : x.1 ∈ cycleInterval (walkCycleVertices p) 1 (n - 2)
    · have hxC := cycleInterval_subset 1 (n - 2) hxA
      rwa [walkCycleVertices_range p hp] at hxC
    · have hxT := hkeep x.1 hxFace hxA
      have h : x.1 ∈ S ∩ T := ⟨x.2, hxT⟩
      rw [hinter] at h
      exact (Walk.isSubwalk_drop p n).support_subset h
  have hArcCycle : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), z ∈ p.support := by
    intro z hz
    have h := cycleInterval_subset 1 (n - 2) hz
    rwa [walkCycleVertices_range p hp] at h
  apply I.colourable_of_short_path_with_two_short_ends S T (p.drop n) (hp.isPath_drop (by omega))
    (by rw [Walk.drop_length, hlen]; omega) (by rw [Walk.drop_length, hlen]; omega)
    hxa hby hxq hyq (hSC x (hArcCycle x hxArc)) (hSC y (hArcCycle y hyArc)) 
    hxshort hyshort
    hcover hinter hedges hTconn hP oS ?_ ?_ ?_ hSsmall hTsmall hsmall
  · intro z hz
    apply (hSface z).2
    rcases hz with hz | hz | hz
    · exact (Walk.isSubwalk_drop p n).support_subset hz
    · rw [hz]
      exact hArcCycle x hxArc
    · rw [hz]
      exact hArcCycle y hyArc
  · intro z hz
    apply I.interior_lists
    intro hzOld
    exact hz ((hSface z).2 (hOldCycle z hzOld))
  · intro z hzS hzq hzx hzy hzShort w hw
    have hzArc : z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
      by_cases hzFace : OnOuterFace I.embedding I.outer z
      · by_contra hzArc
        have hzT := hkeep z hzFace hzArc
        have h : z ∈ S ∩ T := ⟨hzS, hzT⟩
        rw [hinter] at h
        exact hzq h
      · have h := I.interior_lists z hzFace
        omega
    exact hCaptureArc z hzArc hzx hzy hzShort w hw

end BoundaryInstance
end Thomassen
