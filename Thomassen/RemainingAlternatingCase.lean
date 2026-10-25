/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FiveFaceBoundaryAttachments

/-! Exact boundary-list normal form for the remaining four- and five-vertex cases. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- For a prescription on at most five vertices, every remaining oriented
counterexample has short second and fourth backward lists, together with its
unique interior three-path. No list-pattern or path-existence assumption is
supplied by the caller. -/
theorem remaining_short_prescription_counterexample_alternating (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    3 ≤ r.length ∧ r.length ≤ 4 ∧
      (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧
      (I.lists (p.getVert (p.length-4))).card ≤ 2 ∧
      ∃ x y, ¬ OnOuterFace I.embedding I.outer x ∧ ¬ OnOuterFace I.embedding I.outer y ∧
        G.Adj (p.getVert (p.length-1)) x ∧ G.Adj x y ∧ G.Adj y (p.getVert (p.length-3)) ∧
        (∀ x' y', ¬ OnOuterFace I.embedding I.outer x' → ¬ OnOuterFace I.embedding I.outer y' →
          G.Adj (p.getVert (p.length-1)) x' → G.Adj x' y' → G.Adj y' (p.getVert (p.length-3)) →
          x=x' ∧ y=y') ∧
        (∀ z, G.Adj (p.getVert (p.length-2)) z → z=p.getVert (p.length-3) ∨ z=p.getVert (p.length-1)) := by
  have hrlen : r.length ≤ 4 := by
    have h := hn5
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at h
    omega
  have hrthree : 3 ≤ r.length := by
    by_contra h
    apply hbad
    apply I.colourable_of_nontrivial_prescribed_path_at_most_three r hr hn hP hrpos ?_ hsmall
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support]
    omega
  have hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support := fun x hx =>
    (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx
  have hfirst : p.getVert 1 ∈ I.precolor.vertices := by
    rw [← horder 1 (by omega),hP]
    exact List.mem_toFinset.2 (r.getVert_mem_support 1)
  have hsecond := I.prescribed_second_boundary_list_le_two hG p hp hface hroot hExact r hr hn hP hfirst hbad hsmall
  have hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2 := by
    by_contra h
    exact hbad (I.colourable_of_short_path_short_second_good_fourth hG p hp hface hroot hExact
      r hr hn hP hrpos hn5 horder hsecond (by omega) hsmall)
  exact ⟨hrthree,hrlen,hsecond,hfourth,
    I.remaining_alternating_counterexample_has_unique_five_face hG p hp hface hroot r hr hn hP
      hrpos hn5 horder hfourth hbad hsmall⟩

end Thomassen.BoundaryInstance
