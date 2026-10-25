/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexExceptionalGoodFourth

/-! Complete the good-fourth branch for all six prescribed vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The good-fourth branch no longer has an exceptional hypothesis: the
unique problematic interior witness is retained by the replacement prescription. -/
theorem colourable_of_six_vertex_path_short_second_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨_,u,hu,hub,hu2⟩ := I.remaining_good_fourth_counterexample_has_backward_exception hG p hp hface hroot
    (fun x hx => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx)
    r hr hn hP (by omega) horder hsecond hfourth hbad hsmall
  exact hbad (I.colourable_of_six_vertex_backward_exception_good_fourth hG p hp hface hroot r hr hn hP hrlen
    horder hsecond hfourth u hu hub hu2 hsmall)

/-- A remaining six-vertex counterexample must have short lists at both
the second and fourth backward positions. This includes the mixed exception. -/
theorem remaining_six_vertex_counterexample_has_short_second_and_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧ (I.lists (p.getVert (p.length-4))).card ≤ 2 := by
  have hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support := fun x hx =>
    (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx
  have hfirst : p.getVert 1 ∈ I.precolor.vertices := by
    rw [← horder 1 (by omega),hP]
    exact List.mem_toFinset.2 (r.getVert_mem_support 1)
  have hsecond := I.prescribed_second_boundary_list_le_two hG p hp hface hroot hExact r hr hn hP hfirst hbad hsmall
  refine ⟨hsecond,?_⟩
  by_contra h
  exact hbad (I.colourable_of_six_vertex_path_short_second_good_fourth hG p hp hface hroot r hr hn hP hrlen horder
    hsecond (by omega) hsmall)

end Thomassen.BoundaryInstance
