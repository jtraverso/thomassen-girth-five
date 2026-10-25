/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ResidualShortLeaves

/-! The remaining alternating branch has one exact inner five-face. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- If an alternating deletion with at most five prescribed vertices still
fails, the interior three-path exists, is unique, and leaves exactly two
neighbours at the middle free face vertex. All conclusions are derived from
the strict induction hypothesis and the actual old facial cycle. -/
theorem remaining_alternating_counterexample_has_unique_five_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ x y, ¬ OnOuterFace I.embedding I.outer x ∧ ¬ OnOuterFace I.embedding I.outer y ∧
      G.Adj (p.getVert (p.length-1)) x ∧ G.Adj x y ∧ G.Adj y (p.getVert (p.length-3)) ∧
      (∀ x' y', ¬ OnOuterFace I.embedding I.outer x' → ¬ OnOuterFace I.embedding I.outer y' →
        G.Adj (p.getVert (p.length-1)) x' → G.Adj x' y' → G.Adj y' (p.getVert (p.length-3)) →
        x=x' ∧ y=y') ∧
      (∀ z, G.Adj (p.getVert (p.length-2)) z → z=p.getVert (p.length-3) ∨ z=p.getVert (p.length-1)) := by
  have hThree : ∃ x y, ¬ OnOuterFace I.embedding I.outer x ∧ ¬ OnOuterFace I.embedding I.outer y ∧
      G.Adj (p.getVert (p.length-1)) x ∧ G.Adj x y ∧ G.Adj y (p.getVert (p.length-3)) := by
    by_contra h
    apply hbad
    apply I.colourable_of_alternating_free_path_without_interior_three_path hG p hp hface hroot r hr hn hP
      hrpos hn5 horder hfourth ?_ hsmall
    intro x y hx hy hbx hxy hye
    exact h ⟨x,y,hx,hy,hbx,hxy,hye⟩
  obtain ⟨x,y,hx,hy,hbx,hxy,hye⟩ := hThree
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hlen : 5 ≤ p.length := by omega
  obtain ⟨q,hq,hql,hqo,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot
    (p.length-3) (by omega)
  have hq1 : q.getVert 1 = p.getVert (p.length-2) := by
    rw [hqo 1 (by omega),show p.length-3+1=p.length-2 by omega,walkCycleVertices_nat_le p (by omega)]
  have hq2 : q.getVert 2 = p.getVert (p.length-1) := by
    rw [hqo 2 (by omega),show p.length-3+2=p.length-1 by omega,walkCycleVertices_nat_le p (by omega)]
  have hbxq : G.Adj (q.getVert 2) x := by rwa [hq2]
  refine ⟨x,y,hx,hy,hbx,hxy,hye,?_,?_⟩
  · intro x' y' hx' hy' hbx' hxy' hye'
    exact I.interior_three_path_across_two_face_edges_unique hG q hq hqface hqroot (by omega)
      x y x' y' hx hy hx' hy' hbxq hxy hye (by rwa [hq2]) hxy' hye' hbad hsmall
  · intro z hz
    have h := I.middle_vertex_of_interior_three_path_neighbours hG q hq hqface hqroot (by omega)
      x y hx hy hbxq hxy hye hbad hsmall z (by rwa [hq1])
    simpa only [hq2] using h

end Thomassen.BoundaryInstance
