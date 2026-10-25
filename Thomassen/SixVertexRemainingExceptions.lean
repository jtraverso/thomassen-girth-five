/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexUniqueBoundaryClosure

/-! All remaining six-vertex cases have a short fourth list and a mixed exception. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Without assuming any incidence exclusion, a remaining six-vertex
counterexample contains one of the two permitted mixed two-path
configurations, at the initial or terminal free boundary neighbour. -/
theorem remaining_six_vertex_counterexample_has_mixed_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-2))).card ≤ 2 ∧ (I.lists (p.getVert (p.length-4))).card ≤ 2 ∧
      ∃ u, ¬ OnOuterFace I.embedding I.outer u ∧
        ((G.Adj u (r.getVert 2) ∧ G.Adj u (p.getVert (p.length-1))) ∨
         (G.Adj u (r.getVert 3) ∧ G.Adj u (p.getVert 6))) := by
  obtain ⟨hsecond,hfourth⟩ := I.remaining_six_vertex_counterexample_has_short_second_and_fourth
    hG p hp hface hroot r hr hn hP hrlen horder hbad hsmall
  refine ⟨hsecond,hfourth,?_⟩
  by_contra hNoException
  apply hbad
  apply I.colourable_of_six_vertex_path_with_unique_boundary_neighbours hG p hp hface hroot r hr hn hP hrlen ?_ horder hsmall
  intro u x y hu hx hy hux huy
  by_contra hxy
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hmemP : ∀ i, i ≤ r.length → p.getVert i ∈ I.precolor.vertices := by
    intro i hi
    rw [← horder i hi,hP]
    exact List.mem_toFinset.2 (r.getVert_mem_support i)
  have hAtInitial : ∀ z, OnOuterFace I.embedding I.outer z → z ∉ I.precolor.vertices → G.Adj a z →
      z=p.getVert (p.length-1) := by
    intro z hz hzP haz
    rcases chordless_native_cycle_root_neighbours p hp hch ((hverts z).2 hz) haz with h | h
    · exact (hzP (h ▸ hmemP 1 (by omega))).elim
    · exact h
  have hAtTerminal : ∀ z, OnOuterFace I.embedding I.outer z → z ∉ I.precolor.vertices → G.Adj t z → z=p.getVert 6 := by
    intro z hz hzP htz
    have ht : t=p.getVert 5 := (Walk.getVert_length r).symm.trans (by simpa only [hrlen] using horder 5 (by omega))
    have hadj : G.Adj (p.getVert 5) z := by rwa [← ht]
    rcases chordless_native_cycle_vertex_neighbours p hp hch 5 (by omega) (by omega) ((hverts z).2 hz) hadj with h | h
    · exact (hzP (h ▸ hmemP 4 (by omega))).elim
    · exact h
  obtain ⟨_,hcase⟩ := I.interior_boundary_pair_exceptional r hr hn hP (by omega) hbad hsmall u x y hu hx hy hxy hux huy
  apply hNoException
  refine ⟨u,hu,?_⟩
  rcases hcase with ⟨hx2,hyP,hay⟩ | ⟨hx3,hyP,hty⟩ | ⟨hy2,hxP,hax⟩ | ⟨hy3,hxP,htx⟩
  · exact Or.inl ⟨by rwa [← hx2],by rwa [← hAtInitial y hy hyP hay]⟩
  · exact Or.inr ⟨by rwa [← hx3],by rwa [← hAtTerminal y hy hyP hty]⟩
  · exact Or.inl ⟨by rwa [← hy2],by rwa [← hAtInitial x hx hxP hax]⟩
  · exact Or.inr ⟨by rwa [← hy3],by rwa [← hAtTerminal x hx hxP htx]⟩

end Thomassen.BoundaryInstance
