/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortArcSaturation

/-! Exact neighbourhoods at the prescribed end of the exceptional five-cycle. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The backward mixed exception determines a short five-cycle through the
first three prescribed vertices. Its two internal old facial vertices have
exactly their two cycle neighbours. Extra neighbours would create a nonempty
inner region, already excluded by strict short-cycle induction. -/
theorem backward_exception_prescribed_end_neighbours (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hub : G.Adj u (p.getVert (p.length-1))) (hu2 : G.Adj u (r.getVert 2))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (∀ y, G.Adj a y → y=r.getVert 1 ∨ y=p.getVert (p.length-1)) ∧
    (∀ y, G.Adj (r.getVert 1) y → y=a ∨ y=r.getVert 2) := by
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hplen : 9 ≤ p.length := by omega
  let b := p.getVert (p.length-1)
  obtain ⟨w,hw,hwl,hwo,hwface,hwroot⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot (p.length-1) (by omega)
  have hwo' : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → w.getVert k = r.getVert (k-1) := by
    intro k hk hkl
    rw [hwo k (by omega),show p.length-1+k=p.length+(k-1) by omega,
      Nat.cast_add,ZMod.natCast_self,zero_add,walkCycleVertices_nat_le p (by omega),← horder (k-1) (by omega)]
  have hw1 : w.getVert 1 = a := by simpa only [Nat.sub_self,Walk.getVert_zero] using hwo' 1 (by omega) (by omega)
  have hw2 : w.getVert 2 = r.getVert 1 := hwo' 2 (by omega) (by omega)
  have hw3 : w.getVert 3 = r.getVert 2 := hwo' 3 (by omega) (by omega)
  have h2b : r.getVert 2 ≠ b := by
    intro he
    have hidx := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega)
      (show p.length-1 ≤ p.length-1 from le_rfl) ((horder 2 (by omega)).symm.trans he)
    omega
  let q : G.Walk (w.getVert 3) b := .cons
    (show G.Adj (w.getVert 3) u from by rw [hw3]; exact hu2.symm) (.cons hub .nil)
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true,hw3]
    exact ⟨⟨hu2.ne.symm,h2b⟩,hub.ne⟩
  have hInner : ∀ k, 0 < k → k < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert k) := by
    intro k hk hkl
    have hk1 : k=1 := by change k < 2 at hkl; omega
    subst k; exact hu
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer w hw hwface hwroot 3 q hInner
  let c := spliceFacePath w 3 q
  have hc : c.IsCycle := spliceFacePath_isCycle w hw 3 q hq (by omega) (by omega) hmeet
  have hcl : c.length=5 := by rw [spliceFacePath_length w 3 q (by omega)]; rfl
  have hc0 : c.getVert 0 = b := Walk.getVert_zero c
  have hc1 : c.getVert 1 = a := (spliceFacePath_getVert_prefix w 3 q (by omega) (by omega)).trans hw1
  have hc2 : c.getVert 2 = r.getVert 1 := (spliceFacePath_getVert_prefix w 3 q (by omega) (by omega)).trans hw2
  have hc3 : c.getVert 3 = r.getVert 2 := (spliceFacePath_getVert_prefix w 3 q (by omega) (by omega)).trans hw3
  have hcycleChordless : c.IsChordless := by
    let : NeZero c.length := ⟨by omega⟩
    have hch := short_cycle_isChordless I.girth (walk_isCycleMap c hc) hc.three_le_length (by omega)
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    apply (walkCycleVertices_edges c hc x y).1
    apply cyclicSubgraph_of_chordless hch
    · rw [walkCycleVertices_range c hc]; exact hx
    · rw [walkCycleVertices_range c hc]; exact hy
    · exact hxy
  constructor
  · intro y hay
    have hyc : y ∈ c.support := I.neighbours_on_short_closed_face_prefix hG w hw hwface hwroot
      3 (by omega) (by omega) q hq (by change 0 < 2; omega) (by change 3+2 ≤ 6; omega) hInner
      hbad hsmall 1 (by omega) (by omega) y (by rwa [hw1])
    have haC : G.Adj (c.getVert 1) y := by rwa [hc1]
    have hy := chordless_native_cycle_vertex_neighbours c hc hcycleChordless 1 (by omega) (by omega) hyc haC
    simpa only [hc0,hc2] using hy.symm
  · intro y hty
    have hyc : y ∈ c.support := I.neighbours_on_short_closed_face_prefix hG w hw hwface hwroot
      3 (by omega) (by omega) q hq (by change 0 < 2; omega) (by change 3+2 ≤ 6; omega) hInner
      hbad hsmall 2 (by omega) (by omega) y (by rwa [hw2])
    have htC : G.Adj (c.getVert 2) y := by rwa [hc2]
    have hy := chordless_native_cycle_vertex_neighbours c hc hcycleChordless 2 (by omega) (by omega) hyc htC
    simpa only [hc1,hc3] using hy

end Thomassen.BoundaryInstance
