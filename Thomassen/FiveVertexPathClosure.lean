/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FreeFiveFaceColouring

/-! Complete strict induction for nontrivial prescriptions on at most five vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Every remaining alternating case on four or five prescribed vertices
has its unique inner five-face. Rebase at its third free vertex and delete that
face with the explicit compatible colours, keeping the entire old prescription. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_five_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hr3,_,_,hfourth,x,y,hx,hy,hbx,hxy,hye,_,_⟩ :=
    I.remaining_short_prescription_counterexample_alternating hG p hp hface hroot r hr hn hP hrpos hn5 horder hbad hsmall
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hlen : 7 ≤ p.length := by omega
  have hnotP : ∀ i, r.length < i → i < p.length → p.getVert i ∉ I.precolor.vertices := by
    intro i hri hip hz
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv _).1 hz)
    have he := hp.getVert_injOn' (show j ≤ p.length-1 from by omega) (show i ≤ p.length-1 from by omega)
      ((horder j hjl).symm.trans hj)
    omega
  obtain ⟨q,hq,hql,hqo,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot
    (p.length-3) (by omega)
  have hq1 : q.getVert 1 = p.getVert (p.length-2) := by
    rw [hqo 1 (by omega),show p.length-3+1=p.length-2 by omega,walkCycleVertices_nat_le p (by omega)]
  have hq2 : q.getVert 2 = p.getVert (p.length-1) := by
    rw [hqo 2 (by omega),show p.length-3+2=p.length-1 by omega,walkCycleVertices_nat_le p (by omega)]
  have hq3 : q.getVert 3 = a := by
    rw [hqo 3 (by omega),Nat.sub_add_cancel (by omega : 3 ≤ p.length),ZMod.natCast_self]
    simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
  have hqprev : q.getVert (q.length-1) = p.getVert (p.length-4) := by
    rw [hql,hqo (p.length-1) (by omega),show p.length-3+(p.length-1)=p.length+(p.length-4) by omega,
      Nat.cast_add,ZMod.natCast_self,zero_add,walkCycleVertices_nat_le p (by omega)]
  have haP : a ∈ I.precolor.vertices := (hPv a).2 r.start_mem_support
  apply hbad
  apply I.colourable_of_free_inner_five_face_short_neighbours hG r hr hn hP hrpos hn5 q hq hqface hqroot
    (by omega) (hnotP _ (by omega) (by omega))
    (by rw [hq1]; exact hnotP _ (by omega) (by omega))
    (by rw [hq2]; exact hnotP _ (by omega) (by omega))
    (by rwa [hqprev]) (by rw [hq3,I.singleton a haP,Finset.card_singleton])
    x y hx hy (by rwa [hq2]) hxy hye hsmall

/-- All nontrivial prescriptions on at most five vertices, for the original
arbitrary face and either orientation, are complete strict induction cases. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_five (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn5 : r.support.toFinset.card ≤ 5)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.colourable_of_nontrivial_prescribed_path_at_most_five_native_face hG p hp hface hroot
      r hr hn hP hrpos hn5 horder hsmall
  · exact I.mirror.colourable_of_nontrivial_prescribed_path_at_most_five_native_face hG p hp hface hroot
      r hr hn hP hrpos hn5 horder hsmall

/-- All other prescription states are closed: every remaining minimal
counterexample must prescribe exactly six vertices, as a native five-edge path. -/
theorem remaining_counterexample_has_six_prescribed_vertices (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ a t : V, ∃ (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6),
      I.precolor = .path r hr hn ∧ r.length=5 := by
  obtain ⟨a,t,r,hr,hn,hP,hr3,hr5⟩ := I.remaining_counterexample_has_four_to_six_prescribed_vertices hbad hsmall
  have heq : r.length=5 := by
    by_contra h
    apply hbad
    apply I.colourable_of_nontrivial_prescribed_path_at_most_five r hr hn hP (by omega) ?_ hsmall
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support]
    omega
  exact ⟨a,t,r,hr,hn,hP,heq⟩

end Thomassen.BoundaryInstance
