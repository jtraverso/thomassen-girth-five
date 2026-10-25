/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MirrorEmbedding

/-! Complete prescribed-edge reduction with the actual arbitrary original face. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Every instance with exactly a native edge prescribed is a complete main
induction case. Connectivity, a native facial cycle, placement of the edge and
its two possible orientations are all derived, not assumed. -/
theorem colourable_of_prescribed_edge (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG, _, _, b, p, hp, _, _, hverts, hface, hroot⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hplen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range (walkCycleVertices p) := by
    intro x hx
    rw [walkCycleVertices_range p hp]
    exact (hverts x).2 hx
  obtain ⟨i, e, he, horder⟩ := I.prescribed_path_follows_facial_cycle (walk_isCycleMap p hp) hplen hface hrange hG hbad hsmall r hr hPv
  have hstart : p.getVert i.val = a := by
    simpa only [Walk.getVert_zero, Nat.cast_zero, zero_mul, add_zero, walkCycleVertices] using (horder 0 (Nat.zero_le _)).symm
  subst a
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  have hi : i.val < p.length := ZMod.val_lt i
  rcases he with he | he
  · obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hpRoot i.val hi
    have hfirst : q.getVert 1 ∈ I.precolor.vertices := by
      have heq : q.getVert 1 = r.getVert 1 := by
        rw [hqo 1 (by omega), Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
        simpa only [Nat.cast_one, he, one_mul] using (horder 1 (by omega)).symm
      rw [heq]
      exact (hPv _).2 (r.getVert_mem_support 1)
    have hExactq : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ q.support :=
      fun x hx => (native_facial_cycle_support_iff I.embedding I.outer q hq hqf hqr x).2 hx
    exact hbad (I.colourable_of_prescribed_edge_native_face hG q hq hqf hqr hExactq r hr hn hP hrlen hfirst hsmall)
  · obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_mirrored_native_face_cycle_at I.embedding I.outer p hp hface hpRoot i.val hi
    have hfirst : q.getVert 1 ∈ I.mirror.precolor.vertices := by
      have heq : q.getVert 1 = r.getVert 1 := by
        rw [hqo 1 (by omega), ZMod.natCast_zmod_val, Nat.cast_one]
        simpa only [Nat.cast_one, he, one_mul, sub_eq_add_neg] using (horder 1 (by omega)).symm
      rw [heq]
      exact (hPv _).2 (r.getVert_mem_support 1)
    have hExactq : ∀ x, OnOuterFace I.mirror.embedding I.mirror.outer x → x ∈ q.support :=
      fun x hx => (native_facial_cycle_support_iff I.mirror.embedding I.mirror.outer q hq hqf hqr x).2 hx
    exact hbad (I.mirror.colourable_of_prescribed_edge_native_face hG q hq hqf hqr hExactq r hr hn hP hrlen hfirst hsmall)

end Thomassen.BoundaryInstance
