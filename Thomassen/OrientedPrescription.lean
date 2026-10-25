/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.TwoBoundaryComplement

/-! Native facial normalization in the direction of a prescribed path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A minimal counterexample admits an actual native facial cycle rooted at
the initial prescribed vertex and traversing the prescription forward, either
in its original embedding or in the proved mirror embedding. Every original
list and prescribed colour is retained. -/
theorem exists_oriented_native_face_for_prescribed_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧
      ((∃ q : G.Walk a a, ∃ hq : q.IsCycle,
        IsFacialCycleAlong I.embedding (walk_isCycleMap q hq) Set.univ ∧
        SameCycle I.embedding.facePerm I.outer (walkArcRoot q hq) ∧
        ∀ i ≤ r.length, r.getVert i = q.getVert i) ∨
      (∃ q : G.Walk a a, ∃ hq : q.IsCycle,
        IsFacialCycleAlong I.mirror.embedding (walk_isCycleMap q hq) Set.univ ∧
        SameCycle I.mirror.embedding.facePerm I.mirror.outer (walkArcRoot q hq) ∧
        ∀ i ≤ r.length, r.getVert i = q.getVert i)) := by
  obtain ⟨hG,_,_,b,p,hp,_,_,hverts,hface,hroot⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hplen := hp.three_le_length
  have hrbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range (walkCycleVertices p) := by
    intro x hx
    rw [walkCycleVertices_range p hp]
    exact (hverts x).2 hx
  obtain ⟨i,e,he,horder⟩ := I.prescribed_path_follows_facial_cycle (walk_isCycleMap p hp) hplen
    hface hrange hG hbad hsmall r hr hPv
  have hstart : p.getVert i.val = a := by
    simpa only [Walk.getVert_zero,Nat.cast_zero,zero_mul,add_zero,walkCycleVertices] using
      (horder 0 (Nat.zero_le _)).symm
  subst a
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  refine ⟨hG,?_⟩
  rcases he with he | he
  · obtain ⟨q,hq,_,hqo,hqf,hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hpRoot i.val (ZMod.val_lt i)
    left
    refine ⟨q,hq,hqf,hqr,?_⟩
    intro k hk
    rw [hqo k (by omega),Nat.cast_add,ZMod.natCast_zmod_val]
    simpa only [he,mul_one] using horder k hk
  · obtain ⟨q,hq,_,hqo,hqf,hqr⟩ := exists_mirrored_native_face_cycle_at I.embedding I.outer p hp hface hpRoot i.val (ZMod.val_lt i)
    right
    refine ⟨q,hq,hqf,hqr,?_⟩
    intro k hk
    rw [hqo k (by omega),ZMod.natCast_zmod_val]
    simpa only [he,mul_neg_one,← sub_eq_add_neg] using horder k hk

end Thomassen.BoundaryInstance
