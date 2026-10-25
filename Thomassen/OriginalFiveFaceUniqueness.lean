/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFacePreservation

/-! A three-edge interior path across a two-edge facial arc is unique. -/
-- Geometry adapted from Thomassen/InteriorThreePathUniqueness.lean to the original invariant.
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Closing two consecutive old face edges with an interior three-path
determines actual corners on the inner five-face. -/
theorem interior_three_path_facial_corners (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    I.embedding.facePerm (walkArcRoot p hp).symm =
      ⟨(a,y),hya.symm⟩ ∧
    I.embedding.facePerm ⟨(a,y),hya.symm⟩ = ⟨(y,x),hxy.symm⟩ := by
  have hf : ∀ j, OnOuterFace I.embedding I.outer (p.getVert j) := fun j =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support j)
  have hxa : x ≠ a := fun h => hx (by rw [h]; simpa only [Walk.getVert_zero] using hf 0)
  have hxb : x ≠ p.getVert 2 := fun h => hx (h ▸ hf 2)
  have hba : p.getVert 2 ≠ a := by
    intro h
    have he := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from by omega)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  let q : G.Walk (p.getVert 2) a := .cons hbx (.cons hxy (.cons hya .nil))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨hxb.symm,fun h => hy (h ▸ hf 2),hba⟩,⟨hxy.ne,hxa⟩,hya.ne⟩
  have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
    intro j hj hjl
    have hj' : j=1 ∨ j=2 := by change j < 3 at hjl; omega
    rcases hj' with rfl | rfl
    · exact hx
    · exact hy
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot 2 q hInner
  let c := spliceFacePath p 2 q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp 2 q hq (by omega) (by omega) hmeet
  have hcl : c.length=5 := by rw [spliceFacePath_length p 2 q (by omega)]; rfl
  let : NeZero c.length := ⟨by omega⟩
  have hc0 : walkCycleVertices c 0 = a := by
    simpa only [Nat.cast_zero,Walk.getVert_zero] using walkCycleVertices_nat_le c (i := 0) (by omega)
  have hc1 : walkCycleVertices c 1 = p.getVert 1 := by
    simpa only [Nat.cast_one] using spliceFacePath_cycleVertex_prefix p 2 q (by omega) (i := 1) (by omega)
  have hc3 : walkCycleVertices c (3 : ℕ) = x := by
    rw [walkCycleVertices_nat_le c (by omega)]
    change (spliceFacePath p 2 q).getVert 3 = x
    simp only [spliceFacePath,Walk.getVert_append,Walk.take_length,Nat.min_eq_left (by omega : 2 ≤ p.length),
      show ¬ (3 < 2) by omega,ite_false]
    rfl
  have hc4 : walkCycleVertices c (4 : ℕ) = y := by
    rw [walkCycleVertices_nat_le c (by omega)]
    change (spliceFacePath p 2 q).getVert 4 = y
    simp only [spliceFacePath,Walk.getVert_append,Walk.take_length,Nat.min_eq_left (by omega : 2 ≤ p.length),
      show ¬ (4 < 2) by omega,ite_false]
    rfl
  have hm : (0 : ZMod c.length)-1 = (4 : ℕ) := by rw [hcl]; decide
  have hm4 : (4 : ZMod c.length)-1 = (3 : ℕ) := by rw [hcl]; decide
  have hd1 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) 1) =
      ((walkArcRoot p hp).symm : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    have hp1 : walkCycleVertices p (0+1) = p.getVert 1 := by
      simpa only [zero_add,Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
    have hp0 : walkCycleVertices p 0 = a := by simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    exact Prod.ext (hc1.trans hp1.symm) (by change walkCycleVertices c (1-1) = walkCycleVertices p 0; rw [sub_self,hc0]; exact hp0.symm)
  have hd0 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) 0) =
      (⟨(a,y),hya.symm⟩ : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    exact Prod.ext hc0 (by change walkCycleVertices c (0-1) = y; rw [hm]; exact hc4)
  have hd4 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) (4 : ℕ)) =
      (⟨(y,x),hxy.symm⟩ : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    exact Prod.ext hc4 (by change walkCycleVertices c (4-1) = x; rw [hm4]; exact hc3)
  have hcroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot c hc) := by
    rw [spliceFacePath_root p hp 2 q hq (by omega) (by omega) hmeet]
    exact hroot
  have hout : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ c.support :=
    ⟨p.getVert 3,hf 3,spliceFacePath_misses_next_vertex p hp 2 q (by omega) hlen hmeet⟩
  have h1 := I.short_facial_arc_backward_face_preserved hG c hc (by omega) hcroot hout hbad hsmall 1
  have h0 := I.short_facial_arc_backward_face_preserved hG c hc (by omega) hcroot hout hbad hsmall 0
  rw [sub_self,hd1,hd0] at h1
  rw [hm,hd0,hd4] at h0
  exact ⟨h1,h0⟩

/-- The actual face permutation forces both interior vertices to agree.
No uniqueness assumption is imposed on the plane graph. -/
theorem interior_three_path_across_two_face_edges_unique (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y x' y' : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hx' : ¬ OnOuterFace I.embedding I.outer x') (hy' : ¬ OnOuterFace I.embedding I.outer y')
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbx' : G.Adj (p.getVert 2) x') (hxy' : G.Adj x' y') (hya' : G.Adj y' a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : x=x' ∧ y=y' := by
  obtain ⟨h1,h0⟩ := I.interior_three_path_facial_corners hG p hp hface hroot hlen x y hx hy hbx hxy hya hbad hsmall
  obtain ⟨h1',h0'⟩ := I.interior_three_path_facial_corners hG p hp hface hroot hlen x' y' hx' hy' hbx' hxy' hya' hbad hsmall
  have hyEq : y=y' := congrArg (fun d : G.Dart => d.snd) (h1.symm.trans h1')
  subst y'
  exact ⟨congrArg (fun d : G.Dart => d.snd) (h0.symm.trans h0'),rfl⟩

/-- The middle old face vertex on the two-edge arc has exactly its two
old cyclic neighbours. This removes all possible further attachments there. -/
theorem middle_vertex_of_interior_three_path_neighbours (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2 := by
  have hf : ∀ j, OnOuterFace I.embedding I.outer (p.getVert j) := fun j =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support j)
  have hxa : x ≠ a := fun h => hx (by rw [h]; simpa only [Walk.getVert_zero] using hf 0)
  have hxb : x ≠ p.getVert 2 := fun h => hx (h ▸ hf 2)
  have hba : p.getVert 2 ≠ a := by
    intro h
    have he := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from by omega)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  let q : G.Walk (p.getVert 2) a := .cons hbx (.cons hxy (.cons hya .nil))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨hxb.symm,fun h => hy (h ▸ hf 2),hba⟩,⟨hxy.ne,hxa⟩,hya.ne⟩
  have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
    intro j hj hjl
    have hj' : j=1 ∨ j=2 := by change j < 3 at hjl; omega
    rcases hj' with rfl | rfl
    · exact hx
    · exact hy
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot 2 q hInner
  let c := spliceFacePath p 2 q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp 2 q hq (by omega) (by omega) hmeet
  have hcl : c.length=5 := by rw [spliceFacePath_length p 2 q (by omega)]; rfl
  have hcch : c.IsChordless := by
    let : NeZero c.length := ⟨by omega⟩
    have hch := short_cycle_isChordless I.girth (walk_isCycleMap c hc) hc.three_le_length (by omega)
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro z w hz hw hzw
    apply (walkCycleVertices_edges c hc z w).1
    exact cyclicSubgraph_of_chordless hch (by rw [walkCycleVertices_range c hc]; exact hz)
      (by rw [walkCycleVertices_range c hc]; exact hw) hzw
  have hc0 : c.getVert 0 = a := Walk.getVert_zero c
  have hc1 : c.getVert 1 = p.getVert 1 := spliceFacePath_getVert_prefix p 2 q (by omega) (by omega)
  have hc2 : c.getVert 2 = p.getVert 2 := spliceFacePath_getVert_prefix p 2 q (by omega) (by omega)
  intro z hz
  have hzc := I.neighbours_on_short_closed_face_prefix hG p hp hface hroot 2 (by omega) hlen q hq
    (by change 0 < 3; omega) (by change 2+3 ≤ 6; omega) hInner hbad hsmall 1 (by omega) (by omega) z hz
  have hadj : G.Adj (c.getVert 1) z := by rwa [hc1]
  simpa only [hc0,hc2] using chordless_native_cycle_vertex_neighbours c hc hcch 1 (by omega) (by omega) hzc hadj

end Thomassen.OriginalBoundaryInstance
