/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFaceSaturation

/-! An empty side of a chordless cycle is an actual face of the original map. -/
-- Geometry adapted from Thomassen/ShortCycleFacePreservation.lean to the original invariant.
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} [Fintype V]

-- The two generic face-permutation theorems are reused from the existing module.
namespace OriginalBoundaryInstance
variable {C : Type v}

/-- In a smallest counterexample, the backward side of a short cycle
sharing an actual old facial edge is itself an actual face, whenever an old
face vertex lies outside the cycle. -/
theorem short_facial_arc_backward_face_preserved (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (i : ZMod p.length) :
    I.embedding.facePerm (toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) i)) =
      toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) (i-1)) := by
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let hc := walk_isCycleMap p hp
  have hch := short_cycle_isChordless I.girth hc hk hlen
  have hempty := I.short_facial_arc_backward_region_empty hG p hp hlen hroot houtside hbad hsmall
  have h := facePerm_preserved_of_chordless_empty_region I.embedding hc hch (cycleBackward hc 0)
    hempty (cycleBackward hc i) (cycle_backward_sameCycle (restrictMap I.embedding cyclicSubgraph_le) hc hk i)
  rw [cycle_face_backward] at h
  · exact h
  · exact hk

/-- All vertices on the inner face of a short closed old-face prefix are
exactly the vertices of that short native cycle. The original face root on
the first reversed edge is independent of the closing interior path. -/
theorem short_closed_face_prefix_inner_face_vertices (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (_hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) (z : V) :
    OnOuterFace I.embedding
      (walkArcRoot p hp).symm z ↔
      z ∈ (spliceFacePath p n q).support := by
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot n q hInner
  let c := spliceFacePath p n q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp n q hq hn (by omega) hmeet
  have hcl : c.length ≤ 6 := by rw [spliceFacePath_length p n q (by omega)]; exact hshort
  let : NeZero c.length := ⟨by have := hc.three_le_length; omega⟩
  have hcroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot c hc) := by
    rw [spliceFacePath_root p hp n q hq hn (by omega) hmeet]
    exact hroot
  have hout : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ c.support :=
    ⟨p.getVert (n+1),native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _
      (p.getVert_mem_support _),spliceFacePath_misses_next_vertex p hp n q hn hnp hmeet⟩
  have hpres := I.short_facial_arc_backward_face_preserved hG c hc hcl hcroot hout hbad hsmall
  have hd1 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) 1) =
      ((walkArcRoot p hp).symm : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    have hp1 : walkCycleVertices p (0+1) = p.getVert 1 := by
      simpa only [zero_add,Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
    have hp0 : walkCycleVertices p 0 = a := by simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    refine Prod.ext ?_ ?_
    · change walkCycleVertices c 1 = walkCycleVertices p (0+1)
      apply Eq.trans ?_ hp1.symm
      simpa only [Nat.cast_one] using spliceFacePath_cycleVertex_prefix p n q (by omega) (i := 1) (by omega)
    · change walkCycleVertices c (1-1) = walkCycleVertices p 0
      rw [sub_self,hp0]
      simpa only [Nat.cast_zero,Walk.getVert_zero] using walkCycleVertices_nat_le c (i := 0) (by have := hc.three_le_length; omega)
  have h := outerFace_vertices_of_backward_cycle_preserved I.embedding (walk_isCycleMap c hc) hpres z
  rw [hd1,walkCycleVertices_range c hc] at h
  exact h

/-- Two short interior paths closing the same old facial prefix determine
the same inner-face vertices and have the same length. In particular a
three-edge closing path rules out every four-edge closing path. -/
theorem short_closed_face_prefix_unique (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q q' : G.Walk (p.getVert n) a) (hq : q.IsPath) (hq' : q'.IsPath)
    (hql : 0 < q.length) (hql' : 0 < q'.length)
    (hshort : n+q.length ≤ 6) (hshort' : n+q'.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hInner' : ∀ j, 0 < j → j < q'.length → ¬ OnOuterFace I.embedding I.outer (q'.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    (∀ z, z ∈ (spliceFacePath p n q).support ↔ z ∈ (spliceFacePath p n q').support) ∧
      q.length=q'.length := by
  have hsupport : ∀ z, z ∈ (spliceFacePath p n q).support ↔ z ∈ (spliceFacePath p n q').support := by
    intro z
    exact (I.short_closed_face_prefix_inner_face_vertices hG p hp hface hroot n hn hnp q hq hql hshort
      hInner hbad hsmall z).symm.trans
      (I.short_closed_face_prefix_inner_face_vertices hG p hp hface hroot n hn hnp q' hq' hql' hshort'
        hInner' hbad hsmall z)
  have hc := spliceFacePath_isCycle p hp n q hq hn (by omega)
    (closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot n q hInner)
  have hc' := spliceFacePath_isCycle p hp n q' hq' hn (by omega)
    (closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot n q' hInner')
  have hsets : (spliceFacePath p n q).support.toFinset = (spliceFacePath p n q').support.toFinset := by
    ext z
    simpa only [List.mem_toFinset] using hsupport z
  have hcLen := congrArg Finset.card hsets
  rw [cycle_support_card_eq_length _ hc,cycle_support_card_eq_length _ hc',
    spliceFacePath_length p n q (by omega),spliceFacePath_length p n q' (by omega)] at hcLen
  exact ⟨hsupport,by omega⟩

end OriginalBoundaryInstance
end Thomassen
