/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AlternatingFreePathDeletion

/-! An empty side of a chordless cycle is an actual face of the original map. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} [Fintype V]

/-- A chordless cycle with no vertices in one open region has no gaps in
that region. Its face permutation is therefore preserved in the original map. -/
theorem facePerm_preserved_of_chordless_empty_region (M : PlaneMap G)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c)
    (hch : IsChordless G c) (o : (cyclicSubgraph G c).Dart)
    (hempty : ∀ w, ¬ inSubface M cyclicSubgraph_le o w)
    (e : (cyclicSubgraph G c).Dart)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm o e) :
    M.facePerm (toDart cyclicSubgraph_le e) =
      toDart cyclicSubgraph_le ((restrictMap M cyclicSubgraph_le).facePerm e) := by
  let d := M.facePerm (toDart cyclicSubgraph_le e)
  have hn : IsNextH M cyclicSubgraph_le d ((restrictMap M cyclicSubgraph_le).facePerm e) :=
    isNextH_rot_subRot M cyclicSubgraph_le e.symm
  have he' : SameCycle (restrictMap M cyclicSubgraph_le).facePerm o
      ((restrictMap M cyclicSubgraph_le).facePerm e) := he.trans ⟨1,by simp⟩
  have hx : d.fst ∈ subVerts (cyclicSubgraph G c) :=
    (isNextH_fst M cyclicSubgraph_le hn) ▸ ⟨_,((restrictMap M cyclicSubgraph_le).facePerm e).adj⟩
  have hd : InH (cyclicSubgraph G c) d := by
    by_cases hy : d.snd ∈ subVerts (cyclicSubgraph G c)
    · exact cyclicSubgraph_of_chordless hch (by rwa [← cyclicSubgraph_subVerts hc])
        (by rwa [← cyclicSubgraph_subVerts hc]) d.adj
    · exact (hempty d.snd ⟨hy,d,_,hx,hy,hn,he',.refl _⟩).elim
  exact eq_of_isNextH_of_inH M cyclicSubgraph_le hd hn

/-- A fully preserved backward cycle is precisely the vertex set of its
actual original face orbit, including at a fixed first backward edge. -/
theorem outerFace_vertices_of_backward_cycle_preserved (M : PlaneMap G)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : ∀ i, M.facePerm (toDart cyclicSubgraph_le (cycleBackward hc i)) =
      toDart cyclicSubgraph_le (cycleBackward hc (i-1))) (z : V) :
    OnOuterFace M (toDart cyclicSubgraph_le (cycleBackward hc 1)) z ↔ z ∈ Set.range c := by
  let d : ZMod k → G.Dart := fun i => toDart cyclicSubgraph_le (cycleBackward hc i)
  have hpow : ∀ n : ℕ, (M.facePerm ^ n) (d 0) = d (-(n : ZMod k)) := by
    intro n
    induction n with
    | zero => simp only [pow_zero,Perm.one_apply,Nat.cast_zero,neg_zero]
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,ih]
      change M.facePerm (toDart cyclicSubgraph_le (cycleBackward hc _)) = _
      rw [hface]
      congr 2
      push_cast
      ring
  have hs : ∀ i, SameCycle M.facePerm (d 0) (d i) := by
    intro i
    refine ⟨((-i).val : ℤ),?_⟩
    rw [zpow_natCast,hpow,ZMod.natCast_zmod_val,neg_neg]
  have hstep : ∀ i : ZMod k, M.facePerm (d (-i)) = d (-(i+1)) := by
    intro i
    change M.facePerm (toDart cyclicSubgraph_le (cycleBackward hc _)) = _
    rw [hface]
    congr 2
    ring
  constructor
  · rintro ⟨e,he,hez⟩
    have he0 : SameCycle M.facePerm (d (-0)) e := by simpa only [neg_zero] using (hs 1).trans he
    obtain ⟨i,hi⟩ := eq_of_sameCycle_cyc hstep he0
    exact ⟨-i,(congrArg (fun e : G.Dart => e.fst) hi).symm.trans hez⟩
  · rintro ⟨i,rfl⟩
    exact ⟨d i,(hs 1).symm.trans (hs i),rfl⟩

namespace BoundaryInstance
variable {C : Type v}

/-- In a smallest counterexample, the backward side of a short cycle
sharing an actual old facial edge is itself an actual face, whenever an old
face vertex lies outside the cycle. -/
theorem short_facial_arc_backward_face_preserved (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
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
theorem short_closed_face_prefix_inner_face_vertices (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (_hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) (z : V) :
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
theorem short_closed_face_prefix_unique (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q q' : G.Walk (p.getVert n) a) (hq : q.IsPath) (hq' : q'.IsPath)
    (hql : 0 < q.length) (hql' : 0 < q'.length)
    (hshort : n+q.length ≤ 6) (hshort' : n+q'.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hInner' : ∀ j, 0 < j → j < q'.length → ¬ OnOuterFace I.embedding I.outer (q'.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
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

end BoundaryInstance
end Thomassen
