/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalTripleDeletion

/-! The second five-face in original step (10), independent of the chosen outer face. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The saturation argument needs only nonseparation of the short cycle.
Consequently it applies to a different actual face from the original exterior,
as required by the second five-face in Thomassen's residual obstruction. -/
theorem neighbours_on_facial_arc_of_not_separating (M : PlaneMap G) (outer : G.Dart)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (A : Set V) (hAC : A ⊆ {x | x ∈ p.support})
    (hArc : IsFacialCycleAlong M (walk_isCycleMap p hp) A)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace M outer z ∧ z ∉ p.support)
    (hNoSep : ¬ NativeCycleSeparates M p hp)
    (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ p.support := by
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let hc := walk_isCycleMap p hp
  let left := cycleForward hc 0
  let right := cycleBackward hc 0
  let root := toDart (show cyclicSubgraph G (walkCycleVertices p) ≤ G from cyclicSubgraph_le) left
  have hnext : IsNextH M cyclicSubgraph_le root left :=
    ⟨0,rfl,fun n hn => (Nat.not_lt_zero n hn).elim⟩
  obtain ⟨z,hz,hzout⟩ := houtside
  have hzroot : OnOuterFace M root z := by
    obtain ⟨d,hd,hdz⟩ := hz
    exact ⟨d,hroot.symm.trans hd,hdz⟩
  have hzleft : z ∈ subfaceSide M cyclicSubgraph_le left :=
    cycle_original_face_subset_side M hc hk root (SameCycle.refl _ _) hnext z hzroot
  have hzC : z ∉ Set.range (walkCycleVertices p) := by
    simpa only [walkCycleVertices_range p hp,Set.mem_ofPred_eq] using hzout
  have hzIn : inSubface M cyclicSubgraph_le left z := by
    rcases hzleft with hzleft | hzleft
    · exact (hzC (by simpa only [cycle_subface_vertices M hc hk left] using hzleft)).elim
    · exact hzleft
  have hrightEmpty : ∀ w, ¬ inSubface M cyclicSubgraph_le right w := by
    intro w hw
    exact hNoSep ⟨⟨z,hzIn⟩,⟨w,hw⟩⟩
  by_contra hy
  have hyC : y ∉ Set.range (walkCycleVertices p) := by
    simpa only [walkCycleVertices_range p hp,Set.mem_ofPred_eq] using hy
  have hyCover : y ∈ subfaceSide M cyclicSubgraph_le left ∪
      subfaceSide M cyclicSubgraph_le right := by
    rw [cycle_sides_cover M hc hk hG]
    trivial
  rcases hyCover with hyLeft | hyRight
  · exact cycle_no_exterior_neighbour_along M hc hk A
      (by intro w hw; rw [walkCycleVertices_range p hp]; exact hAC hw) hArc hx ⟨hyLeft,hyC⟩ hxy
  · rcases hyRight with hyRight | hyRight
    · exact hyC (by simpa only [cycle_subface_vertices M hc hk right] using hyRight)
    · exact hrightEmpty y hyRight

namespace OriginalBoundaryInstance

/-- The two actual inner-face corners at the final attachment persist when
the first closing vertex is itself the next old-boundary vertex. -/
theorem three_path_inner_face_corners_allow_boundary (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y : V) (hx1 : x ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y)
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    I.embedding.facePerm (walkArcRoot p hp).symm = ⟨(a,y),hya.symm⟩ ∧
      I.embedding.facePerm ⟨(a,y),hya.symm⟩ = ⟨(y,x),hxy.symm⟩ := by
  by_cases hxf : OnOuterFace I.embedding I.outer x
  · have hx3 := (I.boundary_three_path_first_vertex hG p hp hch hface hroot hlen x y hxf hx1
        hy h2x hxy hya hbad hsmall).1
    have h3a : p.getVert 3 ≠ a := by
      intro he
      have hidx := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega)
        (show 0 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using he)
      omega
    have h3y : p.getVert 3 ≠ y := by simpa only [← hx3] using hxy.ne
    let q : G.Walk (p.getVert 3) a := .cons (show G.Adj (p.getVert 3) y from hx3 ▸ hxy) (.cons hya .nil)
    have hq : q.IsPath := by simp [q,Walk.isPath_def,h3a,h3y,hya.ne]
    have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
      intro j hj hjl
      have hj1 : j=1 := by change j < 2 at hjl; omega
      subst j
      exact hy
    have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot 3 q hInner
    let c := spliceFacePath p 3 q
    have hc : c.IsCycle := spliceFacePath_isCycle p hp 3 q hq (by omega) (by omega) hmeet
    have hcl : c.length=5 := by rw [spliceFacePath_length p 3 q (by omega)]; rfl
    let : NeZero c.length := ⟨by omega⟩
    have hc0 : walkCycleVertices c 0 = a := by simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    have hc1 : walkCycleVertices c 1 = p.getVert 1 := by
      simpa only [Nat.cast_one] using spliceFacePath_cycleVertex_prefix p 3 q (by omega) (i := 1) (by omega)
    have hc3 : walkCycleVertices c (3 : ℕ) = x := by
      exact (spliceFacePath_cycleVertex_prefix p 3 q (by omega) (by omega)).trans hx3.symm
    have hc4 : walkCycleVertices c (4 : ℕ) = y := by
      rw [walkCycleVertices_nat_le c (by omega)]
      change (spliceFacePath p 3 q).getVert 4 = y
      simp only [spliceFacePath,Walk.getVert_append,Walk.take_length,
        Nat.min_eq_left (by omega : 3 ≤ p.length),show ¬ (4 < 3) by omega,ite_false]
      rfl
    have hm : (0 : ZMod c.length)-1 = (4 : ℕ) := by rw [hcl]; decide
    have hm4 : (4 : ZMod c.length)-1 = (3 : ℕ) := by rw [hcl]; decide
    have hd1 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) 1) =
        ((walkArcRoot p hp).symm : G.Dart) := by
      apply (Dart.ext_iff _ _).2
      have hp1 : walkCycleVertices p (0+1) = p.getVert 1 := by
        simpa only [zero_add,Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
      have hp0 : walkCycleVertices p 0 = a := by simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
      exact Prod.ext (hc1.trans hp1.symm)
        (by change walkCycleVertices c (1-1) = walkCycleVertices p 0; rw [sub_self,hc0]; exact hp0.symm)
    have hd0 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) 0) =
        (⟨(a,y),hya.symm⟩ : G.Dart) := by
      apply (Dart.ext_iff _ _).2
      exact Prod.ext hc0 (by change walkCycleVertices c (0-1)=y; rw [hm]; exact hc4)
    have hd4 : toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap c hc) (4 : ℕ)) =
        (⟨(y,x),hxy.symm⟩ : G.Dart) := by
      apply (Dart.ext_iff _ _).2
      exact Prod.ext hc4 (by change walkCycleVertices c (4-1)=x; rw [hm4]; exact hc3)
    have hcroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot c hc) := by
      rw [spliceFacePath_root p hp 3 q hq (by omega) (by omega) hmeet]
      exact hroot
    have hf4 := native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support 4)
    have hout : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ c.support :=
      ⟨p.getVert 4,hf4,spliceFacePath_misses_next_vertex p hp 3 q (by omega) (by omega) hmeet⟩
    have h1 := I.short_facial_arc_backward_face_preserved hG c hc (by omega) hcroot hout hbad hsmall 1
    have h0 := I.short_facial_arc_backward_face_preserved hG c hc (by omega) hcroot hout hbad hsmall 0
    rw [sub_self,hd1,hd0] at h1
    rw [hm,hd0,hd4] at h0
    exact ⟨h1,h0⟩
  · exact I.interior_three_path_facial_corners hG p hp hface hroot (by omega) x y hxf hy h2x hxy hya hbad hsmall

/-- A short cycle sharing one actual face corner has degree two at that
corner when a preceding face dart starts outside the cycle. This applies to
the second five-face in source (10), whose face is not the original exterior. -/
theorem short_cycle_single_corner_neighbours (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (r : G.Walk a a) (hr : r.IsCycle) (hlen : r.length ≤ 6)
    (d : G.Dart) (hd : d.fst ∉ r.support)
    (hprev : I.embedding.facePerm d = walkArcRoot r hr)
    (hcorner : I.embedding.facePerm (walkArcRoot r hr) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap r hr) 1)) :
    ∀ z, G.Adj (r.getVert 1) z → z=a ∨ z=r.getVert 2 := by
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hk := hr.three_le_length
  let : NeZero r.length := ⟨by omega⟩
  let hc := walk_isCycleMap r hr
  have hc1 : walkCycleVertices r 1 = r.getVert 1 := by
    simpa only [Nat.cast_one] using walkCycleVertices_nat_le r (i := 1) (by omega)
  have hArc : IsFacialCycleAlong I.embedding hc {r.getVert 1} := by
    intro i hi
    have hi1 : i=1 := hc.inj ((Set.mem_singleton_iff.1 hi).trans hc1.symm)
    subst i
    simpa only [sub_self,hc,walkArcRoot] using hcorner
  have hOutside : ∃ z, OnOuterFace I.embedding (walkArcRoot r hr) z ∧ z ∉ r.support := by
    refine ⟨d.fst,⟨d,?_,rfl⟩,hd⟩
    rw [← hprev]
    exact ((SameCycle.refl I.embedding.facePerm d).apply_right).symm
  have hNoSep : ¬ NativeCycleSeparates I.embedding r hr := by
    intro hsep
    exact hbad (I.extends_of_separating_short_cycle hG r hr
      (by rw [cycle_support_card_eq_length r hr]; exact hlen) hsep hsmall)
  have hrch : r.IsChordless := by
    have hch := short_cycle_isChordless I.girth hc hk hlen
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    apply (walkCycleVertices_edges r hr x y).1
    exact cyclicSubgraph_of_chordless hch (by rw [walkCycleVertices_range r hr]; exact hx)
      (by rw [walkCycleVertices_range r hr]; exact hy) hxy
  intro z hz
  have hzc := neighbours_on_facial_arc_of_not_separating I.embedding (walkArcRoot r hr) hG r hr
    {r.getVert 1} (by intro x hx; have he := Set.mem_singleton_iff.1 hx; exact he ▸ r.getVert_mem_support 1)
    hArc (SameCycle.refl _ _) hOutside hNoSep (r.getVert 1) (Set.mem_singleton _) z hz
  simpa only [Nat.sub_self,Walk.getVert_zero] using
    chordless_native_cycle_vertex_neighbours r hr hrch 1 (by omega) (by omega) hzc hz

end OriginalBoundaryInstance
end Thomassen
