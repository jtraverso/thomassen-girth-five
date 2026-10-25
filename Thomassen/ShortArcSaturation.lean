/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixPathGoodFourthDeletion
public import Thomassen.ShortCycleReduction

/-! Short cycles with an old facial arc cannot contain a hidden inner region. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- If a short native cycle follows an old facial arc and some old face
vertex lies outside it, the arc vertices have no neighbours outside the cycle
in a smallest counterexample. Both face regions and the strict short-cycle
reduction are used; no empty-region assumption is supplied. -/
theorem neighbours_on_short_facial_arc_stay_on_cycle (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6) (A : Set V) (hAC : A ⊆ {x | x ∈ p.support})
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) A)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ p.support := by
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let hc := walk_isCycleMap p hp
  let left := cycleForward hc 0
  let right := cycleBackward hc 0
  let root := toDart (show cyclicSubgraph G (walkCycleVertices p) ≤ G from cyclicSubgraph_le) left
  have hnext : IsNextH I.embedding cyclicSubgraph_le root left :=
    ⟨0,rfl,fun n hn => (Nat.not_lt_zero n hn).elim⟩
  obtain ⟨z,hz,hzout⟩ := houtside
  have hzroot : OnOuterFace I.embedding root z := by
    obtain ⟨d,hd,hdz⟩ := hz
    exact ⟨d,hroot.symm.trans hd,hdz⟩
  have hzleft : z ∈ subfaceSide I.embedding cyclicSubgraph_le left :=
    cycle_original_face_subset_side I.embedding hc hk root (SameCycle.refl _ _) hnext z hzroot
  have hzC : z ∉ Set.range (walkCycleVertices p) := by
    simpa only [walkCycleVertices_range p hp,Set.mem_ofPred_eq] using hzout
  have hzIn : inSubface I.embedding cyclicSubgraph_le left z := by
    rcases hzleft with hzleft | hzleft
    · exact (hzC (by simpa only [cycle_subface_vertices I.embedding hc hk left] using hzleft)).elim
    · exact hzleft
  have hrightEmpty : ∀ w, ¬ inSubface I.embedding cyclicSubgraph_le right w := by
    intro w hw
    apply hbad
    apply I.colourable_of_separating_short_cycle hG p hp ?_ ⟨⟨z,hzIn⟩,⟨w,hw⟩⟩ hsmall
    rw [cycle_support_card_eq_length p hp]
    exact hlen
  by_contra hy
  have hyC : y ∉ Set.range (walkCycleVertices p) := by
    simpa only [walkCycleVertices_range p hp,Set.mem_ofPred_eq] using hy
  have hyCover : y ∈ subfaceSide I.embedding cyclicSubgraph_le left ∪
      subfaceSide I.embedding cyclicSubgraph_le right := by
    rw [cycle_sides_cover I.embedding hc hk hG]
    trivial
  rcases hyCover with hyLeft | hyRight
  · exact cycle_no_exterior_neighbour_along I.embedding hc hk A
      (by intro w hw; rw [walkCycleVertices_range p hp]; exact hAC hw) hArc hx ⟨hyLeft,hyC⟩ hxy
  · rcases hyRight with hyRight | hyRight
    · exact hyC (by simpa only [cycle_subface_vertices I.embedding hc hk right] using hyRight)
    · exact hrightEmpty y hyRight

/-- In the same setting the backward open region is empty, while the forward
region contains an actual old face vertex outside the cycle. -/
theorem short_facial_arc_backward_region_empty (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ w, ¬ inSubface I.embedding cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) 0) w := by
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let hc := walk_isCycleMap p hp
  let root := toDart (show cyclicSubgraph G (walkCycleVertices p) ≤ G from cyclicSubgraph_le) (cycleForward hc 0)
  have hnext : IsNextH I.embedding cyclicSubgraph_le root (cycleForward hc 0) :=
    ⟨0,rfl,fun n hn => (Nat.not_lt_zero n hn).elim⟩
  obtain ⟨z,hz,hzout⟩ := houtside
  have hzroot : OnOuterFace I.embedding root z := by
    obtain ⟨d,hd,hdz⟩ := hz
    exact ⟨d,hroot.symm.trans hd,hdz⟩
  have hzleft := cycle_original_face_subset_side I.embedding hc hk root (SameCycle.refl _ _) hnext z hzroot
  have hzIn : inSubface I.embedding cyclicSubgraph_le (cycleForward hc 0) z := by
    rcases hzleft with h | h
    · have hzC : z ∈ Set.range (walkCycleVertices p) := by
        simpa only [cycle_subface_vertices I.embedding hc hk (cycleForward hc 0)] using h
      exact (hzout (by simpa only [walkCycleVertices_range p hp,Set.mem_ofPred_eq] using hzC)).elim
    · exact h
  intro w hw
  exact hbad (I.colourable_of_separating_short_cycle hG p hp
    (by rw [cycle_support_card_eq_length p hp]; exact hlen) ⟨⟨z,hzIn⟩,⟨w,hw⟩⟩ hsmall)

/-- Close a short prefix of the actual old face by an interior path. When
the resulting cycle has at most six vertices, every neighbour of an internal
prefix vertex lies on that cycle in a smallest counterexample. The facial
arc, its old root and a genuine outside vertex are all derived. -/
theorem neighbours_on_short_closed_face_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i : ℕ) (hi : 0 < i) (hin : i < n) (y : V) (hadj : G.Adj (p.getVert i) y) :
    y ∈ (spliceFacePath p n q).support := by
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot n q hInner
  let r := spliceFacePath p n q
  have hr : r.IsCycle := spliceFacePath_isCycle p hp n q hq hn (by omega) hmeet
  have hrl : r.length ≤ 6 := by rw [spliceFacePath_length p n q (by omega)]; exact hshort
  let A := cycleInterval (walkCycleVertices r) 1 (n-2)
  have hA : A ⊆ {x | x ∈ r.support} := by
    intro x hx
    obtain ⟨j,hj,hjx⟩ := hx
    have hrj : (1+j : ℕ) ≤ r.length := by rw [spliceFacePath_length p n q (by omega)]; omega
    rw [walkCycleVertices_nat_le r hrj] at hjx
    exact hjx ▸ r.getVert_mem_support _
  have hxA : p.getVert i ∈ A := by
    refine ⟨i-1,by omega,?_⟩
    have he : 1+(i-1)=i := by omega
    rw [he]
    exact spliceFacePath_cycleVertex_prefix p n q (by omega) (by omega)
  have hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap r hr) A :=
    spliceFacePath_isFacialAlong I.embedding p hp hface n q hq hn (by omega) hql hmeet
  have hrroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot r hr) := by
    rw [spliceFacePath_root p hp n q hq hn (by omega) hmeet]
    exact hroot
  have hout : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ r.support :=
    ⟨p.getVert (n+1),native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _
      (p.getVert_mem_support _),spliceFacePath_misses_next_vertex p hp n q hn hnp hmeet⟩
  exact I.neighbours_on_short_facial_arc_stay_on_cycle hG r hr hrl A hA hArc hrroot hout hbad hsmall
    (p.getVert i) hxA y hadj

end Thomassen.BoundaryInstance
