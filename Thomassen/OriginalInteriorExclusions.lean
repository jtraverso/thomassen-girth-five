/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalDegree

/-! Source reductions (4) and (5) with arbitrary endpoints on the old face. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Nonadjacent distinct endpoints are separated by at least two steps in
each direction of a native cycle. -/
theorem cycle_index_bounds_of_nonadjacent {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n : ℕ) (hn : n < p.length) (hna : p.getVert n ≠ a)
    (hno : ¬ G.Adj a (p.getVert n)) : 2 ≤ n ∧ n+2 ≤ p.length := by
  have hn0 : n ≠ 0 := fun h => hna (by simp only [h,Walk.getVert_zero])
  have hn1 : n ≠ 1 := by
    intro h
    have he := p.adj_getVert_succ (by have := hp.three_le_length; omega : 0 < p.length)
    exact hno (by simpa only [Walk.getVert_zero,zero_add,← h] using he)
  have hnlast : n+1 ≠ p.length := by
    intro h
    have he := p.adj_getVert_succ hn
    rw [h,Walk.getVert_length] at he
    exact hno he.symm
  omega

namespace OriginalBoundaryInstance
variable [Fintype V]

/-- Rebase the actual minimal-counterexample face at any one of its vertices.
The native cycle, face corners and exact old boundary are preserved. -/
theorem exists_native_face_cycle_at (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u : V) (hu : OnOuterFace I.embedding I.outer u) :
    ∃ p : G.Walk u u, ∃ hp : p.IsCycle,
      5 ≤ p.length ∧ IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧
      SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) := by
  obtain ⟨_,_,_,a,p,hp,_,_,hverts,hface,hroot⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  obtain ⟨s,hs⟩ := (walkCycleVertices_range p hp).symm ▸
    (show u ∈ {x | x ∈ p.support} from (hverts u).2 hu)
  subst u
  obtain ⟨q,hq,hql,_,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp
    hface (by rw [hroot]) s.val (ZMod.val_lt s)
  refine ⟨q,hq,five_le_egirth_iff.1 I.girth _ q hq,hqface,hqroot,?_⟩
  exact native_facial_cycle_support_iff I.embedding I.outer q hq hqface hqroot

/-- Original reduction (4), independent of the chosen facial indexing:
a short vertex and another distinct old outer vertex have no common interior
neighbour in a minimal original counterexample. -/
theorem no_interior_two_path_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u v z : V) (hu : u ∈ I.short) (hv : OnOuterFace I.embedding I.outer v)
    (huv : u ≠ v) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hzu : G.Adj z u) (hzv : G.Adj z v) : False := by
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  obtain ⟨p,hp,_,hface,hroot,hverts⟩ := I.exists_native_face_cycle_at hbad hsmall u (I.on_outer u hu)
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  obtain ⟨n,hn⟩ := (walkCycleVertices_range p hp).symm ▸
    (show v ∈ {x | x ∈ p.support} from (hverts v).2 hv)
  change p.getVert n.val = v at hn
  have hna : p.getVert n.val ≠ u := by rw [hn]; exact huv.symm
  have hno : ¬ G.Adj u (p.getVert n.val) := by
    rw [hn]
    exact neighbors_nonadjacent I.girth hzu hzv
  obtain ⟨hn2,hnp⟩ := cycle_index_bounds_of_nonadjacent p hp n.val (ZMod.val_lt n) hna hno
  exact hbad (I.extends_of_interior_two_path hG p hp hface hroot hu n.val hn2 hnp z hz hzu
    (by simpa only [hn] using hzv) hsmall)

/-- Original reduction (5), independent of facial indexing: no interior
three-edge path joins two distinct old short vertices in a minimal original
counterexample. -/
theorem no_interior_three_path_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u v z w : V) (hu : u ∈ I.short) (hv : v ∈ I.short) (huv : u ≠ v)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hw : ¬ OnOuterFace I.embedding I.outer w)
    (huz : G.Adj u z) (hzw : G.Adj z w) (hwv : G.Adj w v) : False := by
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  obtain ⟨p,hp,_,hface,hroot,hverts⟩ := I.exists_native_face_cycle_at hbad hsmall u (I.on_outer u hu)
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  obtain ⟨n,hn⟩ := (walkCycleVertices_range p hp).symm ▸
    (show v ∈ {x | x ∈ p.support} from (hverts v).2 (I.on_outer v hv))
  change p.getVert n.val = v at hn
  have hna : p.getVert n.val ≠ u := by rw [hn]; exact huv.symm
  have hno : ¬ G.Adj u (p.getVert n.val) := by
    rw [hn]
    intro huv'
    have huw : u ≠ w := fun h => hw (h ▸ I.on_outer u hu)
    have hzv : z ≠ v := fun h => hz (h.symm ▸ I.on_outer v hv)
    exact hzv (common_neighbor_unique I.girth huw huz hzw.symm huv' hwv)
  obtain ⟨hn2,hnp⟩ := cycle_index_bounds_of_nonadjacent p hp n.val (ZMod.val_lt n) hna hno
  have hnA : p.getVert n.val ∈ I.short := hn ▸ hv
  exact hbad (I.extends_of_interior_three_path hG p hp hface hroot hu n.val hn2 hnp hnA w z hw hz
    (by simpa only [hn] using hwv.symm) hzw.symm huz.symm hsmall)

end OriginalBoundaryInstance
end Thomassen
