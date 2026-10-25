/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalPredecessor

/-! Five-face attachments, including the old-boundary endpoint in source (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A short closing path saturates each internal old-prefix vertex: its
only neighbours are the preceding and succeeding native prefix vertices. -/
theorem short_closed_prefix_neighbours (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (i : ℕ) (hi : 0 < i) (hin : i < n) :
    ∀ z, G.Adj (p.getVert i) z → z=p.getVert (i-1) ∨ z=p.getVert (i+1) := by
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot n q hInner
  let c := spliceFacePath p n q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp n q hq hn (by omega) hmeet
  have hcl : c.length ≤ 6 := by rw [spliceFacePath_length p n q (by omega)]; exact hshort
  have hcch : c.IsChordless := by
    let : NeZero c.length := ⟨by have := hc.three_le_length; omega⟩
    have hch := short_cycle_isChordless I.girth (walk_isCycleMap c hc) hc.three_le_length hcl
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    apply (walkCycleVertices_edges c hc x y).1
    exact cyclicSubgraph_of_chordless hch (by rw [walkCycleVertices_range c hc]; exact hx)
      (by rw [walkCycleVertices_range c hc]; exact hy) hxy
  have hci : c.getVert i = p.getVert i := spliceFacePath_getVert_prefix p n q (by omega) (by omega)
  have hcp : c.getVert (i-1) = p.getVert (i-1) := spliceFacePath_getVert_prefix p n q (by omega) (by omega)
  have hcn : c.getVert (i+1) = p.getVert (i+1) := spliceFacePath_getVert_prefix p n q (by omega) (by omega)
  intro z hz
  have hzc := I.neighbours_on_short_closed_face_prefix hG p hp hface hroot n hn hnp q hq
    hql hshort hInner hbad hsmall i hi hin z hz
  have hiz : G.Adj (c.getVert i) z := by rwa [hci]
  have hilen : i+1 ≤ c.length := by rw [spliceFacePath_length p n q (by omega)]; omega
  simpa only [hcp,hcn] using chordless_native_cycle_vertex_neighbours c hc hcch i hi hilen hzc hiz

/-- If the first vertex on the closing three-path is old-boundary, it is
exactly the next boundary vertex and the preceding exceptional endpoint has
degree two. This is the boundary possibility explicitly allowed in source (10). -/
theorem boundary_three_path_first_vertex (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y : V)
    (hxface : OnOuterFace I.embedding I.outer x) (hx1 : x ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y)
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    x=p.getVert 3 ∧
      (∀ z, G.Adj (p.getVert 2) z → z=p.getVert 1 ∨ z=x) ∧
      (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) := by
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hx3 : x=p.getVert 3 :=
    (chordless_native_cycle_vertex_neighbours p hp hch 2 (by omega) (by omega)
      ((hverts x).2 hxface) h2x).resolve_left hx1
  have h3a : p.getVert 3 ≠ a := by
    intro he
    have hidx := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega)
      (show 0 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using he)
    omega
  let q : G.Walk (p.getVert 3) a := .cons (show G.Adj (p.getVert 3) y from hx3 ▸ hxy) (.cons hya .nil)
  have h3y : p.getVert 3 ≠ y := by simpa only [← hx3] using hxy.ne
  have hq : q.IsPath := by
    simp [q,Walk.isPath_def,h3a,h3y,hya.ne]
  have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
    intro j hj hjl
    have hj1 : j=1 := by change j < 2 at hjl; omega
    subst j
    exact hy
  refine ⟨hx3,?_,?_⟩
  · intro z hz
    have h := I.short_closed_prefix_neighbours hG p hp hface hroot 3 (by omega) (by omega) q hq
      (by change 0 < 2; omega) (by change 3+2 ≤ 6; omega) hInner hbad hsmall 2 (by omega) (by omega) z hz
    simpa only [← hx3] using h
  · intro z hz
    have h := I.short_closed_prefix_neighbours hG p hp hface hroot 3 (by omega) (by omega) q hq
      (by change 0 < 2; omega) (by change 3+2 ≤ 6; omega) hInner hbad hsmall 1 (by omega) (by omega) z hz
    simpa only [Nat.sub_self,Walk.getVert_zero] using h

/-- Across two old facial edges the closing three-path is unique even when
its first new vertex is the next old-boundary vertex. Its other new vertex
is required to be interior, exactly as in the original residual obstruction. -/
theorem three_path_across_two_face_edges_unique_allow_boundary (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y x' y' : V)
    (hx1 : x ≠ p.getVert 1) (hx1' : x' ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y) (hy' : ¬ OnOuterFace I.embedding I.outer y')
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (h2x' : G.Adj (p.getVert 2) x') (hxy' : G.Adj x' y') (hya' : G.Adj y' a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : x=x' ∧ y=y' := by
  have hfacekey : ∀ z t z' t', OnOuterFace I.embedding I.outer z → z ≠ p.getVert 1 →
      z' ≠ p.getVert 1 → ¬ OnOuterFace I.embedding I.outer t →
      G.Adj (p.getVert 2) z → G.Adj z t → G.Adj t a →
      G.Adj (p.getVert 2) z' → G.Adj z' t' → G.Adj t' a → z=z' ∧ t=t' := by
    intro z t z' t' hzf hz1 hz1' ht h2z hzt hta h2z' hzt' hta'
    obtain ⟨hz3,hneigh,_⟩ := I.boundary_three_path_first_vertex hG p hp hch hface hroot hlen
      z t hzf hz1 ht h2z hzt hta hbad hsmall
    have hzz' : z=z' := ((hneigh z' h2z').resolve_left hz1').symm
    have hza : z ≠ a := by
      intro he
      have hidx := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega)
        (show 0 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using hz3.symm.trans he)
      omega
    refine ⟨hzz',?_⟩
    exact common_neighbor_unique I.girth hza hzt hta.symm (hzz'.symm ▸ hzt') hta'.symm
  by_cases hxf : OnOuterFace I.embedding I.outer x
  · exact hfacekey x y x' y' hxf hx1 hx1' hy h2x hxy hya h2x' hxy' hya'
  · by_cases hxf' : OnOuterFace I.embedding I.outer x'
    · obtain ⟨hx,hy⟩ := hfacekey x' y' x y hxf' hx1' hx1 hy' h2x' hxy' hya' h2x hxy hya
      exact ⟨hx.symm,hy.symm⟩
    · exact I.interior_three_path_across_two_face_edges_unique hG p hp hface hroot (by omega)
        x y x' y' hxf hy hxf' hy' h2x hxy hya h2x' hxy' hya' hbad hsmall

end Thomassen.OriginalBoundaryInstance
