/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortPathGoodFourthDeletion

/-! Exact classification of all interior boundary-neighbour pairs. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Every distinct boundary-neighbour pair of an interior vertex is exactly
one of the two mixed six-vertex exceptions, in either order. -/
theorem interior_boundary_pair_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxy : x ≠ y) (hux : G.Adj u x) (huy : G.Adj u y) :
    r.length=5 ∧
    ((x=r.getVert 2 ∧ y ∉ I.precolor.vertices ∧ G.Adj a y) ∨
     (x=r.getVert 3 ∧ y ∉ I.precolor.vertices ∧ G.Adj t y) ∨
     (y=r.getVert 2 ∧ x ∉ I.precolor.vertices ∧ G.Adj a x) ∨
     (y=r.getVert 3 ∧ x ∉ I.precolor.vertices ∧ G.Adj t x)) := by
  have hlen : 2 ≤ r.length := by
    by_contra h
    exact hbad (I.colourable_of_prescribed_edge r hr hn hP (by omega) hsmall)
  by_cases hxP : x ∈ I.precolor.vertices <;> by_cases hyP : y ∈ I.precolor.vertices
  · exact (hxy (I.interior_prescribed_neighbour_unique r hr hn hP hbad hsmall u x y hu hxP hyP hux huy)).elim
  · obtain ⟨hl,hcase⟩ := I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP hrpos
      hbad hsmall u x y hu hxP hy hyP hux huy
    refine ⟨hl,?_⟩
    rcases hcase with ⟨hx2,hay⟩ | ⟨hx3,hty⟩
    · exact Or.inl ⟨hx2,hyP,hay⟩
    · exact Or.inr (Or.inl ⟨hx3,hyP,hty⟩)
  · obtain ⟨hl,hcase⟩ := I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP hrpos
      hbad hsmall u y x hu hyP hx hxP huy hux
    refine ⟨hl,?_⟩
    rcases hcase with ⟨hy2,hax⟩ | ⟨hy3,htx⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hy2,hxP,hax⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hy3,hxP,htx⟩))
  · exact (hxy (I.interior_unprescribed_neighbour_unique r hr hn hP hlen hbad hsmall u x y hu hx hy hxP hyP hux huy)).elim

/-- An old short free boundary vertex cannot participate in either mixed
exception, because each exceptional free vertex adjoins a prescribed end. -/
theorem interior_neighbours_unique_at_short_free_boundary_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hxShort : (I.lists x).card ≤ 2)
    (hux : G.Adj u x) (huy : G.Adj u y) : x=y := by
  by_contra hxy
  obtain ⟨_,hcase⟩ := I.interior_boundary_pair_exceptional r hr hn hP hrpos hbad hsmall u x y hu hx hy hxy hux huy
  have hPmem : ∀ k, r.getVert k ∈ I.precolor.vertices := by
    intro k; rw [hP]; exact List.mem_toFinset.2 (r.getVert_mem_support k)
  have haP : a ∈ I.precolor.vertices := by simpa only [Walk.getVert_zero] using hPmem 0
  have htP : t ∈ I.precolor.vertices := by simpa only [Walk.getVert_length] using hPmem r.length
  rcases hcase with ⟨hx2,_,_⟩ | ⟨hx3,_,_⟩ | ⟨_,_,hax⟩ | ⟨_,_,htx⟩
  · exact hxP (hx2 ▸ hPmem 2)
  · exact hxP (hx3 ▸ hPmem 3)
  · exact I.short_not_adj_precolored hxP haP hxShort hax.symm
  · exact I.short_not_adj_precolored hxP htP hxShort htx.symm

end Thomassen.BoundaryInstance
