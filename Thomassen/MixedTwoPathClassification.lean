/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedTwoPathExceptions

/-! Complete mixed two-path classification, including prescribed endpoints. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The initial-endpoint two-path exclusion holds for the original arbitrary
face and either prescribed-path orientation. -/
theorem no_interior_boundary_pair_at_initial_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a) (hua : G.Adj u a) (huy : G.Adj u y) : False := by
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · have hfirst : p.getVert 1 ∈ I.precolor.vertices := by
      rw [← horder 1 (by omega),hP]
      exact List.mem_toFinset.2 (r.getVert_mem_support 1)
    exact I.no_interior_two_path_from_forward_prescribed_endpoint hG p hp hface hroot
      (fun z hz => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot z).2 hz)
      r hr hn hP hfirst hbad hsmall u y hu hy hya hua huy
  · have hfirst : p.getVert 1 ∈ I.mirror.precolor.vertices := by
      change p.getVert 1 ∈ I.precolor.vertices
      rw [← horder 1 (by omega),hP]
      exact List.mem_toFinset.2 (r.getVert_mem_support 1)
    have huM : ¬ OnOuterFace I.mirror.embedding I.mirror.outer u :=
      fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h)
    exact I.mirror.no_interior_two_path_from_forward_prescribed_endpoint hG p hp hface hroot
      (fun z hz => (native_facial_cycle_support_iff I.mirror.embedding I.mirror.outer p hp hface hroot z).2 hz)
      r hr hn hP hfirst hbad hsmall u y huM ((mirror_onOuterFace_iff I.embedding I.outer y).2 hy) hya hua huy

/-- The terminal-endpoint exclusion is obtained by reversing the actual native
prescription. Its vertices, edges, lists and all instance invariants are kept. -/
theorem no_interior_boundary_pair_at_terminal_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : OnOuterFace I.embedding I.outer y) (hyt : y ≠ t) (hut : G.Adj u t) (huy : G.Adj u y) : False := by
  have hnrev : r.reverse.support.toFinset.card ≤ 6 := by
    simpa only [Walk.support_reverse,List.toFinset_reverse] using hn
  let P : BoundaryPrecolor G := .path r.reverse hr.reverse hnrev
  have hPv : ∀ z, z ∈ P.vertices ↔ z ∈ I.precolor.vertices := by
    intro z; simp only [P,hP,BoundaryPrecolor.vertices,Walk.support_reverse,List.toFinset_reverse]
  have hPe : ∀ z w, s(z,w) ∈ P.edges ↔ s(z,w) ∈ I.precolor.edges := by
    intro z w; simp only [P,hP,BoundaryPrecolor.edges,Walk.edges_reverse,List.toFinset_reverse]
  let J : BoundaryInstance G C := {
    girth := I.girth
    embedding := I.embedding
    outer := I.outer
    precolor := P
    lists := I.lists
    prescribed := I.prescribed
    on_outer := fun z hz => I.on_outer z ((hPv z).1 hz)
    singleton := fun z hz => I.singleton z ((hPv z).1 hz)
    proper_precolor := fun {z w} hzw => I.proper_precolor ((hPe z w).1 hzw)
    boundary_lists := fun z hz hzP => I.boundary_lists z hz (fun h => hzP ((hPv z).2 h))
    interior_lists := I.interior_lists
    short_edges := fun {z w} hzw hz hw => (hPe z w).2 (I.short_edges hzw hz hw) }
  exact J.no_interior_boundary_pair_at_initial_vertex r.reverse hr.reverse hnrev rfl (by simpa only [Walk.length_reverse] using hrpos) hbad hsmall
    u y hu hy hyt hut huy


/-- Without any facial orientation or index supplied, the only mixed
prescribed/free pair of boundary neighbours in a counterexample is one of
the two exceptional configurations for six prescribed vertices. -/
theorem interior_prescribed_and_free_neighbours_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hux : G.Adj u x) (hub : G.Adj u b) :
    r.length=5 ∧ ((x=r.getVert 2 ∧ G.Adj a b) ∨ (x=r.getVert 3 ∧ G.Adj t b)) := by
  have hxR : x ∈ r.support := by simpa only [hP,BoundaryPrecolor.vertices,List.mem_toFinset] using hx
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hxR
  have hba : b ≠ a := by
    intro h
    apply hbP
    rw [h,hP]
    exact List.mem_toFinset.2 r.start_mem_support
  have hbt : b ≠ t := by
    intro h
    apply hbP
    rw [h,hP]
    exact List.mem_toFinset.2 r.end_mem_support
  have hi0 : i ≠ 0 := by
    intro hi0
    have hxa : x=a := by simpa only [hi0,Walk.getVert_zero] using hi.symm
    exact I.no_interior_boundary_pair_at_initial_vertex r hr hn hP hrpos hbad hsmall
      u b hu hb hba (hxa ▸ hux) hub
  have hin : i ≠ r.length := by
    intro hin
    have hxt : x=t := by simpa only [hin,Walk.getVert_length] using hi.symm
    exact I.no_interior_boundary_pair_at_terminal_vertex r hr hn hP hrpos hbad hsmall
      u b hu hb hbt (hxt ▸ hux) hub
  obtain ⟨hlen,hcase⟩ := I.mixed_interior_two_path_exceptional r hr hn hP i (by omega) (by omega)
    hbad hsmall u b hu hb hbP (by rwa [hi]) hub
  refine ⟨hlen,?_⟩
  rcases hcase with ⟨hi2,hab⟩ | ⟨hi3,htb⟩
  · exact Or.inl ⟨by simpa only [hi2] using hi.symm,hab⟩
  · exact Or.inr ⟨by simpa only [hi3] using hi.symm,htb⟩

/-- With two to five old prescribed vertices, every mixed interior two-path
is a complete strict-induction case. The six-vertex exceptions are impossible. -/
theorem colourable_of_mixed_two_path_with_at_most_five_prescribed_vertices (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (u x b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hux : G.Adj u x) (hub : G.Adj u b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hlen := (I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP hrpos
    hbad hsmall u x b hu hx hb hbP hux hub).1
  rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at hn5
  omega

end Thomassen.BoundaryInstance
