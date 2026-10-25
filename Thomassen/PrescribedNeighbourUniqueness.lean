/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CentralPrescribedTwoPath

/-! Interior vertices have at most one prescribed neighbour in a counterexample. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Neighbours of a vertex outside a simple path in girth five are separated
by at least three edges on that path. -/
lemma path_neighbour_indices_gap (hg : 5 ≤ G.egirth) {a t u : V}
    (r : G.Walk a t) (hr : r.IsPath) (hu : u ∉ r.support) (i j : ℕ)
    (hij : i < j) (hj : j ≤ r.length) (hui : G.Adj u (r.getVert i)) (huj : G.Adj u (r.getVert j)) :
    i+3 ≤ j := by
  by_contra h
  rcases (by omega : j=i+1 ∨ j=i+2) with he | he
  · exact neighbors_nonadjacent hg hui huj (by rw [he]; exact r.adj_getVert_succ (by omega))
  · have hne : r.getVert i ≠ r.getVert j := by
      intro heq
      have hidx := hr.getVert_injOn (by change i ≤ r.length; omega) hj heq
      omega
    have huj' : G.Adj (r.getVert (i+2)) u := by rw [← he]; exact huj.symm
    have hadj : G.Adj (r.getVert (i+2)) (r.getVert (i+1)) := by
      simpa only [Nat.add_assoc] using (r.adj_getVert_succ (by omega : i+1 < r.length)).symm
    have heq := common_neighbor_unique hg (by simpa only [he] using hne) hui.symm huj'
      (r.adj_getVert_succ (by omega : i < r.length)) hadj
    exact hu (heq ▸ r.getVert_mem_support _)

namespace BoundaryInstance
variable [Fintype V]

/-- The initial-endpoint two-path exclusion holds for the original arbitrary
face and either prescribed-path orientation. -/
theorem no_interior_prescribed_pair_at_initial_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : y ∈ I.precolor.vertices) (hya : y ≠ a) (hua : G.Adj u a) (huy : G.Adj u y) : False := by
  have hyR : y ∈ r.support := by simpa only [hP,BoundaryPrecolor.vertices,List.mem_toFinset] using hy
  have hrpos : 0 < r.length := by
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hyR
    by_contra h
    have hi0 : i=0 := by omega
    exact hya (by simpa only [hi0,Walk.getVert_zero] using hi.symm)
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · have hfirst : p.getVert 1 ∈ I.precolor.vertices := by
      rw [← horder 1 (by omega),hP]
      exact List.mem_toFinset.2 (r.getVert_mem_support 1)
    exact I.no_interior_two_path_from_forward_prescribed_endpoint hG p hp hface hroot
      (fun z hz => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot z).2 hz)
      r hr hn hP hfirst hbad hsmall u y hu (I.on_outer y hy) hya hua huy
  · have hfirst : p.getVert 1 ∈ I.mirror.precolor.vertices := by
      change p.getVert 1 ∈ I.precolor.vertices
      rw [← horder 1 (by omega),hP]
      exact List.mem_toFinset.2 (r.getVert_mem_support 1)
    have huM : ¬ OnOuterFace I.mirror.embedding I.mirror.outer u :=
      fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h)
    exact I.mirror.no_interior_two_path_from_forward_prescribed_endpoint hG p hp hface hroot
      (fun z hz => (native_facial_cycle_support_iff I.mirror.embedding I.mirror.outer p hp hface hroot z).2 hz)
      r hr hn hP hfirst hbad hsmall u y huM (I.mirror.on_outer y hy) hya hua huy

/-- The terminal-endpoint exclusion is obtained by reversing the actual native
prescription. Its vertices, edges, lists and all instance invariants are kept. -/
theorem no_interior_prescribed_pair_at_terminal_vertex (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hy : y ∈ I.precolor.vertices) (hyt : y ≠ t) (hut : G.Adj u t) (huy : G.Adj u y) : False := by
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
  exact J.no_interior_prescribed_pair_at_initial_vertex r.reverse hr.reverse hnrev rfl hbad hsmall
    u y hu ((hPv y).2 hy) hyt hut huy

/-- In a minimal counterexample no interior vertex has two distinct old
prescribed neighbours. Endpoint cases, all girth obstructions and the sole
central six-vertex configuration are resolved, for arbitrary original faces. -/
theorem interior_prescribed_neighbour_unique (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : x ∈ I.precolor.vertices) (hy : y ∈ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x=y := by
  by_contra hxy
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hrlen : r.length ≤ 5 := by
    have h := hn
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at h
    omega
  have huR : u ∉ r.support := fun h => hu (I.on_outer u ((hPv u).2 h))
  by_cases hxa : x=a
  · exact I.no_interior_prescribed_pair_at_initial_vertex r hr hn hP hbad hsmall u y hu hy
      (fun h => hxy (hxa.trans h.symm)) (hxa ▸ hux) huy
  by_cases hya : y=a
  · exact I.no_interior_prescribed_pair_at_initial_vertex r hr hn hP hbad hsmall u x hu hx
      hxa (hya ▸ huy) hux
  by_cases hxt : x=t
  · exact I.no_interior_prescribed_pair_at_terminal_vertex r hr hn hP hbad hsmall u y hu hy
      (fun h => hxy (hxt.trans h.symm)) (hxt ▸ hux) huy
  by_cases hyt : y=t
  · exact I.no_interior_prescribed_pair_at_terminal_vertex r hr hn hP hbad hsmall u x hu hx
      hxt (hyt ▸ huy) hux
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv x).1 hx)
  obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv y).1 hy)
  have hi0 : i ≠ 0 := fun h => hxa (by simpa only [h,Walk.getVert_zero] using hi.symm)
  have hj0 : j ≠ 0 := fun h => hya (by simpa only [h,Walk.getVert_zero] using hj.symm)
  have hin : i ≠ r.length := fun h => hxt (by simpa only [h,Walk.getVert_length] using hi.symm)
  have hjn : j ≠ r.length := fun h => hyt (by simpa only [h,Walk.getVert_length] using hj.symm)
  have hij : i ≠ j := fun h => hxy (hi.symm.trans ((congrArg r.getVert h).trans hj))
  have hgap : i+3 ≤ j ∨ j+3 ≤ i := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (path_neighbour_indices_gap I.girth r hr huR i j h hjl (by rwa [hi]) (by rwa [hj]))
    · exact Or.inr (path_neighbour_indices_gap I.girth r hr huR j i h hil (by rwa [hj]) (by rwa [hi]))
  have hrl : r.length=5 := by omega
  have hcen : (i=1 ∧ j=4) ∨ (i=4 ∧ j=1) := by omega
  apply hbad
  apply I.colourable_of_central_prescribed_two_path_arbitrary_face r hr hn hP hrl u hu ?_ ?_ hsmall
  · rcases hcen with ⟨h,_⟩ | ⟨_,h⟩
    · simpa only [← hi,h] using hux
    · simpa only [← hj,h] using huy
  · rcases hcen with ⟨_,h⟩ | ⟨h,_⟩
    · simpa only [← hj,h] using huy
    · simpa only [← hi,h] using hux

end BoundaryInstance
end Thomassen
