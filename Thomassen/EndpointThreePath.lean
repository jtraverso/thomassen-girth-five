/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortEndpointThreePath

/-! Three-path cuts at either endpoint of the original prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The free complementary facial arc closes every interior three-path from
the initial prescribed endpoint to an unprescribed boundary vertex, regardless
of the latter's list size. -/
theorem colourable_of_initial_prescribed_endpoint_three_path_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hua : G.Adj u a) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hbrange : b ∈ Set.range (walkCycleVertices p) := by
    rw [walkCycleVertices_range p hp]; exact (hverts b).2 hb
  obtain ⟨j,hjb⟩ := hbrange
  have hjp : j.val < p.length := ZMod.val_lt j
  have hjv : p.getVert j.val = b := hjb
  have hrj : r.length < j.val := by
    by_contra h
    apply hbP ((hPv b).2 ?_)
    rw [← hjv,← horder j.val (by omega)]
    exact r.getVert_mem_support _
  have hav : a ≠ v2 := fun h => hv (h ▸ I.on_outer a ((hPv a).2 r.start_mem_support))
  have hub : u ≠ b := fun h => hu (h.symm ▸ hb)
  have hNoAdj : ¬ G.Adj a b := by
    intro h
    exact hub (common_neighbor_unique I.girth hav hua.symm huv.symm h hvb)
  have hjlast : j.val+2 ≤ p.length := by
    by_contra h
    have he : j.val+1=p.length := by omega
    apply hNoAdj
    have hadj := (p.adj_getVert_succ hjp).symm
    simpa only [he,Walk.getVert_length,hjv] using hadj
  obtain ⟨q,hq,hqlen,hqo,hqface,hqroot⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot j.val hjp
  have hqa : q.getVert (p.length-j.val) = a := by
    rw [hqo _ (by omega),Nat.add_sub_of_le (by omega : j.val ≤ p.length),ZMod.natCast_self]
    simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
  have hfree : ∀ z ∈ I.precolor.vertices,
      z ∉ cycleInterval (walkCycleVertices q) 1 (p.length-j.val-2) := by
    intro z hz hzarc
    obtain ⟨k,hkz,hkr⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hz)
    obtain ⟨l,hl,hlz⟩ := hzarc
    rw [walkCycleVertices_nat_le q (by omega : 1+l ≤ q.length),hqo (1+l) (by omega),
      walkCycleVertices_nat_le p (by omega : j.val+(1+l) ≤ p.length)] at hlz
    have he := hp.getVert_injOn' (show k ≤ p.length-1 from by omega)
      (show j.val+(1+l) ≤ p.length-1 from by omega)
      ((horder k hkr).symm.trans (hkz.trans hlz.symm))
    omega
  apply hbad
  apply I.colourable_of_interior_three_path_free_arc_terminal_short hG q hq hqface hqroot
    (p.length-j.val) (by omega) (by omega) v2 u hv hu (by rwa [hjv]) huv.symm
    (by rwa [hqa]) ?_ hfree hsmall
  rw [hqa,I.singleton a ((hPv a).2 r.start_mem_support),Finset.card_singleton]
  omega

/-- Initial endpoint three-path exclusion, deriving the actual native face
and its orientation from the original instance. -/
theorem colourable_of_initial_prescribed_endpoint_three_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hua : G.Adj u a) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.colourable_of_initial_prescribed_endpoint_three_path_on_native_face hG p hp hface hroot
      r hr hn hP hrpos horder b u v2 hb hbP hu hv hua huv hvb hsmall
  · have hm := mirror_onOuterFace_iff I.embedding I.outer
    exact I.mirror.colourable_of_initial_prescribed_endpoint_three_path_on_native_face hG p hp hface hroot
      r hr hn hP hrpos horder b u v2 ((hm b).2 hb) hbP
      (fun h => hu ((hm u).1 h)) (fun h => hv ((hm v2).1 h)) hua huv hvb hsmall

/-- Terminal endpoint three-path exclusion, using the same exact lists and
prescribed colours with the original path reversed. -/
theorem colourable_of_terminal_prescribed_endpoint_three_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hut : G.Adj u t) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
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
  exact J.colourable_of_initial_prescribed_endpoint_three_path r.reverse hr.reverse hnrev rfl
    (by simpa only [Walk.length_reverse] using hrpos) b u v2 hb (fun h => hbP ((hPv b).1 h)) hu hv hut huv hvb hsmall

/-- The structural three-path step: a free boundary endpoint with an old
short list, or a prescribed initial/terminal endpoint at the other end, always
closes the strict-induction case. Two unrestricted free three-list endpoints
are intentionally retained for the final deletion argument. -/
theorem colourable_of_three_path_forbidden_boundary_configuration (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : OnOuterFace I.embedding I.outer x)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hforbidden : (I.lists b).card ≤ 2 ∨ x=a ∨ x=t)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  rcases hforbidden with hbShort | hxa | hxt
  · exact I.colourable_of_three_path_short_free_boundary_endpoint r hr hn hP hrpos
      x b u v2 hx hb hbP hbShort hu hv hux huv hvb hsmall
  · exact I.colourable_of_initial_prescribed_endpoint_three_path r hr hn hP hrpos
      b u v2 hb hbP hu hv (hxa ▸ hux) huv hvb hsmall
  · exact I.colourable_of_terminal_prescribed_endpoint_three_path r hr hn hP hrpos
      b u v2 hb hbP hu hv (hxt ▸ hux) huv hvb hsmall

end Thomassen.BoundaryInstance
