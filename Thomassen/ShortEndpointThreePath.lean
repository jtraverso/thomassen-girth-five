/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedThreePathClosure

/-! Global three-path exclusion from an unprescribed old short boundary list. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The completed short-endpoint three-path case works on every specified
old facial subarc, with exact transport of its prescription-free condition. -/
theorem colourable_of_interior_three_path_free_subarc_one_short_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u (p.getVert s)) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists (p.getVert s)).card ≤ 2 ∨ (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨q, hq, hqlen, horder, hqface, hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot s (by omega)
  have hqn : q.getVert (n - s) = p.getVert n := by
    rw [horder (n - s) (by omega), Nat.add_sub_of_le (by omega : s ≤ n)]
    exact walkCycleVertices_nat_le p (by omega)
  have hPq : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices q) 1 (n - s - 2) := by
    intro x hx
    rw [rebased_native_cycleInterval p q s (n - s - 2) hqlen horder (by omega)]
    exact hPoutside x hx
  exact I.colourable_of_interior_three_path_free_arc_one_short_endpoint hG q hq hqface hqroot (n - s) (by omega) (by omega)
    u v hu hv hua huv (by rwa [hqn]) (hashort.imp_left id |>.imp_right (by intro h; rwa [hqn])) hPq hsmall

theorem colourable_of_free_three_path_short_endpoint_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u v2 x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvy : G.Adj v2 y)
    (hyShort : (I.lists y).card ≤ 2) : ListColourable G I.lists := by
  by_contra hbad
  have hverts : ∀ z, z ∈ p.support ↔ OnOuterFace I.embedding I.outer z :=
    native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  obtain ⟨q,hq,hqlen,hqo,hqface,hqroot⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot r.length (by omega)
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hindex : ∀ z, OnOuterFace I.embedding I.outer z → z ∉ I.precolor.vertices →
      ∃ j : ℕ, r.length < j ∧ j < p.length ∧ p.getVert j = z := by
    intro z hz hzP
    have hzrange : z ∈ Set.range (walkCycleVertices p) := by
      rw [walkCycleVertices_range p hp]; exact (hverts z).2 hz
    obtain ⟨i,hi⟩ := hzrange
    have hil : i.val < p.length := ZMod.val_lt i
    refine ⟨i.val,?_,hil,hi⟩
    by_contra h
    have hile : i.val ≤ r.length := by omega
    apply hzP ((hPv z).2 ?_)
    have hiv : p.getVert i.val = z := hi
    rw [← hiv,← horder i.val hile]
    exact r.getVert_mem_support _
  obtain ⟨i,hri,hip,hix⟩ := hindex x hx hxP
  obtain ⟨j,hrj,hjp,hjy⟩ := hindex y hy hyP
  have hqi : q.getVert (i-r.length) = x := by
    rw [hqo _ (by omega),Nat.add_sub_of_le (by omega : r.length ≤ i),walkCycleVertices_nat_le p (by omega),hix]
  have hqj : q.getVert (j-r.length) = y := by
    rw [hqo _ (by omega),Nat.add_sub_of_le (by omega : r.length ≤ j),walkCycleVertices_nat_le p (by omega),hjy]
  have hfree : ∀ z ∈ I.precolor.vertices,
      z ∉ cycleInterval (walkCycleVertices q) 1 (p.length-r.length-2) := by
    intro z hz hzarc
    obtain ⟨k,hkz,hkr⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hz)
    obtain ⟨l,hl,hlz⟩ := hzarc
    rw [walkCycleVertices_nat_le q (by omega : 1+l ≤ q.length),hqo (1+l) (by omega),
      walkCycleVertices_nat_le p (by omega : r.length+(1+l) ≤ p.length)] at hlz
    have heq : p.getVert k = p.getVert (r.length+(1+l)) :=
      (horder k hkr).symm.trans (hkz.trans hlz.symm)
    have hi := hp.getVert_injOn' (show k ≤ p.length-1 from by omega)
      (show r.length+(1+l) ≤ p.length-1 from by omega) heq
    omega
  have hxv : x ≠ v2 := fun h => hv (h ▸ hx)
  have huy : u ≠ y := fun h => hu (h.symm ▸ hy)
  have hxy : x ≠ y := by
    intro h
    exact neighbors_nonadjacent I.girth hux huv (h ▸ hvy.symm)
  have hNoAdj : ¬ G.Adj x y := by
    intro h
    exact huy (common_neighbor_unique I.girth hxv hux.symm huv.symm h hvy)
  have hij : i ≠ j := fun h => hxy (hix.symm.trans ((congrArg p.getVert h).trans hjy))
  have hfreeSub : ∀ s t : ℕ, s+2 ≤ t → t < p.length-r.length →
      ∀ z ∈ I.precolor.vertices, z ∉ cycleInterval (walkCycleVertices q) (s+1) (t-s-2) := by
    intro s t hst htp z hz hzarc
    obtain ⟨l,hl,hlz⟩ := hzarc
    apply hfree z hz
    refine ⟨s+l,by omega,?_⟩
    simpa only [Nat.add_assoc,Nat.add_left_comm s 1] using hlz
  apply hbad
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap : i+2 ≤ j := by
      by_contra h
      have hj : j=i+1 := by omega
      apply hNoAdj
      have h := p.adj_getVert_succ hip
      simpa only [← hj,hix,hjy] using h
    apply I.colourable_of_interior_three_path_free_subarc_one_short_endpoint hG q hq hqface hqroot
      (i-r.length) (j-r.length) (by omega) (by omega) u v2 hu hv
      (by rwa [hqi]) huv (by rwa [hqj]) (Or.inr (by rwa [hqj]))
      (hfreeSub _ _ (by omega) (by omega)) hsmall
  · have hgap : j+2 ≤ i := by
      by_contra h
      have hi : i=j+1 := by omega
      apply hNoAdj
      have h := (p.adj_getVert_succ hjp).symm
      simpa only [← hi,hix,hjy] using h
    apply I.colourable_of_interior_three_path_free_subarc_one_short_endpoint hG q hq hqface hqroot
      (j-r.length) (i-r.length) (by omega) (by omega) v2 u hv hu
      (by rwa [hqj]) huv.symm (by rwa [hqi]) (Or.inl (by rwa [hqj]))
      (hfreeSub _ _ (by omega) (by omega)) hsmall

/-- A free old short boundary list cannot be joined to any other boundary
vertex by a three-edge interior path in a smallest counterexample. Both the
mixed-prescription and the entirely free facial cases are proved internally. -/
theorem colourable_of_three_path_short_free_boundary_endpoint (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : OnOuterFace I.embedding I.outer x)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  by_cases hxP : x ∈ I.precolor.vertices
  · exact hbad (I.colourable_of_mixed_three_path_short_free_endpoint r hr hn hP hrpos
      x b u v2 hxP hb hbP hbShort hu hv hux huv hvb hsmall)
  have hrlen : 2 ≤ r.length := by
    by_contra h
    have hr1 : r.length=1 := by omega
    exact hbad (I.colourable_of_prescribed_edge r hr hn hP hr1 hsmall)
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.colourable_of_free_three_path_short_endpoint_on_native_face hG p hp hface hroot
      r hr hn hP hrlen horder hsmall u v2 x b hu hv hx hb hxP hbP hux huv hvb hbShort
  · have hm := mirror_onOuterFace_iff I.embedding I.outer
    exact I.mirror.colourable_of_free_three_path_short_endpoint_on_native_face hG p hp hface hroot
      r hr hn hP hrlen horder hsmall u v2 x b (fun h => hu ((hm u).1 h)) (fun h => hv ((hm v2).1 h))
      ((hm x).2 hx) ((hm b).2 hb) hxP hbP hux huv hvb hbShort

end Thomassen.BoundaryInstance
