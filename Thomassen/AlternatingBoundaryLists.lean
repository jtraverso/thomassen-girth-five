/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortFaceCompletion

/-! Closing the alternating short-list boundary case by compatible precolouring. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Exact native rebasing preserves the entire support, including the root. -/
lemma native_rebase_support_eq {a b : V} (p : G.Walk a a) (hp : p.IsCycle) (q : G.Walk b b)
    (s : ℕ) (hlen : q.length = p.length)
    (horder : ∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s+i : ℕ) : ZMod p.length)) :
    ∀ x, x ∈ q.support ↔ x ∈ p.support := by
  let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    rw [horder i (by omega)] at hix
    exact hix ▸ p.getVert_mem_support _
  · intro hx
    obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    let i := (((j : ZMod p.length)-(s : ZMod p.length))).val
    have hi : i < p.length := ZMod.val_lt _
    apply Walk.mem_support_iff_exists_getVert.2
    refine ⟨i, ?_, by omega⟩
    rw [horder i hi.le, Nat.cast_add, show (i : ZMod p.length) = (j : ZMod p.length)-(s : ZMod p.length) from ZMod.natCast_zmod_val _]
    rw [show (s : ZMod p.length) + ((j : ZMod p.length)-(s : ZMod p.length)) = j by ring,
      walkCycleVertices_nat_le p hj]
    exact hjx

namespace BoundaryInstance
variable {C : Type v} [Fintype V] {a : V}

/-- With the first facial edge prescribed, a short fourth backward list is
resolved by precolouring a five-vertex native boundary path. The only enlarged
list gets the adjacent prescribed colour as its extra colour, so every resulting
colouring restores that original list. Only the strict main induction is used. -/
theorem colourable_of_prescribed_edge_short_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : 7 ≤ p.length) (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  let b := p.getVert (p.length-1)
  let d := p.getVert (p.length-2)
  let e := p.getVert (p.length-3)
  let w := p.getVert (p.length-4)
  let g := p.getVert (p.length-5)
  let t := p.getVert 1
  have hfourthw : (I.lists w).card ≤ 2 := hfourth
  have hne : ∀ i j, i < p.length → j < p.length → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (show i ≤ p.length-1 from by omega) (show j ≤ p.length-1 from by omega) he)
  have hna : ∀ i, 0 < i → i < p.length → p.getVert i ≠ a := by
    intro i hi hil
    simpa only [Walk.getVert_zero] using hne i 0 hil (by omega) (by omega)
  have haP := (hP a).2 (Or.inl rfl)
  have htP := (hP t).2 (Or.inr rfl)
  have hnotP : ∀ i, 2 ≤ i → i < p.length → p.getVert i ∉ I.precolor.vertices := by
    intro i hi hil hx
    exact ((hP _).1 hx).elim (hna i (by omega) hil) (hne i 1 hil (by omega) (by omega))
  have hf : ∀ i, OnOuterFace I.embedding I.outer (p.getVert i) := fun i =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support i)
  have hab : G.Adj a b := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length), Walk.getVert_length] using
      (p.adj_getVert_succ (by omega : p.length-1 < p.length)).symm
  have hdb : G.Adj d b := by
    simpa only [show p.length-2+1 = p.length-1 by omega] using p.adj_getVert_succ (by omega : p.length-2 < p.length)
  have hed : G.Adj e d := by
    simpa only [show p.length-3+1 = p.length-2 by omega] using p.adj_getVert_succ (by omega : p.length-3 < p.length)
  have hwe : G.Adj w e := by
    simpa only [show p.length-4+1 = p.length-3 by omega] using p.adj_getVert_succ (by omega : p.length-4 < p.length)
  have hgw : G.Adj g w := by
    simpa only [show p.length-5+1 = p.length-4 by omega] using p.adj_getVert_succ (by omega : p.length-5 < p.length)
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact I.short_not_adj_precolored (x := b) (y := a) (hnotP _ (by omega) (by omega)) haP (by omega) hab.symm
  have h3e : 3 ≤ (I.lists e).card := by
    by_contra h
    exact hnotP (p.length-4) (by omega) (by omega)
      (I.precolor.endpoints_of_mem_edges (I.short_edges hwe hfourth (by omega))).1
  have h3g : 3 ≤ (I.lists g).card := by
    by_contra h
    exact hnotP (p.length-4) (by omega) (by omega)
      (I.precolor.endpoints_of_mem_edges (I.short_edges hgw (by omega) hfourth)).2
  have hw2 : (I.lists w).card = 2 := by
    have h2 : 2 ≤ (I.lists w).card := I.outside_precolor_list_ge_two (hnotP (p.length-4) (by omega) (by omega))
    omega
  obtain ⟨ce, hce, hcew⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := I.lists w) (t := I.lists e) (by omega)
  obtain ⟨cd, hcd, hcde⟩ := Finset.exists_mem_ne (s := I.lists d)
    (by have h2 : 2 ≤ (I.lists d).card := I.outside_precolor_list_ge_two (hnotP (p.length-2) (by omega) (by omega)); omega) ce
  obtain ⟨cb, hcb, hcba, hcbd⟩ : ∃ c ∈ I.lists b, c ≠ I.prescribed a ∧ c ≠ cd := by
    have hc : ({I.prescribed a,cd} : Finset C).card < (I.lists b).card := Finset.card_le_two.trans_lt (by omega)
    obtain ⟨c, hcL, hcN⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hn : c ≠ I.prescribed a ∧ c ≠ cd := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hcN
    exact ⟨c, hcL, hn⟩
  obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot (p.length-3) (by omega)
  have hq0 : q.getVert 0 = e := Walk.getVert_zero q
  have hq1 : q.getVert 1 = d := by rw [hqo 1 (by omega), show p.length-3+1 = p.length-2 by omega, walkCycleVertices_nat_le p (by omega)]
  have hq2 : q.getVert 2 = b := by rw [hqo 2 (by omega), show p.length-3+2 = p.length-1 by omega, walkCycleVertices_nat_le p (by omega)]
  have hq3 : q.getVert 3 = a := by
    rw [hqo 3 (by omega), Nat.sub_add_cancel (by omega : 3 ≤ p.length), ZMod.natCast_self]
    simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hq4 : q.getVert 4 = t := by
    rw [hqo 4 (by omega), show p.length-3+4 = p.length+1 by omega, Nat.cast_add, ZMod.natCast_self, zero_add]
    exact walkCycleVertices_nat_le p (by omega)
  have hqg : q.getVert (q.length-2) = g := by
    rw [hql, hqo (p.length-2) (by omega), show p.length-3+(p.length-2) = p.length+(p.length-5) by omega,
      Nat.cast_add, ZMod.natCast_self, zero_add, walkCycleVertices_nat_le p (by omega)]
  let r : G.Walk e t := (q.take 4).copy rfl hq4
  have hr : r.IsPath := (Walk.isPath_copy _ _ _).2 (hq.isPath_take (by omega))
  have hrl : r.length = 4 := by simp only [r, Walk.length_copy, Walk.take_length, Nat.min_eq_left (by omega : 4 ≤ q.length)]
  have hro : ∀ i ≤ 4, r.getVert i = q.getVert i := by
    intro i hi
    simp only [r, Walk.getVert_copy, Walk.take_getVert, Nat.min_eq_right hi]
  have hRv : ∀ x, x ∈ r.support ↔ x = e ∨ x = d ∨ x = b ∨ x = a ∨ x = t := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hix.symm.trans ((hro 0 (by omega)).trans hq0))
      · exact Or.inr (Or.inl (hix.symm.trans ((hro 1 (by omega)).trans hq1)))
      · exact Or.inr (Or.inr (Or.inl (hix.symm.trans ((hro 2 (by omega)).trans hq2))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hix.symm.trans ((hro 3 (by omega)).trans hq3)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hix.symm.trans ((hro 4 (by omega)).trans hq4)))))
    · rintro (h | h | h | h | h)
      all_goals apply Walk.mem_support_iff_exists_getVert.2
      · exact ⟨0, (hro 0 (by omega)).trans (hq0.trans h.symm), by omega⟩
      · exact ⟨1, (hro 1 (by omega)).trans (hq1.trans h.symm), by omega⟩
      · exact ⟨2, (hro 2 (by omega)).trans (hq2.trans h.symm), by omega⟩
      · exact ⟨3, (hro 3 (by omega)).trans (hq3.trans h.symm), by omega⟩
      · exact ⟨4, (hro 4 (by omega)).trans (hq4.trans h.symm), by omega⟩
  have hRout : ∀ x ∈ r.support, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases (hRv x).1 hx with he | hd | hb | ha | ht
    · exact he ▸ hf _
    · exact hd ▸ hf _
    · exact hb ▸ hf _
    · exact ha ▸ I.on_outer a haP
    · exact ht ▸ I.on_outer t htP
  have hOldR : ∀ x ∈ I.precolor.vertices, x ∈ r.support := by
    intro x hx
    rcases (hP x).1 hx with ha | ht
    · exact (hRv x).2 (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact (hRv x).2 (Or.inr (Or.inr (Or.inr (Or.inr ht))))
  have hwR : w ∉ r.support := by
    intro h
    rcases (hRv w).1 h with h | h | h | h | h
    · exact hne (p.length-4) (p.length-3) (by omega) (by omega) (by omega) h
    · exact hne (p.length-4) (p.length-2) (by omega) (by omega) (by omega) h
    · exact hne (p.length-4) (p.length-1) (by omega) (by omega) (by omega) h
    · exact hna (p.length-4) (by omega) (by omega) h
    · exact hne (p.length-4) 1 (by omega) (by omega) (by omega) h
  have hgR : g ∉ r.support := by
    intro h
    rcases (hRv g).1 h with h | h | h | h | h
    · exact hne (p.length-5) (p.length-3) (by omega) (by omega) (by omega) h
    · exact hne (p.length-5) (p.length-2) (by omega) (by omega) (by omega) h
    · exact hne (p.length-5) (p.length-1) (by omega) (by omega) (by omega) h
    · exact hna (p.length-5) (by omega) (by omega) h
    · exact hne (p.length-5) 1 (by omega) (by omega) (by omega) h
  have hgwne : g ≠ w := hne (p.length-5) (p.length-4) (by omega) (by omega) (by omega)
  have hnoends : ¬ G.Adj e t := by
    intro het
    rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) (p.getVert_mem_support 1) het with h | h
    · exact hne 1 (p.length-4) (by omega) (by omega) (by omega) (by simpa only [show p.length-3-1 = p.length-4 by omega] using h)
    · exact hne 1 (p.length-2) (by omega) (by omega) (by omega) (by simpa only [show p.length-3+1 = p.length-2 by omega] using h)
  have hrch := four_edge_path_isChordless I.girth r hr (by omega) hnoends
  let F : V → C := fun x => if x = e then ce else if x = d then cd else if x = b then cb else I.prescribed x
  have hFe : F e = ce := by simp only [F, ite_true]
  have hFd : F d = cd := by simp only [F, ite_eq_right (show d ≠ e from hne (p.length-2) (p.length-3) (by omega) (by omega) (by omega)), ite_true]
  have hFb : F b = cb := by simp only [F, ite_eq_right (show b ≠ e from hne (p.length-1) (p.length-3) (by omega) (by omega) (by omega)), ite_eq_right (show b ≠ d from hne (p.length-1) (p.length-2) (by omega) (by omega) (by omega)), ite_true]
  have hFa : F a = I.prescribed a := by simp only [F, ite_eq_right (show a ≠ e from (hna (p.length-3) (by omega) (by omega)).symm), ite_eq_right (show a ≠ d from (hna (p.length-2) (by omega) (by omega)).symm), ite_eq_right (show a ≠ b from (hna (p.length-1) (by omega) (by omega)).symm)]
  have hFt : F t = I.prescribed t := by simp only [F, ite_eq_right (show t ≠ e from hne 1 (p.length-3) (by omega) (by omega) (by omega)), ite_eq_right (show t ≠ d from hne 1 (p.length-2) (by omega) (by omega) (by omega)), ite_eq_right (show t ≠ b from hne 1 (p.length-1) (by omega) (by omega) (by omega))]
  have hFR : ∀ x ∈ r.support, F x ∈ I.lists x := by
    intro x hx
    rcases (hRv x).1 hx with hx | hx | hx | hx | hx
    · rw [hx, hFe]; exact hce
    · rw [hx, hFd]; exact hcd
    · rw [hx, hFb]; exact hcb
    · rw [hx, hFa, I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [hx, hFt, I.singleton t htP]; exact Finset.mem_singleton_self _
  have hFedge : ∀ i, i < r.length → F (r.getVert i) ≠ F (r.getVert (i+1)) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · simpa only [hro 0 (by omega), hro 1 (by omega), hq0, hq1, hFe, hFd] using hcde.symm
    · simpa only [hro 1 (by omega), hro 2 (by omega), hq1, hq2, hFd, hFb] using hcbd.symm
    · simpa only [hro 2 (by omega), hro 3 (by omega), hq2, hq3, hFb, hFa] using hcba
    · simpa only [hro 3 (by omega), hro 4 (by omega), hq3, hq4, hFa, hFt] using I.proper_on_precolored_vertices haP htP (by simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length))
  have hAvoid : ∀ x, x ∉ r.support → x ≠ w → (I.lists x).card ≤ 2 → ∀ u ∈ r.support, ¬ G.Adj x u := by
    intro x hx hxw hxs u hu hxu
    have hxf : OnOuterFace I.embedding I.outer x := by
      by_contra h
      have := I.interior_lists x h
      omega
    have hxp := hExact x hxf
    rcases (hRv u).1 hu with hue | hud | hub | hua | hut
    · rw [hue] at hxu
      rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) hxp hxu.symm with h | h
      · exact hxw (by simpa only [show p.length-3-1 = p.length-4 by omega] using h)
      · exact hx ((hRv x).2 (Or.inr (Or.inl (by simpa only [show p.length-3+1 = p.length-2 by omega] using h))))
    · rw [hud] at hxu
      rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) hxp hxu.symm with h | h
      · exact hx ((hRv x).2 (Or.inl (by simpa only [show p.length-2-1 = p.length-3 by omega] using h)))
      · exact hx ((hRv x).2 (Or.inr (Or.inr (Or.inl (by simpa only [show p.length-2+1 = p.length-1 by omega] using h)))))
    · rw [hub] at hxu
      rcases chordless_native_cycle_last_neighbours p hp hch hxp hxu.symm with h | h
      · exact hx ((hRv x).2 (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact hx ((hRv x).2 (Or.inr (Or.inl h)))
    · exact I.short_not_adj_precolored (fun h => hx (hOldR x h)) haP hxs (by rwa [hua] at hxu)
    · exact I.short_not_adj_precolored (fun h => hx (hOldR x h)) htP hxs (by rwa [hut] at hxu)
  have hrbound : r.support.toFinset.card ≤ 6 := by
    calc _ ≤ r.support.length := List.toFinset_card_le _
         _ = r.length+1 := Walk.length_support _
         _ ≤ 6 := by omega
  let L : V → Finset C := fun x => if x ∈ r.support then {F x} else if x = w then insert ce (I.lists x) else I.lists x
  have hLw : L w = insert ce (I.lists w) := by simp only [L, ite_eq_right hwR, ite_true]
  have hLw3 : 3 ≤ (L w).card := by rw [hLw, Finset.card_insert_of_notMem hcew, hw2]
  let J : BoundaryInstance G C := {
    girth := I.girth
    embedding := I.embedding
    outer := I.outer
    precolor := .path r hr hrbound
    lists := L
    prescribed := F
    on_outer := fun x hx => hRout x (List.mem_toFinset.1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left (List.mem_toFinset.1 hx)]
    proper_precolor := by
      intro x y he
      obtain ⟨i, hi, hxy⟩ := r.mk_mem_edges_iff_exists.1 (List.mem_toFinset.1 he)
      rcases Sym2.eq_iff.1 hxy with h | h
      · simpa only [h.1, h.2] using hFedge i hi
      · simpa only [h.1, h.2] using (hFedge i hi).symm
    boundary_lists := by
      intro x _ hx
      have hxR : x ∉ r.support := fun h => hx (List.mem_toFinset.2 h)
      by_cases hxw : x = w
      · rw [hxw]; omega
      · simpa only [L, ite_eq_right hxR, ite_eq_right hxw] using I.outside_precolor_list_ge_two (fun h => hxR (hOldR x h))
    interior_lists := by
      intro x hx
      have hxR : x ∉ r.support := fun h => hx (hRout x h)
      have hxw : x ≠ w := fun h => hx (h ▸ hf (p.length-4))
      simpa only [L, ite_eq_right hxR, ite_eq_right hxw] using I.interior_lists x hx
    short_edges := by
      intro x y hxy hx hy
      have hshort : ∀ z, (L z).card ≤ 2 → z ∉ r.support → z ≠ w ∧ (I.lists z).card ≤ 2 := by
        intro z hz hzR
        have hzw : z ≠ w := fun h => by rw [h] at hz; omega
        exact ⟨hzw, by simpa only [L, ite_eq_right hzR, ite_eq_right hzw] using hz⟩
      by_cases hxR : x ∈ r.support <;> by_cases hyR : y ∈ r.support
      · exact List.mem_toFinset.2 (hrch.mem_edges hxR hyR hxy)
      · obtain ⟨hyw, hyOld⟩ := hshort y hy hyR
        exact (hAvoid y hyR hyw hyOld x hxR hxy.symm).elim
      · obtain ⟨hxw, hxOld⟩ := hshort x hx hxR
        exact (hAvoid x hxR hxw hxOld y hyR hxy).elim
      · obtain ⟨_, hxOld⟩ := hshort x hx hxR
        obtain ⟨_, hyOld⟩ := hshort y hy hyR
        exact (hxR (hOldR x (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)).1)).elim }
  have hExactq : ∀ x, OnOuterFace J.embedding J.outer x → x ∈ q.support := by
    intro x hx
    exact (native_rebase_support_eq p hp q (p.length-3) hql hqo x).2 (hExact x hx)
  have hfirstq : q.getVert 1 ∈ J.precolor.vertices := by
    change q.getVert 1 ∈ r.support.toFinset
    exact List.mem_toFinset.2 (by rw [hq1]; exact (hRv d).2 (Or.inr (Or.inl rfl)))
  have hsecondq : 3 ≤ (J.lists (q.getVert (q.length-2))).card := by
    change 3 ≤ (L (q.getVert (q.length-2))).card
    rw [hqg]
    simpa only [L, ite_eq_right hgR, ite_eq_right hgwne] using h3g
  obtain ⟨c, hc⟩ := J.colourable_of_good_second_boundary_list_all_prescriptions hG q hq hqf hqr hExactq r hr hrbound rfl hfirstq hsecondq hsmall
  have hceFixed : c e = ce := by
    have heR := (hRv e).2 (Or.inl rfl)
    have he : c e ∈ L e := hc e
    simpa only [L, ite_eq_left heR, hFe, Finset.mem_singleton] using he
  apply hbad
  refine ⟨c, ?_⟩
  intro x
  have hx : c x ∈ L x := hc x
  by_cases hxR : x ∈ r.support
  · have he : c x = F x := Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hxR] using hx)
    rw [he]; exact hFR x hxR
  by_cases hxw : x = w
  · have hcw : c w ∈ insert ce (I.lists w) := by simpa only [hxw, hLw] using hx
    rcases Finset.mem_insert.1 hcw with he | he
    · exact ((c.valid hwe) (he.trans hceFixed.symm)).elim
    · simpa only [hxw] using he
  · simpa only [L, ite_eq_right hxR, ite_eq_right hxw] using hx


/-- The whole short-second-list branch for a prescribed edge is closed.
The good-fourth case uses the checked deletion; the alternating case uses
compatible five-vertex precolouring and restores its one enlarged list. -/
theorem colourable_of_prescribed_edge_short_second (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : 6 ≤ p.length) (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card
  · exact I.colourable_of_prescribed_edge_short_second_good_fourth hG p hp hface hroot hExact hP hlen hsecond hfourth hsmall
  by_cases hseven : 7 ≤ p.length
  · exact I.colourable_of_prescribed_edge_short_fourth hG p hp hface hroot hExact hP hseven (by omega) hsmall
  have hsix : p.length = 6 := by omega
  have hxP : p.getVert 2 ∉ I.precolor.vertices := by
    intro h
    rcases (hP _).1 h with h2a | h21
    · have hi := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from Nat.zero_le _)
        (by simpa only [Walk.getVert_zero] using h2a)
      omega
    · have hi := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 1 ≤ p.length-1 from by omega) h21
      omega
  have hshort2 : (I.lists (p.getVert 2)).card ≤ 2 := by
    have h4 : (I.lists (p.getVert (p.length-4))).card ≤ 2 := by omega
    simpa only [hsix, show 6-4 = 2 by omega] using h4
  exact (I.short_not_adj_precolored hxP ((hP _).2 (Or.inr rfl)) hshort2
    (by simpa only [show 1+1 = 2 by omega] using (p.adj_getVert_succ (by omega : 1 < p.length)).symm)).elim

/-- Every actual native facial case with an edge prescribed is closed under
the strict main induction. This combines the five-vertex face, good-second-list
branch and the complete short-second-list branch. -/
theorem colourable_of_prescribed_edge_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  by_cases hsecond : 3 ≤ (I.lists (p.getVert (p.length-2))).card
  · exact hbad (I.colourable_of_good_second_boundary_list_all_prescriptions hG p hp hface hroot hExact r hr hn hP hfirst hsecond hsmall)
  have horder := I.prescribed_path_forward_of_first_face_vertex hG p hp hface hExact r hr hn hP hfirst hbad hsmall
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z = a ∨ z = p.getVert 1 := by
    intro z
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset]
    constructor
    · intro hz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact Or.inl (by simpa only [Walk.getVert_zero] using hiz.symm)
      · exact Or.inr (hiz.symm.trans (horder 1 (by omega)))
    · rintro (hza | hz1)
      · exact hza ▸ r.start_mem_support
      · exact hz1 ▸ (horder 1 (by omega) ▸ r.getVert_mem_support 1)
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth a p hp
  by_cases hfive : p.length = 5
  · exact hbad (I.colourable_of_prescribed_edge_five_vertex_face hG p hp hface hroot hExact hPv hfive hsmall)
  · exact hbad (I.colourable_of_prescribed_edge_short_second hG p hp hface hroot hExact hPv (by omega) (by omega) hsmall)

end BoundaryInstance
end Thomassen
