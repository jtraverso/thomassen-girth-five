/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.LongPrescriptionReduction

/-! Three free boundary vertices can be deleted without an interior three-path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- In the alternating short-list branch, delete only the first three free
boundary vertices. Every original prescribed vertex is retained. This closes
all prescriptions on at most five vertices if the interior three-path between
the first and third deleted vertices is absent. -/
theorem colourable_of_alternating_free_path_without_interior_three_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hn5 : r.support.toFinset.card ≤ 5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj (p.getVert (p.length-1)) x → G.Adj x y → G.Adj y (p.getVert (p.length-3)) → False)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hlen : 5 ≤ p.length := by omega
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  let b := p.getVert (p.length-1)
  let d := p.getVert (p.length-2)
  let e := p.getVert (p.length-3)
  let g := p.getVert (p.length-4)
  have hfourthg : (I.lists g).card ≤ 2 := hfourth
  let A : Finset V := {b,d,e}
  have hAmem : ∀ x, x ∈ A ↔ x=b ∨ x=d ∨ x=e := by
    intro x; simp only [A,Finset.mem_insert,Finset.mem_singleton]
  have hne : ∀ i j : ℕ, i < p.length → j < p.length → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (by change i ≤ p.length-1; omega) (by change j ≤ p.length-1; omega) he)
  have hnotP : ∀ i, r.length < i → i < p.length → p.getVert i ∉ I.precolor.vertices := by
    intro i hri hip hx
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv _).1 hx)
    have he := hp.getVert_injOn' (show j ≤ p.length-1 from by omega) (show i ≤ p.length-1 from by omega)
      ((horder j hjl).symm.trans hj)
    omega
  have hbP : b ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have hdP : d ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have heP : e ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have haP : a ∈ I.precolor.vertices := (hPv a).2 r.start_mem_support
  have hAP : ∀ x ∈ I.precolor.vertices, x ∉ A := by
    intro x hx hxA
    rcases (hAmem x).1 hxA with h | h | h
    · exact hbP (h ▸ hx)
    · exact hdP (h ▸ hx)
    · exact heP (h ▸ hx)
  have hbd : G.Adj b d := by
    simpa only [show p.length-2+1=p.length-1 by omega] using (p.adj_getVert_succ (by omega : p.length-2 < p.length)).symm
  have hde : G.Adj d e := by
    simpa only [show p.length-3+1=p.length-2 by omega] using (p.adj_getVert_succ (by omega : p.length-3 < p.length)).symm
  have hba : G.Adj b a := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),Walk.getVert_length] using p.adj_getVert_succ (by omega : p.length-1 < p.length)
  have heg : G.Adj e g := by
    simpa only [show p.length-4+1=p.length-3 by omega] using (p.adj_getVert_succ (by omega : p.length-4 < p.length)).symm
  have hbe : b ≠ e := hne _ _ (by omega) (by omega) (by omega)
  have hbdNe : b ≠ d := hne _ _ (by omega) (by omega) (by omega)
  have hdeNe : d ≠ e := hne _ _ (by omega) (by omega) (by omega)
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact I.short_not_adj_precolored hbP haP (by omega) hba
  have h3e : 3 ≤ (I.lists e).card := by
    by_contra h
    exact heP (I.precolor.endpoints_of_mem_edges (I.short_edges heg (by omega) hfourth)).1
  obtain ⟨ce,hce,hceg⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := I.lists g) (t := I.lists e) (by omega)
  obtain ⟨cd,hcd,hcde⟩ := Finset.exists_mem_ne (s := I.lists d)
    (by have := I.outside_precolor_list_ge_two hdP; omega) ce
  obtain ⟨cb,hcb,hcbN⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({I.prescribed a,cd} : Finset C)) (t := I.lists b) (Finset.card_le_two.trans_lt (by omega))
  have hcba : cb ≠ I.prescribed a := fun h => hcbN (Finset.mem_insert.2 (Or.inl h))
  have hcbd : cb ≠ cd := fun h => hcbN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let f : V → C := fun x => if x=b then cb else if x=d then cd else ce
  have hfb : f b=cb := by simp only [f,ite_true]
  have hfd : f d=cd := by simp only [f,ite_eq_right hbdNe.symm,ite_true]
  have hfe : f e=ce := by simp only [f,ite_eq_right hbe.symm,ite_eq_right hdeNe.symm]
  have hfA : ∀ x ∈ A, f x ∈ I.lists x := by
    intro x hx
    rcases (hAmem x).1 hx with h | h | h
    · rw [h,hfb]; exact hcb
    · rw [h,hfd]; exact hcd
    · rw [h,hfe]; exact hce
  have hproperA : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y := by
    intro x hx y hy hxy
    have hnoBE : ¬ G.Adj b e := neighbors_nonadjacent I.girth hbd.symm hde
    rcases (hAmem x).1 hx with hx | hx | hx <;> rcases (hAmem y).1 hy with hy | hy | hy
    all_goals rw [hx,hy] at hxy ⊢
    · exact (hxy.ne rfl).elim
    · rw [hfb,hfd]; exact hcbd
    · exact (hnoBE hxy).elim
    · rw [hfd,hfb]; exact hcbd.symm
    · exact (hxy.ne rfl).elim
    · rw [hfd,hfe]; exact hcde
    · exact (hnoBE hxy.symm).elim
    · rw [hfe,hfd]; exact hcde.symm
    · exact (hxy.ne rfl).elim
  have hfFace : ∀ k, OnOuterFace I.embedding I.outer (p.getVert k) := fun k => (hverts _).1 (p.getVert_mem_support k)
  have hOldUnchanged : ∀ x, x ∉ A → (I.lists x).card ≤ 2 → residual G I.lists A f x = I.lists x := by
    intro x hx hxShort
    apply Finset.Subset.antisymm (residual_subset G I.lists A f x)
    intro col hcol
    apply (mem_residual_iff I.lists A f x col).2
    refine ⟨hcol,?_⟩
    intro z hz hxz
    have hxFace : OnOuterFace I.embedding I.outer x := by
      by_contra h
      have h3 := I.interior_lists x h
      omega
    have hxSupport := (hverts x).2 hxFace
    rcases (hAmem z).1 hz with hzb | hzd | hze
    · have hbx : G.Adj b x := hzb ▸ hxz.symm
      rcases chordless_native_cycle_last_neighbours p hp hch hxSupport hbx with hxa | hxd
      · rw [hzb,hfb]
        have hxList : I.lists x={I.prescribed a} := by rw [hxa,I.singleton a haP]
        have hcola : col=I.prescribed a := Finset.mem_singleton.1 (hxList ▸ hcol)
        exact hcola ▸ hcba.symm
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl hxd)))).elim
    · have hdx : G.Adj d x := hzd ▸ hxz.symm
      rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) hxSupport hdx with hxe | hxb
      · exact (hx ((hAmem x).2 (Or.inr (Or.inr (by simpa only [show p.length-2-1=p.length-3 by omega] using hxe))))).elim
      · exact (hx ((hAmem x).2 (Or.inl (by simpa only [show p.length-2+1=p.length-1 by omega] using hxb)))).elim
    · have hex : G.Adj e x := hze ▸ hxz.symm
      rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) hxSupport hex with hxg | hxd
      · have hxg' : x=g := by simpa only [show p.length-3-1=p.length-4 by omega] using hxg
        rw [hze,hfe]
        exact fun h => hceg (by rw [← hxg']; exact h ▸ hcol)
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl (by simpa only [show p.length-3+1=p.length-2 by omega] using hxd))))).elim
  have hPcolour : ∀ x ∈ I.precolor.vertices, residual G I.lists A f x = {I.prescribed x} := by
    intro x hx
    rw [hOldUnchanged x (hAP x hx) (by rw [I.singleton x hx,Finset.card_singleton]; omega),I.singleton x hx]
  have hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f x).card := by
    intro x hx hxP
    by_cases hs : (I.lists x).card ≤ 2
    · rw [hOldUnchanged x hx hs]; exact I.outside_precolor_list_ge_two hxP
    · exact residual_two_edge_path_card_ge_two I.girth hbd hde hbe
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inl h)))) I.lists f (by omega)
  have hNewOffFace : ∀ x, x ∉ A → 3 ≤ (I.lists x).card → (∃ z ∈ A, G.Adj z x) →
      ¬ OnOuterFace I.embedding I.outer x := by
    intro x hx hx3 ⟨z,hz,hzx⟩ hxFace
    have hxSupport := (hverts x).2 hxFace
    have hxa : x ≠ a := by
      intro h
      have h1 : (I.lists x).card=1 := by rw [h,I.singleton a haP,Finset.card_singleton]
      omega
    have hxg : x ≠ g := fun h => by have h2 : (I.lists x).card ≤ 2 := h.symm ▸ hfourth; omega
    rcases (hAmem z).1 hz with hzb | hzd | hze
    · rcases chordless_native_cycle_last_neighbours p hp hch hxSupport (by change G.Adj b x; rw [← hzb]; exact hzx) with h | h
      · exact hxa h
      · exact hx ((hAmem x).2 (Or.inr (Or.inl h)))
    · rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) hxSupport (by change G.Adj d x; rw [← hzd]; exact hzx) with h | h
      · exact hx ((hAmem x).2 (Or.inr (Or.inr (by simpa only [show p.length-2-1=p.length-3 by omega] using h))))
      · exact hx ((hAmem x).2 (Or.inl (by simpa only [show p.length-2+1=p.length-1 by omega] using h)))
    · rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) hxSupport (by change G.Adj e x; rw [← hze]; exact hzx) with h | h
      · exact hxg (by simpa only [show p.length-3-1=p.length-4 by omega] using h)
      · exact hx ((hAmem x).2 (Or.inr (Or.inl (by simpa only [show p.length-3+1=p.length-2 by omega] using h))))
  have hNoOld : ∀ x, x ∉ A → 3 ≤ (I.lists x).card → (∃ z ∈ A, G.Adj z x) →
      ∀ y, y ∉ A → (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hx3 hxN y hy hyShort hxy
    have hxOff := hNewOffFace x hx hx3 hxN
    have hyFace : OnOuterFace I.embedding I.outer y := by
      by_contra h
      have h3 := I.interior_lists y h
      omega
    obtain ⟨z,hz,hzx⟩ := hxN
    have hzFace : OnOuterFace I.embedding I.outer z := by
      rcases (hAmem z).1 hz with h | h | h
      · exact h ▸ hfFace _
      · exact h ▸ hfFace _
      · exact h ▸ hfFace _
    have he := I.interior_boundary_neighbour_unique_of_short_prescription r hr hn hP hrpos hn5 hbad hsmall
      x z y hxOff hzFace hyFace hzx.symm hxy
    exact hy (he ▸ hz)
  have hNew : ∀ x, 3 ≤ (I.lists x).card → (residual G I.lists A f x).card ≤ 2 → ∃ z ∈ A, G.Adj z x :=
    fun x hx hs => short_residual_neighbor I.lists A f x hx hs
  have hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 →
      x ∈ I.precolor.vertices ∧ y ∈ I.precolor.vertices := by
    intro x hx y hy hxy hxs hys
    by_cases hxOld : (I.lists x).card ≤ 2 <;> by_cases hyOld : (I.lists y).card ≤ 2
    · exact I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)
    · exact (hNoOld y hy (by omega) (hNew y (by omega) hys) x hx hxOld hxy.symm).elim
    · exact (hNoOld x hx (by omega) (hNew x (by omega) hxs) y hy hyOld hxy).elim
    · have hxN := hNew x (by omega) hxs
      have hyN := hNew y (by omega) hys
      have hxOff := hNewOffFace x hx (by omega) hxN
      have hyOff := hNewOffFace y hy (by omega) hyN
      rcases short_residual_two_edge_path_adjacent I.girth hbd hde hx hy I.lists f
        (by omega) (by omega) hxs hys hxy with h | h
      · exact (hNoThree x y hxOff hyOff h.1 hxy h.2.symm).elim
      · exact (hNoThree y x hyOff hxOff h.2 hxy.symm h.1.symm).elim
  have hAconn : ConnSet G (↑A : Set V) := by
    have h := ((connSet_singleton G b).insert_adj (Set.mem_singleton b) hbd.symm).insert_adj
      (Set.mem_insert d {b}) hde.symm
    convert h using 1
    ext x
    simp only [A,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  obtain ⟨q,hq,_,_,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot (p.length-1) (by omega)
  apply hbad
  apply I.colourable_of_connected_residual_prescription hG q hq hqface hqroot
    (fun x hx => (native_facial_cycle_support_iff I.embedding I.outer q hq hqface hqroot x).2 hx)
    A ((hAmem b).2 (Or.inl rfl)) hAconn f hfA hproperA {x | x ∈ I.precolor.vertices}
    (by
      have heq : {x | x ∈ I.precolor.vertices} = {x | x ∈ r.support} := by ext x; exact hPv x
      rw [heq]; exact walk_support_connSet r)
    hAP (fun x hx => Or.inl (I.on_outer x hx)) ?_
    (fun x hx => by rw [hPcolour x hx,Finset.card_singleton]; omega)
    I.prescribed (fun x hx => by rw [hPcolour x hx]; exact Finset.mem_singleton_self _)
    (fun x hx y hy hxy => I.proper_on_precolored_vertices hx hy hxy) hTwo hShort hsmall
  intro x y w hw hs
  have hsub : w.support.toFinset ⊆ I.precolor.vertices := fun z hz => hs z (List.mem_toFinset.1 hz)
  have hc := Finset.card_le_card hsub
  have hPcard := I.precolor.card_vertices_le
  rw [List.toFinset_card_of_nodup hw.support_nodup,Walk.length_support] at hc
  omega

end Thomassen.BoundaryInstance
