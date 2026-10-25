/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryPairClassification

/-! The good-fourth deletion for all six permitted prescribed vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- Delete the initial prescribed vertex and the first two backward free
boundary vertices. A short second list and a three-list at the fourth suffice
for every nontrivial original prescribed path on at most six vertices
when the backward six-vertex two-path exception is absent. -/
theorem colourable_of_path_short_second_good_fourth_without_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    {t0 : V} (r : G.Walk a t0) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hNoException : ∀ z, ¬ OnOuterFace I.embedding I.outer z →
      G.Adj z (p.getVert (p.length-1)) → ¬ G.Adj z (r.getVert 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hlen : 6 ≤ p.length := by
    by_contra h
    have hp5 : p.length=5 := by omega
    have h1P : p.getVert 1 ∈ I.precolor.vertices := by
      rw [← horder 1 (by omega)]
      exact (hPv _).2 (r.getVert_mem_support 1)
    have h3 : 3 ≤ (I.lists (p.getVert 1)).card := by simpa only [hp5] using hfourth
    rw [I.singleton _ h1P,Finset.card_singleton] at h3
    omega
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  let b := p.getVert (p.length-1)
  let d := p.getVert (p.length-2)
  let e := p.getVert (p.length-3)
  let t := p.getVert 1
  let A : Finset V := {a,b,d}
  have hAmem : ∀ x, x ∈ A ↔ x = a ∨ x = b ∨ x = d := by intro x; simp only [A, Finset.mem_insert, Finset.mem_singleton]
  have hinj : ∀ i j, i < p.length → j < p.length → p.getVert i = p.getVert j → i = j := by
    intro i j hi hj he
    exact hp.getVert_injOn' (show i ≤ p.length-1 from by omega) (show j ≤ p.length-1 from by omega) he
  have hba : b ≠ a := by intro h; have := hinj (p.length-1) 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have hda : d ≠ a := by intro h; have := hinj (p.length-2) 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have hdb : d ≠ b := by intro h; have := hinj (p.length-2) (p.length-1) (by omega) (by omega) h; omega
  have hta : t ≠ a := by intro h; have := hinj 1 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have htb : t ≠ b := by intro h; have := hinj 1 (p.length-1) (by omega) (by omega) h; omega
  have htd : t ≠ d := by intro h; have := hinj 1 (p.length-2) (by omega) (by omega) h; omega
  have htA : t ∉ A := by simpa only [hAmem, not_or] using ⟨hta, htb, htd⟩
  have hnotP : ∀ k, r.length < k → k < p.length → p.getVert k ∉ I.precolor.vertices := by
    intro k hrk hkp hkpP
    obtain ⟨l,hl,hll⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv _).1 hkpP)
    have he := hinj l k (by omega) hkp ((horder l hll).symm.trans hl)
    omega
  have hbP : b ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have hdP : d ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have haP := (hPv a).2 r.start_mem_support
  have htP : t ∈ I.precolor.vertices := by
    rw [show t=r.getVert 1 from (horder 1 (by omega)).symm]
    exact (hPv _).2 (r.getVert_mem_support 1)
  have hf : ∀ i, OnOuterFace I.embedding I.outer (p.getVert i) := fun i =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support i)
  have hab : G.Adj a b := by
    have h := p.adj_getVert_succ (by omega : p.length-1 < p.length)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length), Walk.getVert_length] using h.symm
  have hbd : G.Adj b d := by
    have h := p.adj_getVert_succ (by omega : p.length-2 < p.length)
    simpa only [show p.length-2+1 = p.length-1 by omega] using h.symm
  have had : ¬ G.Adj a d := neighbors_nonadjacent I.girth hab.symm hbd
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact I.short_not_adj_precolored hbP haP (by omega) hab.symm
  have hAface : ∀ x ∈ A, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases (hAmem x).1 hx with rfl | rfl | rfl
    · simpa only [Walk.getVert_zero] using hf 0
    · exact hf _
    · exact hf _
  have hNewFace : ∀ x, x ∉ A → OnOuterFace I.embedding I.outer x →
      (∃ u ∈ A, G.Adj u x) → x = t ∨ x = e := by
    intro x hx hxf ⟨u, hu, hux⟩
    have hxp := hExact x hxf
    rcases (hAmem u).1 hu with rfl | rfl | rfl
    · rcases chordless_native_cycle_root_neighbours p hp hch hxp hux with hx1 | hxb
      · exact Or.inl hx1
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl hxb)))).elim
    · rcases chordless_native_cycle_last_neighbours p hp hch hxp hux with hxa | hxd
      · exact (hx ((hAmem x).2 (Or.inl hxa))).elim
      · exact (hx ((hAmem x).2 (Or.inr (Or.inr hxd)))).elim
    · rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) hxp hux with hxe | hxb
      · exact Or.inr (by simpa only [show p.length-2-1 = p.length-3 by omega] using hxe)
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl (by simpa only [show p.length-2+1 = p.length-1 by omega] using hxb))))).elim
  have hCross : ∀ x, x ∉ A → ¬ OnOuterFace I.embedding I.outer x →
      (∃ u ∈ A, G.Adj u x) → ∀ y, y ∉ A → OnOuterFace I.embedding I.outer y → ¬ G.Adj x y := by
    intro x _ hxi ⟨u, hu, hux⟩ y hy hyf hxy
    rcases (hAmem u).1 hu with hua | hub | hud
    · have hya : y ≠ a := fun h => hy ((hAmem y).2 (Or.inl h))
      exact I.no_interior_boundary_pair_at_initial_vertex r hr hn hP hrpos hbad hsmall
        x y hxi hyf hya (hua ▸ hux.symm) hxy
    · have hxb : G.Adj x b := hub ▸ hux.symm
      by_cases hyP : y ∈ I.precolor.vertices
      · obtain ⟨_,hcase⟩ := I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP hrpos
          hbad hsmall x y b hxi hyP (hf (p.length-1)) hbP hxy hxb
        rcases hcase with ⟨hy2,_⟩ | ⟨_,htb⟩
        · exact hNoException x hxi hxb (by rwa [← hy2])
        · exact I.free_boundary_not_adjacent_both_prescribed_ends r hr hn hP hrpos hbad hsmall
            b (hf (p.length-1)) hbP hab htb
      · have hlenR : 2 ≤ r.length := by
          by_contra h
          exact hbad (I.colourable_of_prescribed_edge r hr hn hP (by omega) hsmall)
        have he := I.interior_unprescribed_neighbour_unique r hr hn hP hlenR hbad hsmall x b y
          hxi (hf (p.length-1)) hyf hbP hyP hxb hxy
        exact hy ((hAmem y).2 (Or.inr (Or.inl he.symm)))
    · have he := I.interior_neighbours_unique_at_short_free_boundary_vertex r hr hn hP hrpos hbad hsmall
        x d y hxi (hf (p.length-2)) hyf hdP hsecond (hud ▸ hux.symm) hxy
      exact hy ((hAmem y).2 (Or.inr (Or.inr he.symm)))
  have hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj a x → G.Adj x y → G.Adj d y → False := by
    intro x y hxi hyi hax hxy hdy
    obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot (p.length-2) (by omega)
    have hq2 : q.getVert 2 = a := by
      rw [hqo 2 (by omega), Nat.sub_add_cancel (by omega : 2 ≤ p.length), ZMod.natCast_self]
      simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
    have hq1 : q.getVert 1 = b := by
      rw [hqo 1 (by omega), show p.length-2+1 = p.length-1 by omega, walkCycleVertices_nat_le p (by omega)]
    have hfree : ∀ u ∈ I.precolor.vertices, u ∉ cycleInterval (walkCycleVertices q) 1 (2-2) := by
      intro u hu ⟨i, hi, hiu⟩
      have hi0 : i = 0 := by omega
      have hbu : b = u := by simpa only [hi0, Nat.add_zero, Nat.cast_one,
        show walkCycleVertices q 1 = q.getVert 1 by simpa only [Nat.cast_one] using walkCycleVertices_nat_le q (i := 1) (by omega), hq1] using hiu
      exact hbP (hbu ▸ hu)
    exact hbad (I.colourable_of_interior_three_path_free_arc hG q hq hqf hqr 2 (by omega) (by omega) y x hyi hxi hdy.symm hxy.symm
      (by rw [hq2]; exact hax.symm) hsecond hfree hsmall)
  have hNoOld : ∀ x, x ∉ A → 3 ≤ (I.lists x).card → (∃ u ∈ A, G.Adj u x) →
      ∀ y, y ∉ A → (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hx3 hxN y hy hys hxy
    have hyf : OnOuterFace I.embedding I.outer y := by
      by_contra h
      have := I.interior_lists y h
      omega
    by_cases hxf : OnOuterFace I.embedding I.outer x
    · rcases hNewFace x hx hxf hxN with hxt | hxe
      · have hc : (I.lists x).card = 1 := by rw [hxt, I.singleton t htP]; exact Finset.card_singleton _
        omega
      · have hey : G.Adj e y := by rwa [hxe] at hxy
        rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) (hExact y hyf) hey with hy4 | hy2
        · have hc : 3 ≤ (I.lists y).card := by simpa only [show p.length-3-1 = p.length-4 by omega] using hy4 ▸ hfourth
          omega
        · exact hy ((hAmem y).2 (Or.inr (Or.inr (by simpa only [show p.length-3+1 = p.length-2 by omega] using hy2))))
    · exact hCross x hx hxf hxN y hy hyf hxy
  have hOldNoA : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (I.lists x).card ≤ 2 → ∀ u ∈ A, ¬ G.Adj x u := by
    intro x hx hxP hxs u hu hxu
    have hxf : OnOuterFace I.embedding I.outer x := by
      by_contra h
      have := I.interior_lists x h
      omega
    rcases (hAmem u).1 hu with hua | hub | hud
    · rw [hua] at hxu
      exact I.short_not_adj_precolored hxP haP hxs hxu
    · rw [hub] at hxu
      rcases chordless_native_cycle_last_neighbours p hp hch (hExact x hxf) hxu.symm with hxa | hxd
      · exact hx ((hAmem x).2 (Or.inl hxa))
      · exact hx ((hAmem x).2 (Or.inr (Or.inr hxd)))
    · rw [hud] at hxu
      exact hdP (I.precolor.endpoints_of_mem_edges (I.short_edges hxu hxs hsecond)).2
  -- Only unprescribed old short lists need the unchanged-list assertion.
  obtain ⟨cd, hcd⟩ := I.list_nonempty d
  obtain ⟨cb, hcb, hcbA, hcbD⟩ : ∃ c ∈ I.lists b, c ≠ I.prescribed a ∧ c ≠ cd := by
    have hc : ({I.prescribed a, cd} : Finset C).card < (I.lists b).card := Finset.card_le_two.trans_lt (by omega)
    obtain ⟨c, hcL, hcN⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hN : c ≠ I.prescribed a ∧ c ≠ cd := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hcN
    exact ⟨c, hcL, hN⟩
  let f : V → C := fun x => if x = a then I.prescribed a else if x = b then cb else cd
  have hfa : f a = I.prescribed a := by simp only [f, ite_true]
  have hfb : f b = cb := by simp only [f, ite_eq_right hba, ite_true]
  have hfd : f d = cd := by simp only [f, ite_eq_right hda, ite_eq_right hdb]
  have hfA : ∀ x ∈ A, f x ∈ I.lists x := by
    intro x hx
    rcases (hAmem x).1 hx with hx | hx | hx
    · rw [hx, hfa, I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [hx, hfb]; exact hcb
    · rw [hx, hfd]; exact hcd
  have hproperA : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y := by
    intro x hx y hy hxy
    rcases (hAmem x).1 hx with hx | hx | hx <;> rcases (hAmem y).1 hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢
    · exact (hxy.ne rfl).elim
    · rw [hfa, hfb]; exact hcbA.symm
    · exact (had hxy).elim
    · rw [hfb, hfa]; exact hcbA
    · exact (hxy.ne rfl).elim
    · rw [hfb, hfd]; exact hcbD
    · exact (had hxy.symm).elim
    · rw [hfd, hfb]; exact hcbD.symm
    · exact (hxy.ne rfl).elim
  have hAconn : ConnSet G (↑A : Set V) := by
    have h := ((connSet_singleton G a).insert_adj (Set.mem_singleton a) hab.symm).insert_adj
      (Set.mem_insert b {a}) hbd.symm
    convert h using 1
    ext x
    simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  let Q : Set V := {x | x ∈ I.precolor.vertices ∧ x ∉ A}
  have hQeq : Q = {x | x ∈ (r.drop 1).support} := by
    ext x
    constructor
    · rintro ⟨hxP,hxA⟩
      obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv x).1 hxP)
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k=0 := by omega
        have hxa : x=a := by simpa only [hk0,Walk.getVert_zero] using hk.symm
        exact hxA ((hAmem x).2 (Or.inl hxa))
      exact Walk.mem_support_iff_exists_getVert.2 ⟨k-1,
        by rw [Walk.drop_getVert,Nat.add_sub_of_le hkpos]; exact hk,
        by rw [Walk.drop_length]; omega⟩
    · intro hx
      have hxP := (hPv x).2 ((Walk.isSubwalk_drop r 1).support_subset hx)
      refine ⟨hxP,?_⟩
      intro hxA
      rcases (hAmem x).1 hxA with hxa | hxb | hxd
      · obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 hx
        rw [Walk.drop_getVert] at hk
        have he := hr.getVert_injOn (by change 1+k ≤ r.length; rw [Walk.drop_length] at hkl; omega)
          (Nat.zero_le _) (by simpa only [Walk.getVert_zero] using hk.trans hxa)
        omega
      · exact hbP (hxb ▸ hxP)
      · exact hdP (hxd ▸ hxP)
  have hResP : ∀ x ∈ Q, residual G I.lists A f x = {I.prescribed x} := by
    intro x hx
    apply Finset.Subset.antisymm
    · have h := residual_subset G I.lists A f x
      rwa [I.singleton x hx.1] at h
    · apply Finset.singleton_subset_iff.2
      apply (mem_residual_iff I.lists A f x _).2
      refine ⟨by simp only [I.singleton x hx.1,Finset.mem_singleton],?_⟩
      intro z hz hxz
      rcases (hAmem z).1 hz with hza | hzb | hzd
      · rw [hza,hfa]
        exact I.proper_on_precolored_vertices hx.1 haP (hza ▸ hxz)
      · have hxb : G.Adj b x := hzb ▸ hxz.symm
        rcases chordless_native_cycle_last_neighbours p hp hch (hExact x (I.on_outer x hx.1)) hxb with hxa | hxd
        · exact (hx.2 ((hAmem x).2 (Or.inl hxa))).elim
        · exact (hx.2 ((hAmem x).2 (Or.inr (Or.inr hxd)))).elim
      · exact (I.short_not_adj_precolored hdP hx.1 hsecond (hzd ▸ hxz.symm)).elim
  have hResTwo : ∀ x, x ∉ A → x ∉ Q → 2 ≤ (residual G I.lists A f x).card := by
    intro x hx hxQ
    have hxP : x ∉ I.precolor.vertices := fun h => hxQ ⟨h,hx⟩
    by_cases hxs : (I.lists x).card ≤ 2
    · rw [residual_unchanged I.lists A f x (hOldNoA x hx hxP hxs)]
      exact I.outside_precolor_list_ge_two hxP
    · exact residual_two_edge_path_card_ge_two I.girth hab hbd hda.symm
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inl h)))) I.lists f (by omega)
  have hNew : ∀ x, 3 ≤ (I.lists x).card → (residual G I.lists A f x).card ≤ 2 → ∃ u ∈ A, G.Adj u x :=
    fun x hx hxs => short_residual_neighbor I.lists A f x hx hxs
  have hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → x ∈ Q ∧ y ∈ Q := by
    intro x hx y hy hxy hxs hys
    by_cases hxOld : (I.lists x).card ≤ 2 <;> by_cases hyOld : (I.lists y).card ≤ 2
    · have hends := I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)
      exact ⟨⟨hends.1,hx⟩,⟨hends.2,hy⟩⟩
    · exact (hNoOld y hy (by omega) (hNew y (by omega) hys) x hx hxOld hxy.symm).elim
    · exact (hNoOld x hx (by omega) (hNew x (by omega) hxs) y hy hyOld hxy).elim
    · exfalso
      have hxN := hNew x (by omega) hxs
      have hyN := hNew y (by omega) hys
      by_cases hxf : OnOuterFace I.embedding I.outer x
      · by_cases hyf : OnOuterFace I.embedding I.outer y
        · have hxe : x = e := (hNewFace x hx hxf hxN).resolve_left (fun h => by
            have hc : (I.lists x).card = 1 := by rw [h, I.singleton t htP]; exact Finset.card_singleton _
            omega)
          have hye : y = e := (hNewFace y hy hyf hyN).resolve_left (fun h => by
            have hc : (I.lists y).card = 1 := by rw [h, I.singleton t htP]; exact Finset.card_singleton _
            omega)
          exact hxy.ne (hxe.trans hye.symm)
        · exact hCross y hy hyf hyN x hx hxf hxy.symm
      by_cases hyf : OnOuterFace I.embedding I.outer y
      · exact hCross x hx hxf hxN y hy hyf hxy
      rcases short_residual_two_edge_path_adjacent I.girth hab hbd hx hy I.lists f (by omega) (by omega) hxs hys hxy with h | h
      · exact hNoThree x y hxf hyf h.1 hxy h.2
      · exact hNoThree y x hyf hxf h.2 hxy.symm h.1
  apply hbad
  apply I.colourable_of_connected_residual_prescription hG p hp hface hroot hExact A
    ((hAmem a).2 (Or.inl rfl)) hAconn f hfA hproperA Q ?_ (fun _ h => h.2)
    (fun x hx => Or.inl (I.on_outer x hx.1)) ?_
    (fun x hx => by rw [hResP x hx,Finset.card_singleton]; omega)
    I.prescribed (fun x hx => by rw [hResP x hx]; exact Finset.mem_singleton_self _)
    (fun x hx y hy hxy => I.proper_on_precolored_vertices hx.1 hy.1 hxy)
    hResTwo hShort hsmall
  · rw [hQeq]; exact walk_support_connSet (r.drop 1)
  · intro x y q hq hs
    have hsub : q.support.toFinset ⊆ I.precolor.vertices := fun z hz => (hs z (List.mem_toFinset.1 hz)).1
    have hc := Finset.card_le_card hsub
    have hPcard := I.precolor.card_vertices_le
    rw [List.toFinset_card_of_nodup hq.support_nodup,Walk.length_support] at hc
    omega

/-- A remaining good-fourth-list counterexample necessarily has all six
prescribed vertices and the backward exceptional common neighbour. Thus the
general nonexceptional branch is closed without a five-vertex restriction. -/
theorem remaining_good_fourth_counterexample_has_backward_exception (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    {t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    r.length=5 ∧ ∃ u, ¬ OnOuterFace I.embedding I.outer u ∧
      G.Adj u (p.getVert (p.length-1)) ∧ G.Adj u (r.getVert 2) := by
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  by_cases hno : ∀ z, ¬ OnOuterFace I.embedding I.outer z →
      G.Adj z (p.getVert (p.length-1)) → ¬ G.Adj z (r.getVert 2)
  · exact (hbad (I.colourable_of_path_short_second_good_fourth_without_exception hG p hp hface hroot hExact
      r hr hn hP hrpos horder hsecond hfourth hno hsmall)).elim
  · push Not at hno
    obtain ⟨u,hu,hub,hu2⟩ := hno
    have hbP : p.getVert (p.length-1) ∉ I.precolor.vertices := by
      intro h
      obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv _).1 h)
      have he := hp.getVert_injOn' (show k ≤ p.length-1 from by omega)
        (show p.length-1 ≤ p.length-1 from le_rfl) ((horder k hkl).symm.trans hk)
      omega
    obtain ⟨hl,_⟩ := I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP hrpos hbad hsmall
      u (r.getVert 2) (p.getVert (p.length-1)) hu ((hPv _).2 (r.getVert_mem_support 2))
      ((hverts _).1 (p.getVert_mem_support _)) hbP hu2 hub
    exact ⟨hl,u,hu,hub,hu2⟩

end Thomassen.BoundaryInstance
