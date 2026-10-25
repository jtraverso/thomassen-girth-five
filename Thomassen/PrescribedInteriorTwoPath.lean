/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CompatiblePrescription

/-! Interior two-paths through the original prescribed prefix. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- An interior two-path from the initial prescribed endpoint to internal
position three or four is a complete induction case when the prescription
follows the forward native facial order. The inner cycle has at most six
vertices; replacing its prescribed prefix leaves a path on at most five. -/
theorem colourable_of_prescribed_prefix_interior_two_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (d : ℕ) (hd : d = 3 ∨ d = 4) (hdr : d < r.length)
    (x : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hxa : G.Adj x a) (hxd : G.Adj x (r.getVert d))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hrlen : r.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup, Walk.length_support] at hn
    omega
  have hlen : r.length < p.length := by
    by_contra h
    have he : r.getVert p.length = r.getVert 0 := by
      rw [horder p.length (by omega), Walk.getVert_length, Walk.getVert_zero]
    have hi := hr.getVert_injOn (by change p.length ≤ r.length; omega) (Nat.zero_le _) he
    have := hp.three_le_length
    omega
  have hxR : x ∉ r.support := fun h => hx (I.on_outer x ((hPv x).2 h))
  have hdx : r.getVert d ≠ a := by
    intro he
    have hi := hr.getVert_injOn (by change d ≤ r.length; omega) (Nat.zero_le _)
      (show r.getVert d = r.getVert 0 from by simpa only [Walk.getVert_zero] using he)
    omega
  have hUnique : ∀ z ∈ r.support, G.Adj x z → z = a ∨ z = r.getVert d := by
    intro z hz hxz
    by_cases hza : z = a
    · exact Or.inl hza
    obtain ⟨k, hk, hkr, hkz⟩ := I.interior_endpoint_shared_neighbour_indices hG p hp hface hroot hExact r hr hn hP hbad hsmall
      x z hx ((hPv z).2 hz) hza hxa hxz
    have hTail : ∀ i, 3 ≤ i → i ≤ r.length → r.getVert i ∈ (r.drop 3).support := by
      intro i hi hil
      apply Walk.mem_support_iff_exists_getVert.2
      refine ⟨i - 3, ?_, ?_⟩
      · rw [Walk.drop_getVert, Nat.add_sub_of_le hi]
      · rw [Walk.drop_length]; omega
    exact Or.inr (external_short_path_neighbour_unique I.girth (r.drop 3) (hr.drop 3)
      (by rw [Walk.drop_length]; omega) (hTail d (by omega) (by omega))
      (fun h => hxR ((Walk.isSubwalk_drop r 3).support_subset h)) hxd
      (hkz ▸ hTail k (by omega) (by omega)) hxz)
  have hNoOld : ∀ z, z ∉ r.support → (I.lists z).card ≤ 2 → ¬ G.Adj x z := by
    intro z hz hzs hxz
    have hzface : OnOuterFace I.embedding I.outer z := by
      by_contra h
      have := I.interior_lists z h
      omega
    exact I.no_interior_two_path_from_prescribed_endpoint hG p hp hface hroot hExact r hr hPv hbad hsmall
      x z hx hzface (fun h => hz ((hPv z).1 h)) hxa hxz
  have h3x := I.interior_lists x hx
  obtain ⟨cx, hcx, hcxA, hcxD⟩ : ∃ c ∈ I.lists x, c ≠ I.prescribed a ∧ c ≠ I.prescribed (r.getVert d) := by
    have hc : ({I.prescribed a, I.prescribed (r.getVert d)} : Finset C).card < (I.lists x).card :=
      (Finset.card_le_two).trans_lt (by omega)
    obtain ⟨c, hcL, hcN⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hN : c ≠ I.prescribed a ∧ c ≠ I.prescribed (r.getVert d) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hcN
    exact ⟨c, hcL, hN⟩
  let f : V → C := fun z => if z = x then cx else I.prescribed z
  have hfOld : ∀ z ∈ r.support, f z = I.prescribed z := by
    intro z hz
    change (if z = x then cx else I.prescribed z) = I.prescribed z
    exact ite_eq_right (fun (h : z = x) => hxR (h ▸ hz))
  have hfList : ∀ z, z ∈ r.support ∨ z = x → f z ∈ I.lists z := by
    intro z hz
    rcases hz with hz | rfl
    · rw [hfOld z hz, I.singleton z ((hPv z).2 hz)]
      exact Finset.mem_singleton_self _
    · simpa only [f, ite_true] using hcx
  have hfProper : ∀ z w, (z ∈ r.support ∨ z = x) → (w ∈ r.support ∨ w = x) → G.Adj z w → f z ≠ f w := by
    intro z w hz hw hzw
    rcases hz with hz | rfl <;> rcases hw with hw | rfl
    · rw [hfOld z hz, hfOld w hw]
      exact I.proper_on_precolored_vertices ((hPv z).2 hz) ((hPv w).2 hw) hzw
    · rw [hfOld z hz]
      simp only [f, ite_true]
      rcases hUnique z hz hzw.symm with rfl | rfl
      · exact hcxA.symm
      · exact hcxD.symm
    · rw [hfOld w hw]
      simp only [f, ite_true]
      rcases hUnique w hw hzw with rfl | rfl
      · exact hcxA
      · exact hcxD
    · exact (hzw.ne rfl).elim
  have hxpn : G.Adj x (p.getVert d) := by rwa [horder d (by omega)] at hxd
  let q : G.Walk (p.getVert d) a := .cons hxpn.symm (.cons hxa .nil)
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, or_false, not_or, and_true, not_false_eq_true]
    exact ⟨⟨hxpn.ne.symm, by simpa only [← horder d (by omega)] using hdx⟩, hxa.ne⟩
  have hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert i) := by
    intro i hi hil
    have hi1 : i = 1 := by change i < 2 at hil; omega
    subst i
    exact hx
  obtain ⟨S, T, hSs, hTs, hcover, hinter, hedges, _, _, hSC, hkeep, ⟨oS, hSface⟩, ⟨M, oT, hTface⟩⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG p hp hface hroot d q hq (by omega) (by omega)
      (by change 0 < 2; omega) (by change 2 ≤ 3; omega) hInner
  let c := spliceFacePath p d q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp d q hq (by omega) (by omega)
    (closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot d q hInner)
  have hcLen : c.length ≤ 6 := by rw [spliceFacePath_length p d q (by omega)]; change d + 2 ≤ 6; omega
  have hcBound : c.support.toFinset.card ≤ 6 := by rw [cycle_support_card_eq_length c hc]; exact hcLen
  have hcMem : ∀ z, z ∈ c.support ↔ z ∈ (p.take d).support ∨ z ∈ q.support :=
    fun _ => Walk.mem_support_append_iff (p.take d) q
  have hqMem : ∀ z, z ∈ q.support ↔ z = p.getVert d ∨ z = x ∨ z = a := by
    intro z
    simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
  have hpreOld : ∀ z ∈ (p.take d).support, z ∈ r.support := by
    intro z hz
    obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    rw [Walk.take_length, Nat.min_eq_left (by omega : d ≤ p.length)] at hk
    rw [Walk.take_getVert, Nat.min_eq_right hk] at hkz
    exact ((horder k (by omega)).trans hkz) ▸ r.getVert_mem_support k
  have hcOld : ∀ z ∈ c.support, z ∈ r.support ∨ z = x := by
    intro z hz
    rcases (hcMem z).1 hz with hz | hz
    · exact Or.inl (hpreOld z hz)
    · rcases (hqMem z).1 hz with hzd | hzx | hza
      · exact Or.inl (hzd.symm ▸ (horder d (by omega) ▸ r.getVert_mem_support d))
      · exact Or.inr hzx
      · exact Or.inl (hza ▸ r.start_mem_support)
  have hSouter : ∀ z : S, OnOuterFace I.embedding I.outer z.1 → z.1 ∈ c.support := by
    intro z hz
    by_cases hzArc : z.1 ∈ cycleInterval (walkCycleVertices p) 1 (d - 2)
    · obtain ⟨k, hk, hkz⟩ := hzArc
      have hkz' : p.getVert (1 + k) = z.1 := by rwa [walkCycleVertices_nat_le p (by omega : 1 + k ≤ p.length)] at hkz
      apply (hcMem z.1).2
      apply Or.inl
      exact Walk.mem_support_iff_exists_getVert.2 ⟨1 + k,
        by rw [Walk.take_getVert, Nat.min_eq_right (by omega : 1 + k ≤ d)]; exact hkz',
        by rw [Walk.take_length, Nat.min_eq_left (by omega : d ≤ p.length)]; omega⟩
    · have hzST : z.1 ∈ S ∩ T := ⟨z.2, hkeep z.1 hz hzArc⟩
      rw [hinter] at hzST
      exact (hcMem z.1).2 (Or.inr hzST)
  let PS : BoundaryPrecolor G := .cycle c hc hcBound
  have hPSv : ∀ z, z ∈ PS.vertices ↔ z ∈ c.support := by simp only [PS, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hSthree : ∀ z ∈ S, z ∉ c.support → 3 ≤ (I.lists z).card := by
    intro z hz hzc
    exact I.interior_lists z (fun h => hzc (hSouter ⟨z, hz⟩ h))
  have hchS : ∀ z ∈ PS.vertices, ∀ w ∈ PS.vertices, G.Adj z w → s(z,w) ∈ PS.edges := by
    intro z hz w hw hzw
    let : NeZero c.length := ⟨by have := hc.three_le_length; omega⟩
    apply List.mem_toFinset.2
    apply (walkCycleVertices_edges c hc z w).1
    apply cyclicSubgraph_of_chordless (short_cycle_isChordless I.girth (walk_isCycleMap c hc) hc.three_le_length hcLen)
    · rw [walkCycleVertices_range c hc]; exact (hPSv z).1 hz
    · rw [walkCycleVertices_range c hc]; exact (hPSv w).1 hw
    · exact hzw
  obtain ⟨cS, hcS, hcSfix⟩ := I.colourable_induced_with_compatible_prescription S (inducedPlaneMap I.embedding S) oS PS
    (fun z hz => hSC z ((hcMem z).1 ((hPSv z).1 hz))) f
    (fun z hz => hfList z (hcOld z ((hPSv z).1 hz)))
    (fun z hz w hw hzw => hfProper z w (hcOld z ((hPSv z).1 hz)) (hcOld w ((hPSv w).1 hw)) hzw)
    hchS (fun z hz hzP => (hPSv z).2 (hSouter ⟨z, hz⟩ (I.on_outer z hzP)))
    (fun z hz => (hSface z).2 ((hcMem z.1).1 ((hPSv z.1).1 hz)))
    (fun z hz => I.interior_lists z.1 (fun h => hz ((hSface z).2 ((hcMem z.1).1 (hSouter z h)))))
    (by intro z hz hzc hzs; have := hSthree z hz (fun h => hzc ((hPSv z).2 h)); omega)
    hSs hsmall
  let b := Walk.cons hxa.symm (Walk.cons hxd (r.drop d))
  have hbMem : ∀ z, z ∈ b.support ↔ z = a ∨ z = x ∨ z ∈ (r.drop d).support := by
    intro z
    simp only [b, Walk.support_cons, List.mem_cons]
  have haTail : a ∉ (r.drop d).support := by
    intro ha
    obtain ⟨k, hka, hk⟩ := Walk.mem_support_iff_exists_getVert.1 ha
    rw [Walk.drop_getVert] at hka
    have hi := hr.getVert_injOn (by change d + k ≤ r.length; rw [Walk.drop_length] at hk; omega)
      (Nat.zero_le _) (by simpa only [Walk.getVert_zero] using hka)
    omega
  have hb : b.IsPath := by
    apply Walk.IsPath.mk'
    simp only [b, Walk.support_cons, List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨hxa.ne.symm, haTail⟩, ⟨fun h => hxR ((Walk.isSubwalk_drop r d).support_subset h), (hr.drop d).support_nodup⟩⟩
  have hbLen : b.length ≤ 4 := by simp only [b, Walk.length_cons, Walk.drop_length]; omega
  have hends : ¬ G.Adj a t := by
    intro hat
    have haP := (hPv a).2 r.start_mem_support
    have htP := (hPv t).2 r.end_mem_support
    have he : s(a,t) ∈ r.edges := by
      simpa only [hP, BoundaryPrecolor.edges, List.mem_toFinset] using I.short_edges hat
        (by simp only [I.singleton a haP, Finset.card_singleton]; omega)
        (by simp only [I.singleton t htP, Finset.card_singleton]; omega)
    have ht := hr.eq_snd_of_mem_edges he
    have hi := hr.getVert_injOn (show r.length ≤ r.length from le_rfl) (show 1 ≤ r.length from by omega)
      (by simpa only [Walk.getVert_length, Walk.snd] using ht)
    omega
  have hbch := four_edge_path_isChordless I.girth b hb hbLen hends
  have hbBound : b.support.toFinset.card ≤ 6 := by
    calc _ ≤ b.support.length := List.toFinset_card_le _
         _ = b.length + 1 := Walk.length_support b
         _ ≤ 6 := by omega
  let PT : BoundaryPrecolor G := .path b hb hbBound
  have hPTv : ∀ z, z ∈ PT.vertices ↔ z ∈ b.support := by simp only [PT, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hbOld : ∀ z ∈ b.support, z ∈ r.support ∨ z = x := by
    intro z hz
    rcases (hbMem z).1 hz with hza | hzx | hzTail
    · exact Or.inl (hza ▸ r.start_mem_support)
    · exact Or.inr hzx
    · exact Or.inl ((Walk.isSubwalk_drop r d).support_subset hzTail)
  have hOldT : ∀ z ∈ T, z ∈ r.support → z ∈ b.support := by
    intro z hzT hzR
    obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.1 hzR
    by_cases hkd : d ≤ k
    · apply (hbMem z).2
      apply Or.inr ∘ Or.inr
      exact Walk.mem_support_iff_exists_getVert.2 ⟨k-d, by rw [Walk.drop_getVert, Nat.add_sub_of_le hkd]; exact hkz,
        by rw [Walk.drop_length]; omega⟩
    · have hzS : z ∈ S := by
        apply hSC z ∘ Or.inl
        apply Walk.mem_support_iff_exists_getVert.2
        exact ⟨k, by rw [Walk.take_getVert, Nat.min_eq_right (by omega : k ≤ d)]; exact (horder k hk).symm.trans hkz,
          by rw [Walk.take_length, Nat.min_eq_left (by omega : d ≤ p.length)]; omega⟩
      have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS, hzT⟩; rwa [hinter] at h
      rcases (hqMem z).1 hzq with hzd | hzx | hza
      · have hi := hr.getVert_injOn hk (show d ≤ r.length from by omega) (hkz.trans (hzd.trans (horder d (by omega)).symm))
        omega
      · exact (hxR (hzx ▸ hzR)).elim
      · exact (hbMem z).2 (Or.inl hza)
  have hbT : ∀ z ∈ b.support, z ∈ T := by
    intro z hz
    rcases (hbMem z).1 hz with hza | hzx | hzTail
    · have h : a ∈ S ∩ T := by rw [hinter]; exact q.end_mem_support
      exact hza ▸ h.2
    · have h : x ∈ S ∩ T := by rw [hinter]; exact (hqMem x).2 (Or.inr (Or.inl rfl))
      exact hzx ▸ h.2
    · have hzOld := (Walk.isSubwalk_drop r d).support_subset hzTail
      apply hkeep z (I.on_outer z ((hPv z).2 hzOld))
      intro hzArc
      obtain ⟨j, hj, hjz⟩ := hzArc
      obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.1 hzTail
      rw [Walk.drop_getVert] at hkz
      have he : p.getVert (d + k) = p.getVert (1 + j) := by
        rw [← horder (d + k) (by rw [Walk.drop_length] at hk; omega), hkz]
        exact (walkCycleVertices_nat_le p (i := 1+j) (by omega)).symm.trans hjz |>.symm
      have hi := hp.getVert_injOn' (show d + k ≤ p.length - 1 from by rw [Walk.drop_length] at hk; omega)
        (show 1 + j ≤ p.length - 1 from by omega) he
      omega
  obtain ⟨cT, hcT, hcTfix⟩ := I.colourable_induced_with_compatible_prescription T M oT PT
    (fun z hz => hbT z ((hPTv z).1 hz)) f
    (fun z hz => hfList z (hbOld z ((hPTv z).1 hz)))
    (fun z hz w hw hzw => hfProper z w (hbOld z ((hPTv z).1 hz)) (hbOld w ((hPTv w).1 hw)) hzw)
    (fun z hz w hw hzw => List.mem_toFinset.2 (hbch.mem_edges ((hPTv z).1 hz) ((hPTv w).1 hw) hzw))
    (fun z hz hzP => (hPTv z).2 (hOldT z hz ((hPv z).1 hzP)))
    (by
      intro z hz
      rcases hbOld z.1 ((hPTv z.1).1 hz) with hzR | hzx
      · exact hTface z (Or.inl (I.on_outer z.1 ((hPv z.1).2 hzR)))
      · exact hTface z (Or.inr ((hqMem z.1).2 (Or.inr (Or.inl hzx)))))
    (fun z hz => I.interior_lists z.1 (fun h => hz (hTface z (Or.inl h))))
    (by
      intro z hzT hzPT hzs w hw hzw
      have hzR : z ∉ r.support := fun h => hzPT ((hPTv z).2 (hOldT z hzT h))
      rcases hbOld w ((hPTv w).1 hw) with hwR | hwx
      · exact I.short_not_adj_precolored (fun h => hzR ((hPv z).1 h)) ((hPv w).2 hwR) hzs hzw
      · exact hNoOld z hzR hzs (by simpa only [hwx] using hzw.symm)) hTs hsmall
  apply hbad
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hcS hcT ?_
  · intro z
    have h := Set.mem_univ z
    rwa [← hcover] at h
  · intro z hzS hzT
    have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS, hzT⟩; rwa [hinter] at h
    have hzPS := (hPSv z).2 ((hcMem z).2 (Or.inr hzq))
    have hzPT : z ∈ PT.vertices := by
      apply (hPTv z).2
      rcases (hqMem z).1 hzq with hzd | hzx | hza
      · apply (hbMem z).2 ∘ Or.inr ∘ Or.inr
        exact hzd.symm ▸ (horder d (by omega) ▸ (r.drop d).start_mem_support)
      · exact (hbMem z).2 (Or.inr (Or.inl hzx))
      · exact (hbMem z).2 (Or.inl hza)
    exact (hcSfix ⟨z, hzS⟩ hzPS).trans (hcTfix ⟨z, hzT⟩ hzPT).symm

/-- The first forward boundary vertex being prescribed fixes the orientation
of the whole original prescribed path. This uses its actual native edge set
and the previously checked facial path-order theorem. -/
lemma prescribed_path_forward_of_first_face_vertex (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ k ≤ r.length, r.getVert k = p.getVert k := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hc := walk_isCycleMap p hp
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hrange : ∀ z, OnOuterFace I.embedding I.outer z → z ∈ Set.range (walkCycleVertices p) := by
    intro z hz
    rw [walkCycleVertices_range p hp]
    exact hExact z hz
  have haP := (hPv a).2 r.start_mem_support
  have hadj : G.Adj a (p.getVert 1) := by
    simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hedge : s(a,p.getVert 1) ∈ r.edges := by
    simpa only [hP, BoundaryPrecolor.edges, List.mem_toFinset] using I.short_edges hadj
      (by simp only [I.singleton a haP, Finset.card_singleton]; omega)
      (by simp only [I.singleton _ hfirst, Finset.card_singleton]; omega)
  have hfirstEq : r.getVert 1 = p.getVert 1 := (hr.eq_snd_of_mem_edges hedge).symm
  have hrpos : 0 < r.length := Walk.not_nil_iff_lt_length.1
    (fun h => List.not_mem_nil ((Walk.edges_eq_nil.2 h) ▸ hedge))
  obtain ⟨i, e, he, horder⟩ := I.prescribed_path_follows_facial_cycle hc hlen hface hrange hG hbad hsmall r hr hPv
  have hzero : walkCycleVertices p 0 = a := by simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hi0 : i = 0 := hc.inj (by
    simpa only [Walk.getVert_zero, Nat.cast_zero, zero_mul, add_zero, hzero] using (horder 0 (Nat.zero_le _)).symm)
  subst i
  have hrlen : r.length < p.length := by
    by_contra h
    have heq : r.getVert p.length = r.getVert 0 := by
      simpa only [ZMod.natCast_self, zero_mul, zero_add, hzero, Walk.getVert_zero] using horder p.length (by omega)
    have hi := hr.getVert_injOn (by change p.length ≤ r.length; omega) (Nat.zero_le _) heq
    omega
  have heone : e = 1 := by
    rcases he with he | he
    · exact he
    · have h1 := horder 1 (by omega)
      rw [hfirstEq, Nat.cast_one, one_mul, zero_add, he] at h1
      have heq : walkCycleVertices p 1 = walkCycleVertices p (-1) := by
        calc
          _ = p.getVert 1 := by simpa only [Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
          _ = _ := h1
      have heq' := hc.inj heq
      exact (zmod_two_ne_zero_of_three_le hlen (by linear_combination heq')).elim
  intro k hk
  rw [horder k hk, heone, mul_one, zero_add, walkCycleVertices_nat_le p (by omega)]

/-- Once the first forward boundary vertex is prescribed, no interior
vertex can join that prescribed endpoint to any other old boundary vertex in a
smallest counterexample. This includes all internal prescribed vertices. -/
theorem no_interior_two_path_from_forward_prescribed_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  by_cases hyP : y ∈ I.precolor.vertices
  · obtain ⟨d, hd, hdr, hdy⟩ := I.interior_endpoint_shared_neighbour_indices hG p hp hface hroot hExact r hr hn hP hbad hsmall
      x y hx hyP hya hxa hxy
    have horder := I.prescribed_path_forward_of_first_face_vertex hG p hp hface hExact r hr hn hP hfirst hbad hsmall
    exact hbad (I.colourable_of_prescribed_prefix_interior_two_path hG p hp hface hroot hExact r hr hn hP horder d hd hdr
      x hx hxa (by rwa [hdy]) hsmall)
  · have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
      simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
    exact I.no_interior_two_path_from_prescribed_endpoint hG p hp hface hroot hExact r hr hPv hbad hsmall x y hx hy hyP hxa hxy

/-- With the good second backward boundary list, a prescribed endpoint has
no neighbour outside the prescription adjacent to another prescribed vertex.
Both interior positions three/four are resolved by actual strict cuts. -/
lemma prescribed_endpoint_no_shared_prescribed_neighbour (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ x, x ∉ r.support → G.Adj a x → ∀ y ∈ r.support, y ≠ a → ¬ G.Adj x y := by
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  intro x hxR hax y hyR hya hxy
  have hyP := (hPv y).2 hyR
  by_cases hx : OnOuterFace I.embedding I.outer x
  · rcases chordless_native_cycle_root_neighbours p hp hch (hExact x hx) hax with hx1 | hxlast
    · have hxP : x ∈ I.precolor.vertices := by rw [hx1]; exact hfirst
      exact hxR ((hPv x).1 hxP)
    · have hlasty : G.Adj (p.getVert (p.length - 1)) y := by rwa [hxlast] at hxy
      rcases chordless_native_cycle_last_neighbours p hp hch (hExact y (I.on_outer y hyP)) hlasty with hya' | hy2
      · exact hya hya'
      · have hycard : (I.lists y).card = 1 := by simp only [I.singleton y hyP, Finset.card_singleton]
        rw [hy2] at hycard
        omega
  · exact I.no_interior_two_path_from_forward_prescribed_endpoint hG p hp hface hroot hExact r hr hn hP hfirst hbad hsmall
      x y hx (I.on_outer y hyP) hya hax.symm hxy

/-- The good-second-boundary-list endpoint-deletion branch is complete for
all original prescribed paths of at most six vertices. Neither endpoint conflict
is assumed: both exclusions follow from the actual boundary and strict cuts. -/
theorem colourable_of_good_second_boundary_list_all_prescriptions (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hNoShared := I.prescribed_endpoint_no_shared_prescribed_neighbour hG p hp hface hroot hExact r hr hn hP hfirst hsecond hbad hsmall
  exact hbad (I.colourable_of_good_second_boundary_list hG p hp hface hroot hExact r hr hn hP hfirst hsecond hNoShared hsmall)

/-- In every smallest counterexample with this orientation of the prescribed
path, the second backward boundary vertex has at most two available colours. -/
lemma prescribed_second_boundary_list_le_two (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length - 2))).card ≤ 2 := by
  by_contra h
  exact hbad (I.colourable_of_good_second_boundary_list_all_prescriptions hG p hp hface hroot hExact r hr hn hP hfirst (by omega) hsmall)

end Thomassen.BoundaryInstance
