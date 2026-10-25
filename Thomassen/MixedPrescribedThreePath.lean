/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FiveEdgePathChordless

/-! Interior three-path cuts through a short end of the old prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A mixed interior three-path with an old short free endpoint is eliminated
when its prescribed endpoint leaves at most three old prescribed vertices
on the initial side.
Both actual pieces, their faces and every short-list attachment are derived. -/
theorem colourable_of_mixed_three_path_short_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (i j : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (hrj : r.length < j) (hjp : j < p.length)
    (hbShort : (I.lists (p.getVert j)).card ≤ 2)
    (u v2 : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert i)) (huz : G.Adj u v2) (hzj : G.Adj v2 (p.getVert j))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hidx : ∀ k l : ℕ, k < p.length → l < p.length → p.getVert k = p.getVert l → k=l := by
    intro k l hk hl he
    exact hp.getVert_injOn' (by change k ≤ p.length-1; omega) (by change l ≤ p.length-1; omega) he
  have huR : u ∉ r.support := fun h => hu (I.on_outer u ((hPv u).2 h))
  have hzR : v2 ∉ r.support := fun h => hz (I.on_outer v2 ((hPv v2).2 h))
  have hjR : p.getVert j ∉ r.support := by
    intro h
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 h
    have he := hidx k j (by omega) hjp ((horder k hkl).symm.trans hk)
    omega
  have hjShortNoP : ∀ x ∈ r.support, ¬ G.Adj (p.getVert j) x := fun x hx =>
    I.short_not_adj_precolored (fun h => hjR ((hPv _).1 h)) ((hPv x).2 hx) hbShort
  have hjlast : j+2 ≤ p.length := by
    by_contra h
    have hj : j=p.length-1 := by omega
    have hja : G.Adj (p.getVert j) a := by
      have h := p.adj_getVert_succ hjp
      simpa only [show j+1=p.length by omega,Walk.getVert_length] using h
    exact hjShortNoP a r.start_mem_support hja
  obtain ⟨w,hw,hwl,hwo,hwf,hwr⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot i (by omega)
  have hw0 : p.getVert i = r.getVert i := (horder i (by omega)).symm
  have hwj : w.getVert (j-i) = p.getVert j := by
    rw [hwo _ (by omega),Nat.add_sub_of_le (by omega : i ≤ j),walkCycleVertices_nat_le p (by omega)]
  let q : G.Walk (w.getVert (j-i)) (p.getVert i) :=
    .cons (show G.Adj (w.getVert (j-i)) v2 from by rw [hwj]; exact hzj.symm)
      (.cons huz.symm (.cons (show G.Adj u (p.getVert i) from by rw [hw0]; exact hui) .nil))
  have hqmem : ∀ x, x ∈ q.support ↔ x=p.getVert j ∨ x=v2 ∨ x=u ∨ x=r.getVert i := by
    intro x; simp only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false,hwj,hw0]
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true,hwj,hw0]
    have hju : p.getVert j ≠ u := fun h => hu (h ▸ (hverts _).1 (p.getVert_mem_support j))
    exact ⟨⟨hzj.ne.symm,hju,fun h => hjR (h ▸ r.getVert_mem_support i)⟩,
      ⟨⟨huz.ne.symm,fun h => hzR (h.symm ▸ r.getVert_mem_support i)⟩,hui.ne⟩⟩
  have hInner : ∀ k, 0 < k → k < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert k) := by
    intro k hk hkl
    rcases (by change k < 3 at hkl; omega : k=1 ∨ k=2) with he | he
    · subst k; exact hz
    · subst k; exact hu
  obtain ⟨S,T,hSs,hTs,hcover,hinter,hedges,hSc,hTc,hSC,hkeep,⟨oS,hSface⟩,⟨M,oT,hTface⟩⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG w hw hwf hwr (j-i) q hq (by omega) (by omega)
      (by change 0 < 3; omega) (by change 3 ≤ 3; omega) hInner
  have hSep : ∀ z ∈ q.support, z ∈ S ∧ z ∈ T := by
    intro z hz
    have he : z ∈ S ∩ T := by rw [hinter]; exact hz
    exact he
  have hArc : ∀ z, z ∈ cycleInterval (walkCycleVertices w) 1 (j-i-2) →
      ∃ k : ℕ, i < k ∧ k < j ∧ p.getVert k = z := by
    intro z hz
    obtain ⟨l,hl,hlz⟩ := hz
    rw [walkCycleVertices_nat_le w (by omega : 1+l ≤ w.length),hwo (1+l) (by omega),
      walkCycleVertices_nat_le p (by omega : i+(1+l) ≤ p.length)] at hlz
    exact ⟨i+(1+l),by omega,by omega,hlz⟩
  have hTailS : ∀ z ∈ (r.drop i).support, z ∈ S := by
    intro z hz
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    rw [Walk.drop_getVert] at hk
    have hki : i+k ≤ r.length := by rw [Walk.drop_length] at hkl; omega
    apply hSC z ∘ Or.inl
    apply Walk.mem_support_iff_exists_getVert.2
    refine ⟨k,?_,?_⟩
    · rw [Walk.take_getVert,Nat.min_eq_right (by omega : k ≤ j-i),hwo k (by omega),
        walkCycleVertices_nat_le p (by omega),← horder (i+k) hki]
      exact hk
    · rw [Walk.take_length,Nat.min_eq_left (by omega : j-i ≤ w.length)]; omega
  have hOldS : ∀ z, z ∈ I.precolor.vertices → z ∈ S → z ∈ (r.drop i).support := by
    intro z hz hzS
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hz)
    have hik : i ≤ k := by
      by_contra h
      have hzNotArc : z ∉ cycleInterval (walkCycleVertices w) 1 (j-i-2) := by
        intro hzarc
        obtain ⟨l,hil,hlj,hlz⟩ := hArc z hzarc
        have he := hidx k l (by omega) (by omega) ((horder k hkl).symm.trans (hk.trans hlz.symm))
        omega
      have hzT := hkeep z (I.on_outer z hz) hzNotArc
      have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS,hzT⟩; rwa [hinter] at h
      rcases (hqmem z).1 hzq with hxj | hxz | hxu | hxi
      · exact hjR (hxj ▸ (hPv z).1 hz)
      · exact hzR (hxz ▸ (hPv z).1 hz)
      · exact huR (hxu ▸ (hPv z).1 hz)
      · have he := hr.getVert_injOn hkl (show i ≤ r.length from by omega) (hk.trans hxi)
        omega
    exact Walk.mem_support_iff_exists_getVert.2 ⟨k-i,by rw [Walk.drop_getVert,Nat.add_sub_of_le hik]; exact hk,
      by rw [Walk.drop_length]; omega⟩
  have hPconn : ConnSet G {z | z ∈ I.precolor.vertices ∧ z ∈ S} := by
    have heq : {z | z ∈ I.precolor.vertices ∧ z ∈ S} = {z | z ∈ (r.drop i).support} := by
      ext z
      exact ⟨fun h => hOldS z h.1 h.2,fun h => ⟨(hPv z).2 ((Walk.isSubwalk_drop r i).support_subset h),hTailS z h⟩⟩
    rw [heq]; exact walk_support_connSet (r.drop i)
  have hOldFaceS : ∀ z : S, OnOuterFace I.embedding I.outer z.1 →
      OnOuterFace (inducedPlaneMap I.embedding S) oS z := by
    intro z hz
    apply (hSface z).2
    by_cases hzArc : z.1 ∈ cycleInterval (walkCycleVertices w) 1 (j-i-2)
    · obtain ⟨l,hl,hlz⟩ := hzArc
      apply Or.inl
      apply Walk.mem_support_iff_exists_getVert.2
      refine ⟨1+l,?_,?_⟩
      · rw [Walk.take_getVert,Nat.min_eq_right (by omega : 1+l ≤ j-i)]
        rwa [walkCycleVertices_nat_le w (by omega : 1+l ≤ w.length)] at hlz
      · rw [Walk.take_length,Nat.min_eq_left (by omega : j-i ≤ w.length)]; omega
    · have hzq : z.1 ∈ q.support := by
        have h : z.1 ∈ S ∩ T := ⟨z.2,hkeep z.1 hz hzArc⟩
        rwa [hinter] at h
      exact Or.inr hzq
  obtain ⟨cS,hcS⟩ := I.colourable_induced_retaining_connected_prescription
    S (inducedPlaneMap I.embedding S) oS hSc.preconnected hPconn hOldFaceS hSs hsmall
  have huS : u ∈ S := (hSep u ((hqmem u).2 (Or.inr (Or.inr (Or.inl rfl))))).1
  have hzS : v2 ∈ S := (hSep v2 ((hqmem v2).2 (Or.inr (Or.inl rfl)))).1
  have hjS : p.getVert j ∈ S := (hSep _ ((hqmem _).2 (Or.inl rfl))).1
  have hiS : r.getVert i ∈ S := (hSep _ ((hqmem _).2 (Or.inr (Or.inr (Or.inr rfl))))).1
  have hcSi : cS ⟨r.getVert i,hiS⟩ = I.prescribed (r.getVert i) := by
    apply Finset.mem_singleton.1
    simpa only [I.singleton _ ((hPv _).2 (r.getVert_mem_support i))] using hcS ⟨r.getVert i,hiS⟩
  let f : V → C := fun x => if x=u then cS ⟨u,huS⟩ else
    if x=v2 then cS ⟨v2,hzS⟩ else if x=p.getVert j then cS ⟨p.getVert j,hjS⟩ else I.prescribed x
  have hfOld : ∀ x ∈ r.support, f x = I.prescribed x := by
    intro x hx
    simp only [f,ite_eq_right (fun (h:x=u) => huR (h ▸ hx)),
      ite_eq_right (fun (h:x=v2) => hzR (h ▸ hx)),ite_eq_right (fun (h:x=p.getVert j) => hjR (h ▸ hx))]
  have hfu : f u = cS ⟨u,huS⟩ := by simp only [f,ite_true]
  have hfz : f v2 = cS ⟨v2,hzS⟩ := by simp only [f,ite_eq_right huz.ne.symm,ite_true]
  have hju : p.getVert j ≠ u := fun h => hu (h ▸ (hverts _).1 (p.getVert_mem_support j))
  have hfj : f (p.getVert j) = cS ⟨p.getVert j,hjS⟩ := by
    simp only [f,ite_eq_right hju,ite_eq_right hzj.ne.symm,ite_true]
  let v := (((r.take i).concat hui.symm).concat huz).concat hzj
  have hvmem : ∀ x, x ∈ v.support ↔ x ∈ (r.take i).support ∨ x=u ∨ x=v2 ∨ x=p.getVert j := by
    intro x; simp only [v,Walk.support_concat,List.mem_append,List.mem_singleton]; tauto
  have hv : v.IsPath := by
    have h1 := (hr.take i).concat (fun h => huR ((Walk.isSubwalk_take r i).support_subset h)) hui.symm
    have h2 := h1.concat (by
      simp only [Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
      exact ⟨fun h => hzR ((Walk.isSubwalk_take r i).support_subset h),huz.ne.symm⟩) huz
    apply h2.concat ?_ hzj
    simp only [Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨fun h => hjR ((Walk.isSubwalk_take r i).support_subset h),hju⟩,hzj.ne.symm⟩
  have hvlen : v.length ≤ 5 := by simp only [v,Walk.length_concat,Walk.take_length]; omega
  have hvch : v.IsChordless := by
    apply five_edge_path_isChordless_of_no_long_chords I.girth v hv hvlen
    intro k l hkl hll hAdj
    have hvlength : v.length=i+3 := by simp only [v,Walk.length_concat,Walk.take_length,Nat.min_eq_left (by omega : i ≤ r.length)]
    have hcases : (k=0 ∧ l=i+3) ∨ (i=2 ∧ k=0 ∧ l=4) ∨ (i=2 ∧ k=1 ∧ l=5) := by omega
    have hbP : p.getVert j ∉ I.precolor.vertices := fun h => hjR ((hPv _).1 h)
    have hbNoP : ∀ x ∈ r.support, ¬ G.Adj (p.getVert j) x := fun x hx =>
      I.short_not_adj_precolored hbP ((hPv x).2 hx) hbShort
    rcases hcases with ⟨hk,hl⟩ | ⟨hi2,hk,hl⟩ | ⟨hi2,hk,hl⟩
    · rw [hk,hl,← hvlength,Walk.getVert_zero,Walk.getVert_length] at hAdj
      exact hbNoP a r.start_mem_support hAdj.symm
    · subst i
      have hv0 : v.getVert 0 = a := Walk.getVert_zero v
      have hv4 : v.getVert 4 = v2 := by
        simp [v,Walk.concat_eq_append,Walk.getVert_append,Nat.min_eq_left (show 2 ≤ r.length from by omega)]
      rw [hk,hl,hv0,hv4] at hAdj
      have hba : p.getVert j ≠ a := fun h => hjR (by rw [h]; exact r.start_mem_support)
      exact I.no_interior_boundary_pair_at_initial_vertex r hr hn hP (by omega) hbad hsmall
        v2 (p.getVert j) hz ((hverts _).1 (p.getVert_mem_support j)) hba hAdj.symm hzj
    · subst i
      have hv1 : v.getVert 1 = r.getVert 1 := by
        simp [v,Walk.concat_eq_append,Walk.getVert_append,Nat.min_eq_left (show 2 ≤ r.length from by omega)]
      rw [hk,hl,show 5=v.length by omega,Walk.getVert_length,hv1] at hAdj
      exact hbNoP _ (r.getVert_mem_support 1) hAdj.symm
  have hprefixT : ∀ z ∈ (r.take i).support, z ∈ T := by
    intro z hz
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    rw [Walk.take_length,Nat.min_eq_left (by omega : i ≤ r.length)] at hkl
    rw [Walk.take_getVert,Nat.min_eq_right hkl] at hk
    apply hkeep z (I.on_outer z ((hPv z).2 ((Walk.isSubwalk_take r i).support_subset hz)))
    intro hzarc
    obtain ⟨l,hil,hlj,hlz⟩ := hArc z hzarc
    have he := hidx k l (by omega) (by omega) ((horder k (by omega)).symm.trans (hk.trans hlz.symm))
    omega
  have hvT : ∀ x ∈ v.support, x ∈ T := by
    intro x hx
    rcases (hvmem x).1 hx with hx | hxu | hxz | hxj
    · exact hprefixT x hx
    · exact hxu ▸ (hSep u ((hqmem u).2 (Or.inr (Or.inr (Or.inl rfl))))).2
    · exact hxz ▸ (hSep v2 ((hqmem v2).2 (Or.inr (Or.inl rfl)))).2
    · exact hxj ▸ (hSep _ ((hqmem _).2 (Or.inl rfl))).2
  have hOldT : ∀ x ∈ T, x ∈ I.precolor.vertices → x ∈ v.support := by
    intro x hxT hxP
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv x).1 hxP)
    by_cases hki : k ≤ i
    · apply (hvmem x).2 ∘ Or.inl
      exact Walk.mem_support_iff_exists_getVert.2 ⟨k,by rw [Walk.take_getVert,Nat.min_eq_right hki]; exact hk,
        by rw [Walk.take_length,Nat.min_eq_left (by omega : i ≤ r.length)]; exact hki⟩
    · have hxS : x ∈ S := hTailS x (Walk.mem_support_iff_exists_getVert.2 ⟨k-i,
        by rw [Walk.drop_getVert,Nat.add_sub_of_le (by omega : i ≤ k)]; exact hk,
        by rw [Walk.drop_length]; omega⟩)
      have hxq : x ∈ q.support := by have h : x ∈ S ∩ T := ⟨hxS,hxT⟩; rwa [hinter] at h
      rcases (hqmem x).1 hxq with hxj | hxz | hxu | hxi
      · exact (hvmem x).2 (Or.inr (Or.inr (Or.inr hxj)))
      · exact (hvmem x).2 (Or.inr (Or.inr (Or.inl hxz)))
      · exact (hvmem x).2 (Or.inr (Or.inl hxu))
      · have he := hr.getVert_injOn hkl (show i ≤ r.length from by omega) (hk.trans hxi)
        omega
  have hfList : ∀ x ∈ v.support, f x ∈ I.lists x := by
    intro x hx
    rcases (hvmem x).1 hx with hx | hxu | hxz | hxj
    · rw [hfOld x ((Walk.isSubwalk_take r i).support_subset hx),I.singleton x ((hPv x).2 ((Walk.isSubwalk_take r i).support_subset hx))]
      exact Finset.mem_singleton_self _
    · rw [hxu,hfu]; exact hcS ⟨u,huS⟩
    · rw [hxz,hfz]; exact hcS ⟨v2,hzS⟩
    · rw [hxj,hfj]; exact hcS ⟨p.getVert j,hjS⟩
  have hfProper : ∀ x ∈ v.support, ∀ y ∈ v.support, G.Adj x y → f x ≠ f y := by
    intro x hx y hy hxy
    have he := hvch.mem_edges hx hy hxy
    simp only [v,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at he
    have hsym : ∀ z z', s(x,y)=s(z,z') → f z ≠ f z' → f x ≠ f y := by
      intro z z' he hne
      rcases Sym2.eq_iff.1 he with h | h
      · simpa only [h.1,h.2] using hne
      · simpa only [h.1,h.2] using hne.symm
    rcases he with ((he | he) | he) | he
    · have hxR := (Walk.isSubwalk_take r i).support_subset ((r.take i).fst_mem_support_of_mem_edges he)
      have hyR := (Walk.isSubwalk_take r i).support_subset ((r.take i).snd_mem_support_of_mem_edges he)
      rw [hfOld x hxR,hfOld y hyR]
      exact I.proper_on_precolored_vertices ((hPv x).2 hxR) ((hPv y).2 hyR) hxy
    · apply hsym _ _ he
      rw [hfOld _ (r.getVert_mem_support i),hfu,← hcSi]
      exact cS.valid (show (G.induce S).Adj ⟨r.getVert i,hiS⟩ ⟨u,huS⟩ from hui.symm)
    · apply hsym _ _ he
      rw [hfu,hfz]
      exact cS.valid (show (G.induce S).Adj ⟨u,huS⟩ ⟨v2,hzS⟩ from huz)
    · apply hsym _ _ he
      rw [hfz,hfj]
      exact cS.valid (show (G.induce S).Adj ⟨v2,hzS⟩ ⟨p.getVert j,hjS⟩ from hzj)
  obtain ⟨cT,hcT,hcTfix⟩ := I.colourable_induced_with_compatible_short_ended_path T M oT hTc.preconnected
    v hv hvlen hvch hvT hOldT u v2 huz
    (by
      intro x hx
      rcases (hvmem x).1 hx with hx | hxu | hxz | hxj
      · exact Or.inl ((hPv x).2 ((Walk.isSubwalk_take r i).support_subset hx))
      · exact Or.inr (Or.inr (Or.inl hxu))
      · exact Or.inr (Or.inr (Or.inr hxz))
      · exact Or.inr (Or.inl (hxj ▸ hbShort)))
    (fun h => hjR (h ▸ r.start_mem_support))
    (by simp only [I.singleton a ((hPv a).2 r.start_mem_support),Finset.card_singleton]; omega)
    hbShort f hfList hfProper
    (by
      intro x hx
      rcases (hvmem x.1).1 hx with hx | hxu | hxz | hxj
      · exact hTface x (Or.inl (I.on_outer x.1 ((hPv x.1).2 ((Walk.isSubwalk_take r i).support_subset hx))))
      · exact hTface x (Or.inr ((hqmem x.1).2 (Or.inr (Or.inr (Or.inl hxu)))))
      · exact hTface x (Or.inr ((hqmem x.1).2 (Or.inr (Or.inl hxz))))
      · exact hTface x (Or.inr ((hqmem x.1).2 (Or.inl hxj))))
    (fun x hx => hTface x (Or.inl hx)) hTs hsmall
  apply hbad
  have hcover' : ∀ x, x ∈ S ∨ x ∈ T := by
    intro x
    have h : x ∈ S ∪ T := by rw [hcover]; trivial
    exact h
  refine glue_induced_colourings S T I.lists hcover' hedges cS cT hcS hcT ?_
  intro x hxS hxT
  have hxq : x ∈ q.support := by have h : x ∈ S ∩ T := ⟨hxS,hxT⟩; rwa [hinter] at h
  have hxv : x ∈ v.support := by
    apply (hvmem x).2
    rcases (hqmem x).1 hxq with hxj | hxz | hxu | hxi
    · exact Or.inr (Or.inr (Or.inr hxj))
    · exact Or.inr (Or.inr (Or.inl hxz))
    · exact Or.inr (Or.inl hxu)
    · exact Or.inl (hxi ▸ (r.take i).end_mem_support)
  rw [hcTfix ⟨x,hxT⟩ hxv]
  rcases (hqmem x).1 hxq with hxj | hxz | hxu | hxi
  · subst x; exact hfj.symm
  · subst x; exact hfz.symm
  · subst x; exact hfu.symm
  · rw [hfOld x ((hPv x).1 (hxi ▸ (hPv _).2 (r.getVert_mem_support i)))]
    exact Finset.mem_singleton.1 (by simpa only [I.singleton x (hxi ▸ (hPv _).2 (r.getVert_mem_support i))] using hcS ⟨x,hxS⟩)

end Thomassen.BoundaryInstance
