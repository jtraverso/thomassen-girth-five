/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RetainedPrescription

/-! Interior two-path cuts through a short end of the old prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A mixed interior two-path is eliminated when its prescribed endpoint
leaves at most three old prescribed vertices on the initial side, and the
unprescribed endpoint is not adjacent to the initial prescribed vertex.
Both actual pieces, their faces and every short-list attachment are derived. -/
theorem colourable_of_mixed_two_path_short_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (i j : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (hrj : r.length < j) (hjp : j < p.length)
    (hba : ¬ G.Adj a (p.getVert j))
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert i)) (huj : G.Adj u (p.getVert j))
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
  have hjR : p.getVert j ∉ r.support := by
    intro h
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 h
    have he := hidx k j (by omega) hjp ((horder k hkl).symm.trans hk)
    omega
  obtain ⟨w,hw,hwl,hwo,hwf,hwr⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot i (by omega)
  have hw0 : p.getVert i = r.getVert i := (horder i (by omega)).symm
  have hwj : w.getVert (j-i) = p.getVert j := by
    rw [hwo _ (by omega),Nat.add_sub_of_le (by omega : i ≤ j),walkCycleVertices_nat_le p (by omega)]
  let q : G.Walk (w.getVert (j-i)) (p.getVert i) :=
    .cons (show G.Adj (w.getVert (j-i)) u from by rw [hwj]; exact huj.symm)
      (.cons (show G.Adj u (p.getVert i) from by rw [hw0]; exact hui) .nil)
  have hqmem : ∀ z, z ∈ q.support ↔ z=p.getVert j ∨ z=u ∨ z=r.getVert i := by
    intro z; simp only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false,hwj,hw0]
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true,hwj,hw0]
    exact ⟨⟨huj.ne.symm,fun h => hjR (h ▸ r.getVert_mem_support i)⟩,hui.ne⟩
  have hInner : ∀ k, 0 < k → k < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert k) := by
    intro k hk hkl
    have hk1 : k=1 := by change k < 2 at hkl; omega
    subst k; exact hu
  obtain ⟨S,T,hSs,hTs,hcover,hinter,hedges,hSc,hTc,hSC,hkeep,⟨oS,hSface⟩,⟨M,oT,hTface⟩⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG w hw hwf hwr (j-i) q hq (by omega) (by omega)
      (by change 0 < 2; omega) (by change 2 ≤ 3; omega) hInner
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
      rcases (hqmem z).1 hzq with hzj | hzu | hzi
      · exact hjR (hzj ▸ (hPv z).1 hz)
      · exact huR (hzu ▸ (hPv z).1 hz)
      · have he := hr.getVert_injOn hkl (show i ≤ r.length from by omega) (hk.trans hzi)
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
  have huS : u ∈ S := (hSep u ((hqmem u).2 (Or.inr (Or.inl rfl)))).1
  have hjS : p.getVert j ∈ S := (hSep _ ((hqmem _).2 (Or.inl rfl))).1
  have hiS : r.getVert i ∈ S := (hSep _ ((hqmem _).2 (Or.inr (Or.inr rfl)))).1
  have hcSi : cS ⟨r.getVert i,hiS⟩ = I.prescribed (r.getVert i) := by
    apply Finset.mem_singleton.1
    simpa only [I.singleton _ ((hPv _).2 (r.getVert_mem_support i))] using hcS ⟨r.getVert i,hiS⟩
  let f : V → C := fun z => if z=u then cS ⟨u,huS⟩ else
    if z=p.getVert j then cS ⟨p.getVert j,hjS⟩ else I.prescribed z
  have hfOld : ∀ z ∈ r.support, f z = I.prescribed z := by
    intro z hz
    simp only [f,ite_eq_right (fun (h:z=u) => huR (h ▸ hz)),
      ite_eq_right (fun (h:z=p.getVert j) => hjR (h ▸ hz))]
  have hfu : f u = cS ⟨u,huS⟩ := by simp only [f,ite_true]
  have hfj : f (p.getVert j) = cS ⟨p.getVert j,hjS⟩ := by
    simp only [f,ite_eq_right huj.ne.symm,ite_true]
  let v := ((r.take i).concat hui.symm).concat huj
  have hvmem : ∀ z, z ∈ v.support ↔ z ∈ (r.take i).support ∨ z=u ∨ z=p.getVert j := by
    intro z; simp only [v,Walk.support_concat,List.mem_append,List.mem_singleton]; tauto
  have hv : v.IsPath := by
    apply ((hr.take i).concat (fun h => huR ((Walk.isSubwalk_take r i).support_subset h)) hui.symm).concat ?_ huj
    simp only [Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
    exact ⟨fun h => hjR ((Walk.isSubwalk_take r i).support_subset h),huj.ne.symm⟩
  have hvlen : v.length ≤ 4 := by simp only [v,Walk.length_concat,Walk.take_length]; omega
  have hvch := four_edge_path_isChordless I.girth v hv hvlen hba
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
  have hvT : ∀ z ∈ v.support, z ∈ T := by
    intro z hz
    rcases (hvmem z).1 hz with hz | hzu | hzj
    · exact hprefixT z hz
    · exact hzu ▸ (hSep u ((hqmem u).2 (Or.inr (Or.inl rfl)))).2
    · exact hzj ▸ (hSep _ ((hqmem _).2 (Or.inl rfl))).2
  have hOldT : ∀ z ∈ T, z ∈ I.precolor.vertices → z ∈ v.support := by
    intro z hzT hzP
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hzP)
    by_cases hki : k ≤ i
    · apply (hvmem z).2 ∘ Or.inl
      exact Walk.mem_support_iff_exists_getVert.2 ⟨k,by rw [Walk.take_getVert,Nat.min_eq_right hki]; exact hk,
        by rw [Walk.take_length,Nat.min_eq_left (by omega : i ≤ r.length)]; exact hki⟩
    · have hzS : z ∈ S := hTailS z (Walk.mem_support_iff_exists_getVert.2 ⟨k-i,
        by rw [Walk.drop_getVert,Nat.add_sub_of_le (by omega : i ≤ k)]; exact hk,
        by rw [Walk.drop_length]; omega⟩)
      have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS,hzT⟩; rwa [hinter] at h
      rcases (hqmem z).1 hzq with hzj | hzu | hzi
      · exact (hvmem z).2 (Or.inr (Or.inr hzj))
      · exact (hvmem z).2 (Or.inr (Or.inl hzu))
      · have he := hr.getVert_injOn hkl (show i ≤ r.length from by omega) (hk.trans hzi)
        omega
  have hfList : ∀ z ∈ v.support, f z ∈ I.lists z := by
    intro z hz
    rcases (hvmem z).1 hz with hz | hzu | hzj
    · rw [hfOld z ((Walk.isSubwalk_take r i).support_subset hz),I.singleton z ((hPv z).2 ((Walk.isSubwalk_take r i).support_subset hz))]
      exact Finset.mem_singleton_self _
    · rw [hzu,hfu]; exact hcS ⟨u,huS⟩
    · rw [hzj,hfj]; exact hcS ⟨p.getVert j,hjS⟩
  have hfProper : ∀ z ∈ v.support, ∀ z' ∈ v.support, G.Adj z z' → f z ≠ f z' := by
    intro z hz z' hz' hzz'
    have he := hvch.mem_edges hz hz' hzz'
    simp only [v,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at he
    have hsym : ∀ x y, s(z,z')=s(x,y) → f x ≠ f y → f z ≠ f z' := by
      intro x y he hne
      rcases Sym2.eq_iff.1 he with h | h
      · simpa only [h.1,h.2] using hne
      · simpa only [h.1,h.2] using hne.symm
    rcases he with (he | he) | he
    · have hzR := (Walk.isSubwalk_take r i).support_subset ((r.take i).fst_mem_support_of_mem_edges he)
      have hzR' := (Walk.isSubwalk_take r i).support_subset ((r.take i).snd_mem_support_of_mem_edges he)
      rw [hfOld z hzR,hfOld z' hzR']
      exact I.proper_on_precolored_vertices ((hPv z).2 hzR) ((hPv z').2 hzR') hzz'
    · apply hsym _ _ he
      rw [hfOld _ (r.getVert_mem_support i),hfu,← hcSi]
      exact cS.valid (show (G.induce S).Adj ⟨r.getVert i,hiS⟩ ⟨u,huS⟩ from hui.symm)
    · apply hsym _ _ he
      rw [hfu,hfj]
      exact cS.valid (show (G.induce S).Adj ⟨u,huS⟩ ⟨p.getVert j,hjS⟩ from huj)
  obtain ⟨cT,hcT,hcTfix⟩ := I.colourable_induced_with_compatible_edge_star_path T M oT hTc.preconnected
    v hv hvlen hvch hvT hOldT u (p.getVert j) huj
    (by
      intro z hz
      rcases (hvmem z).1 hz with hz | hz | hz
      · exact Or.inl ((hPv z).2 ((Walk.isSubwalk_take r i).support_subset hz))
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr hz))
    ((hPv a).2 r.start_mem_support) f hfList hfProper
    (by
      intro z hz
      rcases (hvmem z.1).1 hz with hz | hz | hz
      · exact hTface z (Or.inl (I.on_outer z.1 ((hPv z.1).2 ((Walk.isSubwalk_take r i).support_subset hz))))
      · exact hTface z (Or.inr ((hqmem z.1).2 (Or.inr (Or.inl hz))))
      · exact hTface z (Or.inr ((hqmem z.1).2 (Or.inl hz))))
    (fun z hz => hTface z (Or.inl hz)) hTs hsmall
  apply hbad
  have hcover' : ∀ z, z ∈ S ∨ z ∈ T := by
    intro z
    have h : z ∈ S ∪ T := by rw [hcover]; trivial
    exact h
  refine glue_induced_colourings S T I.lists hcover' hedges cS cT hcS hcT ?_
  intro z hzS hzT
  have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS,hzT⟩; rwa [hinter] at h
  have hzv : z ∈ v.support := by
    apply (hvmem z).2
    rcases (hqmem z).1 hzq with hzj | hzu | hzi
    · exact Or.inr (Or.inr hzj)
    · exact Or.inr (Or.inl hzu)
    · exact Or.inl (hzi ▸ (r.take i).end_mem_support)
  rw [hcTfix ⟨z,hzT⟩ hzv]
  rcases (hqmem z).1 hzq with hzj | hzu | hzi
  · subst z; exact hfj.symm
  · subst z; exact hfu.symm
  · rw [hfOld z ((hPv z).1 (hzi ▸ (hPv _).2 (r.getVert_mem_support i)))]
    exact Finset.mem_singleton.1 (by simpa only [I.singleton z (hzi ▸ (hPv _).2 (r.getVert_mem_support i))] using hcS ⟨z,hzS⟩)

/-- The short-prefix mixed reduction applies to the arbitrary original face
in either orientation. Native facial placement of the unprescribed endpoint
is recovered internally. -/
theorem colourable_of_mixed_two_path_short_prefix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hba : ¬ G.Adj a b) (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert i)) (hub : G.Adj u b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  have hdo : ∀ (J : BoundaryInstance G C), J.lists = I.lists → J.precolor = I.precolor →
      OnOuterFace J.embedding J.outer b → (¬ OnOuterFace J.embedding J.outer u) →
      ∀ (p : G.Walk a a) (hp : p.IsCycle),
      IsFacialCycleAlong J.embedding (walk_isCycleMap p hp) Set.univ →
      SameCycle J.embedding.facePerm J.outer (walkArcRoot p hp) →
      (∀ k ≤ r.length, r.getVert k = p.getVert k) → ListColourable G J.lists := by
    intro J hJL hJP hbJ huJ p hp hface hroot horder
    have hbR : b ∉ r.support := by
      intro h
      apply hbP
      simpa only [hP,BoundaryPrecolor.vertices,List.mem_toFinset] using h
    have hbrange : b ∈ Set.range (walkCycleVertices p) := by
      rw [walkCycleVertices_range p hp]
      exact (native_facial_cycle_support_iff J.embedding J.outer p hp hface hroot b).2 hbJ
    have hplen := hp.three_le_length
    let : NeZero p.length := ⟨by omega⟩
    obtain ⟨k,hk⟩ := hbrange
    have hkp : k.val < p.length := ZMod.val_lt k
    have hkv : p.getVert k.val = b := hk
    have hrk : r.length < k.val := by
      by_contra h
      apply hbR
      rw [← hkv,← horder k.val (by omega)]
      exact r.getVert_mem_support _
    exact J.colourable_of_mixed_two_path_short_prefix hG p hp hface hroot r hr hn
      (hJP.trans hP) horder i k.val hi hi2 hir hrk hkp
      (by rwa [hkv]) u huJ hui (by rwa [hkv]) hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact hdo I rfl rfl hb hu p hp hface hroot horder
  · exact hdo I.mirror rfl rfl ((mirror_onOuterFace_iff I.embedding I.outer b).2 hb)
      (fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h)) p hp hface hroot horder

/-- The same mixed reduction is available at the terminal end of the old
prescription. Reversal preserves every old list, edge and singleton colour. -/
theorem colourable_of_mixed_two_path_short_suffix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbt : ¬ G.Adj t b) (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hui : G.Adj u (r.getVert (r.length-i))) (hub : G.Adj u b)
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
  apply J.colourable_of_mixed_two_path_short_prefix_arbitrary_face r.reverse hr.reverse hnrev rfl
    i hi hi2 (by simpa only [Walk.length_reverse] using hir) b hb
    (fun h => hbP ((hPv b).1 h)) hbt u hu ?_ hub hsmall
  simpa only [Walk.getVert_reverse] using hui

end Thomassen.BoundaryInstance
