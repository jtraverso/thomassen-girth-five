/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CompatiblePathStar
public import Thomassen.OrientedPrescription

/-! The central two-path across a six-vertex prescribed path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The central remaining two-path with both ends internal to a six-vertex
prescription. The five-cycle on positions 1--4 is coloured compatibly with the
exterior five-vertex path. Old short neighbours of the new interior vertex are
handled by the proved branching-prescription extension. -/
theorem colourable_of_central_prescribed_two_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 5)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hu1 : G.Adj u (r.getVert 1)) (hu4 : G.Adj u (r.getVert 4))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hplen : 9 ≤ p.length := by
    have h := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
    omega
  have huR : u ∉ r.support := fun h => hu (I.on_outer u ((hPv u).2 h))
  have hinj : ∀ i j : ℕ, i ≤ 5 → j ≤ 5 → i ≠ j → r.getVert i ≠ r.getVert j := by
    intro i j hi hj hij he
    exact hij (hr.getVert_injOn (by change i ≤ r.length; omega) (by change j ≤ r.length; omega) he)
  have hUnique : ∀ z ∈ r.support, G.Adj u z → z = r.getVert 1 ∨ z = r.getVert 4 := by
    intro z hz huz
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    subst z
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5) with h | h | h | h | h | h
    · exact (neighbors_nonadjacent I.girth hu1.symm (r.adj_getVert_succ (by omega : 0 < r.length)).symm
        (by simpa only [h] using huz)).elim
    · exact Or.inl (congrArg r.getVert h)
    · exact (neighbors_nonadjacent I.girth hu1.symm (r.adj_getVert_succ (by omega : 1 < r.length))
        (by simpa only [h] using huz)).elim
    · exact (neighbors_nonadjacent I.girth hu4.symm (r.adj_getVert_succ (by omega : 3 < r.length)).symm
        (by simpa only [h] using huz)).elim
    · exact Or.inr (congrArg r.getVert h)
    · exact (neighbors_nonadjacent I.girth hu4.symm (r.adj_getVert_succ (by omega : 4 < r.length))
        (by simpa only [h] using huz)).elim
  obtain ⟨cu,hcu,hcuN⟩ : ∃ col ∈ I.lists u,
      col ∉ ({I.prescribed (r.getVert 1),I.prescribed (r.getVert 4)} : Finset C) :=
    Finset.exists_mem_notMem_of_card_lt_card
      (Finset.card_le_two.trans_lt (by have := I.interior_lists u hu; omega))
  have hcu1 : cu ≠ I.prescribed (r.getVert 1) := fun h => hcuN (Finset.mem_insert.2 (Or.inl h))
  have hcu4 : cu ≠ I.prescribed (r.getVert 4) := fun h => hcuN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let f : V → C := fun z => if z = u then cu else I.prescribed z
  have hfOld : ∀ z ∈ r.support, f z = I.prescribed z := by
    intro z hz
    change (if z=u then cu else I.prescribed z) = I.prescribed z
    exact ite_eq_right (fun (h : z=u) => huR (h ▸ hz))
  have hfList : ∀ z, z ∈ r.support ∨ z = u → f z ∈ I.lists z := by
    intro z hz
    rcases hz with hz | rfl
    · rw [hfOld z hz,I.singleton z ((hPv z).2 hz)]; exact Finset.mem_singleton_self _
    · simpa only [f,ite_true] using hcu
  have hfProper : ∀ z, z ∈ r.support ∨ z = u → ∀ w, w ∈ r.support ∨ w = u →
      G.Adj z w → f z ≠ f w := by
    intro z hz w hw hzw
    rcases hz with hz | hzu <;> rcases hw with hw | hwu
    · rw [hfOld z hz,hfOld w hw]
      exact I.proper_on_precolored_vertices ((hPv z).2 hz) ((hPv w).2 hw) hzw
    · have hwf : f w = cu := by simp only [f,hwu,ite_true]
      rw [hfOld z hz,hwf]
      rcases hUnique z hz (hwu ▸ hzw.symm) with h | h
      · simpa only [h] using hcu1.symm
      · simpa only [h] using hcu4.symm
    · have hzf : f z = cu := by simp only [f,hzu,ite_true]
      rw [hfOld w hw,hzf]
      rcases hUnique w hw (hzu ▸ hzw) with h | h
      · simpa only [h] using hcu1
      · simpa only [h] using hcu4
    · exact (hzw.ne (hzu.trans hwu.symm)).elim
  obtain ⟨w,hw,hwl,hwo,hwf,hwr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot 1 (by omega)
  have hwOrd : ∀ i ≤ 4, w.getVert i = r.getVert (i+1) := by
    intro i hi
    rw [hwo i (by omega),walkCycleVertices_nat_le p (by omega)]
    rw [Nat.add_comm 1 i]
    exact (horder (i+1) (by omega)).symm
  have hw0 : p.getVert 1 = r.getVert 1 := by simpa only [Walk.getVert_zero] using hwOrd 0 (by omega)
  have hw3 : w.getVert 3 = r.getVert 4 := hwOrd 3 (by omega)
  let q : G.Walk (w.getVert 3) (p.getVert 1) :=
    .cons (show G.Adj (w.getVert 3) u from by rw [hw3]; exact hu4.symm)
      (.cons (show G.Adj u (p.getVert 1) from by rw [hw0]; exact hu1) .nil)
  have hqmem : ∀ z, z ∈ q.support ↔ z = r.getVert 4 ∨ z = u ∨ z = r.getVert 1 := by
    intro z; simp only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false,hw3,hw0]
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true,hw3,hw0]
    exact ⟨⟨hu4.ne.symm,hinj 4 1 (by omega) (by omega) (by omega)⟩,hu1.ne⟩
  have hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert i) := by
    intro i hi hil
    have hi1 : i=1 := by change i < 2 at hil; omega
    subst i; exact hu
  obtain ⟨S,T,hSs,hTs,hcover,hinter,hedges,_,hTc,hSC,hkeep,⟨oS,hSface⟩,⟨M,oT,hTface⟩⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG w hw hwf hwr 3 q hq (by omega) (by omega)
      (by change 0 < 2; omega) (by change 2 ≤ 3; omega) hInner
  let s := spliceFacePath w 3 q
  have hs : s.IsCycle := spliceFacePath_isCycle w hw 3 q hq (by omega) (by omega)
    (closing_path_intersection_of_interior I.embedding I.outer w hw hwf hwr 3 q hInner)
  have hsLen : s.length ≤ 6 := by rw [spliceFacePath_length w 3 q (by omega)]; change 3+2 ≤ 6; omega
  have hsMem : ∀ z, z ∈ s.support ↔ z ∈ (w.take 3).support ∨ z ∈ q.support :=
    fun _ => Walk.mem_support_append_iff (w.take 3) q
  have hpre : ∀ i ≤ 3, w.getVert i ∈ (w.take 3).support := by
    intro i hi
    have h := (w.take 3).getVert_mem_support i
    simpa only [Walk.take_getVert,Nat.min_eq_right hi] using h
  have hpreOld : ∀ z ∈ (w.take 3).support, z ∈ r.support := by
    intro z hz
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    rw [Walk.take_length,Nat.min_eq_left (by omega : 3 ≤ w.length)] at hil
    rw [Walk.take_getVert,Nat.min_eq_right hil,hwOrd i (by omega)] at hi
    exact hi ▸ r.getVert_mem_support _
  have hsOld : ∀ z ∈ s.support, z ∈ r.support ∨ z = u := by
    intro z hz
    rcases (hsMem z).1 hz with hz | hz
    · exact Or.inl (hpreOld z hz)
    · rcases (hqmem z).1 hz with h | h | h
      · exact Or.inl (h ▸ r.getVert_mem_support _)
      · exact Or.inr h
      · exact Or.inl (h ▸ r.getVert_mem_support _)
  have hArc : ∀ z, z ∈ cycleInterval (walkCycleVertices w) 1 (3-2) ↔
      z = r.getVert 2 ∨ z = r.getVert 3 := by
    intro z
    have hv : ∀ i : ℕ, i ≤ 3 → walkCycleVertices w (i : ZMod w.length) = r.getVert (i+1) := by
      intro i hi; rw [walkCycleVertices_nat_le w (by omega),hwOrd i (by omega)]
    constructor
    · rintro ⟨i,hi,hiz⟩
      rcases (by omega : i=0 ∨ i=1) with rfl | rfl
      · exact Or.inl (by simpa only [hv 1 (by omega)] using hiz.symm)
      · exact Or.inr (by simpa only [hv 2 (by omega)] using hiz.symm)
    · rintro (hz | hz)
      · exact ⟨0,by omega,by simpa only [Nat.add_zero] using (hv 1 (by omega)).trans hz.symm⟩
      · exact ⟨1,by omega,by exact (hv 2 (by omega)).trans hz.symm⟩
  have hSouter : ∀ z : S, OnOuterFace I.embedding I.outer z.1 → z.1 ∈ s.support := by
    intro z hz
    by_cases hzA : z.1 ∈ cycleInterval (walkCycleVertices w) 1 (3-2)
    · rcases (hArc z.1).1 hzA with h | h
      · apply (hsMem z.1).2 ∘ Or.inl
        exact h ▸ ((hwOrd 1 (by omega)) ▸ hpre 1 (by omega))
      · apply (hsMem z.1).2 ∘ Or.inl
        exact h ▸ ((hwOrd 2 (by omega)) ▸ hpre 2 (by omega))
    · have hzq : z.1 ∈ q.support := by
        have h : z.1 ∈ S ∩ T := ⟨z.2,hkeep z.1 hz hzA⟩
        rwa [hinter] at h
      exact (hsMem z.1).2 (Or.inr hzq)
  let PS : BoundaryPrecolor G := .cycle s hs (by rw [cycle_support_card_eq_length s hs]; exact hsLen)
  have hPSv : ∀ z, z ∈ PS.vertices ↔ z ∈ s.support := by
    intro z; simp only [PS,BoundaryPrecolor.vertices,List.mem_toFinset]
  obtain ⟨cS,hcS,hcSfix⟩ := I.colourable_induced_with_compatible_prescription S
    (inducedPlaneMap I.embedding S) oS PS
    (fun z hz => hSC z ((hsMem z).1 ((hPSv z).1 hz))) f
    (fun z hz => hfList z (hsOld z ((hPSv z).1 hz)))
    (fun z hz y hy hzy => hfProper z (hsOld z ((hPSv z).1 hz)) y (hsOld y ((hPSv y).1 hy)) hzy)
    (by
      intro z hz y hy hzy
      let : NeZero s.length := ⟨by have := hs.three_le_length; omega⟩
      exact List.mem_toFinset.2 ((walkCycleVertices_edges s hs z y).1
        (cyclicSubgraph_of_chordless (short_cycle_isChordless I.girth (walk_isCycleMap s hs) hs.three_le_length hsLen)
          (by rw [walkCycleVertices_range s hs]; exact (hPSv z).1 hz)
          (by rw [walkCycleVertices_range s hs]; exact (hPSv y).1 hy) hzy)))
    (fun z hz hzP => (hPSv z).2 (hSouter ⟨z,hz⟩ (I.on_outer z hzP)))
    (fun z hz => (hSface z).2 ((hsMem z.1).1 ((hPSv z.1).1 hz)))
    (fun z hz => I.interior_lists z.1 (fun h => hz ((hSface z).2 ((hsMem z.1).1 (hSouter z h)))))
    (by
      intro z hz hzP hzs
      have h3 := I.interior_lists z (fun h => hzP ((hPSv z).2 (hSouter ⟨z,hz⟩ h)))
      omega) hSs hsmall
  have h01 : G.Adj a (r.getVert 1) := by simpa only [Walk.getVert_zero] using r.adj_getVert_succ (by omega : 0 < r.length)
  have h45 : G.Adj (r.getVert 4) t := by
    have h := r.adj_getVert_succ (by omega : 4 < r.length)
    rw [show 4+1 = r.length by omega,Walk.getVert_length] at h
    exact h
  let v : G.Walk a t := .cons h01 (.cons hu1.symm (.cons hu4 (.cons h45 .nil)))
  have hvMem : ∀ z, z ∈ v.support ↔ z=a ∨ z=r.getVert 1 ∨ z=u ∨ z=r.getVert 4 ∨ z=t := by
    intro z; simp only [v,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false]
  have ha1 : a ≠ r.getVert 1 := by simpa only [Walk.getVert_zero] using hinj 0 1 (by omega) (by omega) (by omega)
  have ha4 : a ≠ r.getVert 4 := by simpa only [Walk.getVert_zero] using hinj 0 4 (by omega) (by omega) (by omega)
  have hat : a ≠ t := by simpa only [← hrlen,Walk.getVert_length,Walk.getVert_zero] using hinj 0 5 (by omega) (by omega) (by omega)
  have h1t : r.getVert 1 ≠ t := by simpa only [← hrlen,Walk.getVert_length] using hinj 1 5 (by omega) (by omega) (by omega)
  have h4t : r.getVert 4 ≠ t := by simpa only [← hrlen,Walk.getVert_length] using hinj 4 5 (by omega) (by omega) (by omega)
  have hau : a ≠ u := fun h => huR (h ▸ r.start_mem_support)
  have hut : u ≠ t := fun h => huR (h.symm ▸ r.end_mem_support)
  have hv : v.IsPath := by
    apply Walk.IsPath.mk'
    simp only [v,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨ha1,hau,ha4,hat⟩,⟨⟨hu1.ne.symm,hinj 1 4 (by omega) (by omega) (by omega),h1t⟩,⟨⟨hu4.ne,hut⟩,h4t⟩⟩⟩
  have hEnds : ¬ G.Adj a t := by
    intro h
    have he : s(a,t) ∈ r.edges := by
      simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using I.short_edges h
        (by simp [I.singleton a ((hPv a).2 r.start_mem_support)])
        (by simp [I.singleton t ((hPv t).2 r.end_mem_support)])
    have hlen := hr.length_eq_one_of_mem_edges he
    omega
  have hvch := four_edge_path_isChordless I.girth v hv (by change 4 ≤ 4; omega) hEnds
  have hvOld : ∀ z ∈ v.support, z ∈ r.support ∨ z=u := by
    intro z hz
    rcases (hvMem z).1 hz with h | h | h | h | h
    · exact Or.inl (h ▸ r.start_mem_support)
    · exact Or.inl (h ▸ r.getVert_mem_support _)
    · exact Or.inr h
    · exact Or.inl (h ▸ r.getVert_mem_support _)
    · exact Or.inl (h ▸ r.end_mem_support)
  have hSepv : ∀ z ∈ q.support, z ∈ v.support := by
    intro z hz
    apply (hvMem z).2
    rcases (hqmem z).1 hz with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  have hvNotInternal : ∀ i : ℕ, i=2 ∨ i=3 → r.getVert i ∉ v.support := by
    intro i hi hz
    rcases (hvMem _).1 hz with h | h | h | h | h
    · exact (hinj i 0 (by omega) (by omega) (by omega)) (by simpa only [Walk.getVert_zero] using h)
    · exact (hinj i 1 (by omega) (by omega) (by omega)) h
    · exact huR (h ▸ r.getVert_mem_support i)
    · exact (hinj i 4 (by omega) (by omega) (by omega)) h
    · exact (hinj i 5 (by omega) (by omega) (by omega)) (by simpa only [← hrlen,Walk.getVert_length] using h)
  have hvT : ∀ z ∈ v.support, z ∈ T := by
    intro z hz
    by_cases hzq : z ∈ q.support
    · have h : z ∈ S ∩ T := by rw [hinter]; exact hzq
      exact h.2
    · have hzR : z ∈ r.support := (hvOld z hz).resolve_right (fun h => hzq ((hqmem z).2 (Or.inr (Or.inl h))))
      apply hkeep z (I.on_outer z ((hPv z).2 hzR))
      intro hzA
      rcases (hArc z).1 hzA with h | h
      · exact hvNotInternal 2 (Or.inl rfl) (h ▸ hz)
      · exact hvNotInternal 3 (Or.inr rfl) (h ▸ hz)
  have hOldT : ∀ z ∈ T, z ∈ I.precolor.vertices → z ∈ v.support := by
    intro z hzT hzP
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hzP)
    by_cases hi23 : i=2 ∨ i=3
    · have hzpre : z ∈ (w.take 3).support := by
        rcases hi23 with rfl | rfl
        · exact hi ▸ ((hwOrd 1 (by omega)) ▸ hpre 1 (by omega))
        · exact hi ▸ ((hwOrd 2 (by omega)) ▸ hpre 2 (by omega))
      have hzq : z ∈ q.support := by
        have h : z ∈ S ∩ T := ⟨hSC z (Or.inl hzpre),hzT⟩
        rwa [hinter] at h
      exact hSepv z hzq
    · apply (hvMem z).2
      rcases (by omega : i=0 ∨ i=1 ∨ i=4 ∨ i=5) with h | h | h | h
      · exact Or.inl (by simpa only [h,Walk.getVert_zero] using hi.symm)
      · exact Or.inr (Or.inl (by simpa only [h] using hi.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [h] using hi.symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [h,← hrlen,Walk.getVert_length] using hi.symm))))
  obtain ⟨cT,hcT,hcTfix⟩ := I.colourable_induced_with_compatible_path_star T M oT hTc.preconnected v hv
    (by change 4 ≤ 5; omega) hvch hvT hOldT u ((hvMem u).2 (Or.inr (Or.inr (Or.inl rfl))))
    (fun z hz => (hvOld z hz).imp_left (fun h => (hPv z).2 h))
    ((hPv a).2 r.start_mem_support) ((hPv t).2 r.end_mem_support) hat f
    (fun z hz => hfList z (hvOld z hz))
    (fun z hz y hy hzy => hfProper z (hvOld z hz) y (hvOld y hy) hzy)
    (by
      intro z hz
      rcases hvOld z.1 hz with hzR | hzu
      · exact hTface z (Or.inl (I.on_outer z.1 ((hPv z.1).2 hzR)))
      · exact hTface z (Or.inr ((hqmem z.1).2 (Or.inr (Or.inl hzu)))))
    (fun z hz => hTface z (Or.inl hz)) hTs hsmall
  apply hbad
  refine glue_induced_colourings S T I.lists (fun z => ?_) hedges cS cT hcS hcT ?_
  · have h := Set.mem_univ z
    rwa [← hcover] at h
  · intro z hzS hzT
    have hzq : z ∈ q.support := by have h : z ∈ S ∩ T := ⟨hzS,hzT⟩; rwa [hinter] at h
    exact (hcSfix ⟨z,hzS⟩ ((hPSv z).2 ((hsMem z).2 (Or.inr hzq)))).trans
      (hcTfix ⟨z,hzT⟩ (hSepv z hzq)).symm

/-- The central six-vertex two-path is a complete main-induction case for the
original arbitrary embedding. A native facial placement and its orientation
are derived internally, using the verified mirror operation when necessary. -/
theorem colourable_of_central_prescribed_two_path_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 5)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hu1 : G.Adj u (r.getVert 1)) (hu4 : G.Adj u (r.getVert 4))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact hbad (I.colourable_of_central_prescribed_two_path hG p hp hface hroot r hr hn hP hrlen horder u hu hu1 hu4 hsmall)
  · have huMirror : ¬ OnOuterFace I.mirror.embedding I.mirror.outer u :=
      fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h)
    exact hbad (I.mirror.colourable_of_central_prescribed_two_path hG p hp hface hroot r hr hn hP hrlen horder u huMirror hu1 hu4 hsmall)

end Thomassen.BoundaryInstance
