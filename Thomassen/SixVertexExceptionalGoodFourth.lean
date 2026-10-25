/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedResidualPinning

/-! Keep the exceptional interior vertex and release two old prescribed vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
set_option maxHeartbeats 1000000
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The backward mixed exception in the good-fourth-list branch is closed.
The interior witness is retained, and the remaining four old prescribed
vertices form a connected five-vertex replacement prescription with it. -/
theorem colourable_of_six_vertex_backward_exception_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=5)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (u : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hub : G.Adj u (p.getVert (p.length-1))) (hu2 : G.Adj u (r.getVert 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hlen : 9 ≤ p.length := by omega
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  let v1 := r.getVert 1
  let z := r.getVert 2
  let b := p.getVert (p.length-1)
  let d := p.getVert (p.length-2)
  let e := p.getVert (p.length-3)
  let A : Finset V := {a,v1,b,d}
  let T : Set V := {x | x ∈ (r.drop 2).support}
  let Q : Set V := insert u T
  have hAmem : ∀ x, x ∈ A ↔ x=a ∨ x=v1 ∨ x=b ∨ x=d := by
    intro x; simp only [A,Finset.mem_insert,Finset.mem_singleton]
  have hne : ∀ i j : ℕ, i < p.length → j < p.length → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (by change i ≤ p.length-1; omega) (by change j ≤ p.length-1; omega) he)
  have hfFace : ∀ i, OnOuterFace I.embedding I.outer (p.getVert i) := fun i => (hverts _).1 (p.getVert_mem_support i)
  have hnotP : ∀ i, r.length < i → i < p.length → p.getVert i ∉ I.precolor.vertices := by
    intro i hri hip hx
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv _).1 hx)
    have he := hp.getVert_injOn' (show j ≤ p.length-1 from by omega) (show i ≤ p.length-1 from by omega)
      ((horder j hjl).symm.trans hj)
    omega
  have haP : a ∈ I.precolor.vertices := (hPv a).2 r.start_mem_support
  have h1P : v1 ∈ I.precolor.vertices := (hPv v1).2 (r.getVert_mem_support 1)
  have hzP : z ∈ I.precolor.vertices := (hPv z).2 (r.getVert_mem_support 2)
  have hbP : b ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have hdP : d ∉ I.precolor.vertices := hnotP _ (by omega) (by omega)
  have huP : u ∉ I.precolor.vertices := fun h => hu (I.on_outer u h)
  have h1a : v1≠a := by
    intro h
    have he := hr.getVert_injOn (show 1 ≤ r.length from by omega) (Nat.zero_le _)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  have hba : b≠a := by simpa only [Walk.getVert_zero] using hne (p.length-1) 0 (by omega) (by omega) (by omega)
  have hda : d≠a := by simpa only [Walk.getVert_zero] using hne (p.length-2) 0 (by omega) (by omega) (by omega)
  have hbd : b≠d := hne _ _ (by omega) (by omega) (by omega)
  have hb1 : b≠v1 := fun h => hbP (h ▸ h1P)
  have hd1 : d≠v1 := fun h => hdP (h ▸ h1P)
  have hzb : z≠b := fun h => hbP (h ▸ hzP)
  have hua : u≠a := fun h => huP (h ▸ haP)
  have hu1 : u≠v1 := fun h => huP (h ▸ h1P)
  have hubNe : u≠b := hub.ne
  have hud : u≠d := fun h => hu (h ▸ hfFace (p.length-2))
  have huA : u ∉ A := by simpa only [hAmem,not_or] using ⟨hua,hu1,hubNe,hud⟩
  obtain ⟨hN0,hN1⟩ := I.backward_exception_prescribed_end_neighbours hG p hp hface hroot r hr hn hP hrlen horder
    u hu hub hu2 hbad hsmall
  have hTP : ∀ x ∈ T, x ∈ I.precolor.vertices := fun x hx => (hPv x).2 ((r.isSubwalk_drop 2).support_subset hx)
  have hTne : ∀ x ∈ T, x≠a ∧ x≠v1 := by
    intro x hx
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    rw [Walk.drop_getVert] at hi
    rw [Walk.drop_length] at hil
    constructor
    · intro h
      have he := hr.getVert_injOn (show 2+i ≤ r.length from by omega) (Nat.zero_le _)
        (by simpa only [Walk.getVert_zero] using hi.trans h)
      omega
    · intro h
      have he := hr.getVert_injOn (show 2+i ≤ r.length from by omega) (show 1 ≤ r.length from by omega) (hi.trans h)
      omega
  have hzT : z ∈ T := (r.drop 2).start_mem_support
  have hPT : ∀ x ∈ I.precolor.vertices, x=a ∨ x=v1 ∨ x ∈ T := by
    intro x hx
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv x).1 hx)
    by_cases hi0 : i=0
    · exact Or.inl (by simpa only [hi0,Walk.getVert_zero] using hi.symm)
    by_cases hi1 : i=1
    · exact Or.inr (Or.inl (by simpa only [hi1] using hi.symm))
    · exact Or.inr (Or.inr (Walk.mem_support_iff_exists_getVert.2 ⟨i-2,
        by rw [Walk.drop_getVert,Nat.add_sub_of_le (by omega : 2 ≤ i)]; exact hi,
        by rw [Walk.drop_length]; omega⟩))
  have hTA : ∀ x ∈ T, x ∉ A := by
    intro x hx hxA
    rcases (hAmem x).1 hxA with h | h | h | h
    · exact (hTne x hx).1 h
    · exact (hTne x hx).2 h
    · exact hbP (h ▸ hTP x hx)
    · exact hdP (h ▸ hTP x hx)
  have hQA : ∀ x ∈ Q, x ∉ A := by
    intro x hx
    rcases hx with h | hx
    · exact h ▸ huA
    · exact hTA x hx
  have hOutsideP : ∀ x, x ∉ A → x ∉ Q → x ∉ I.precolor.vertices := by
    intro x hx hxQ hxP
    rcases hPT x hxP with h | h | h
    · exact hx ((hAmem x).2 (Or.inl h))
    · exact hx ((hAmem x).2 (Or.inr (Or.inl h)))
    · exact hxQ (Or.inr h)
  have hNoEnds : ∀ x, x ∉ A → x ∉ T → ¬ G.Adj x a ∧ ¬ G.Adj x v1 := by
    intro x hx hxT
    constructor
    · intro h
      rcases hN0 x h.symm with h | h
      · exact hx ((hAmem x).2 (Or.inr (Or.inl h)))
      · exact hx ((hAmem x).2 (Or.inr (Or.inr (Or.inl h))))
    · intro h
      rcases hN1 x h.symm with h | h
      · exact hx ((hAmem x).2 (Or.inl h))
      · exact hxT (h ▸ hzT)
  have hab : G.Adj a b := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),Walk.getVert_length] using
      (p.adj_getVert_succ (by omega : p.length-1 < p.length)).symm
  have hbdAdj : G.Adj b d := by
    simpa only [show p.length-2+1=p.length-1 by omega] using (p.adj_getVert_succ (by omega : p.length-2 < p.length)).symm
  have ha1 : G.Adj a v1 := by simpa only [Walk.getVert_zero] using r.adj_getVert_succ (by omega : 0 < r.length)
  have had : ¬ G.Adj a d := neighbors_nonadjacent I.girth hab.symm hbdAdj
  have h1b : ¬ G.Adj v1 b := fun h => (hN1 b h).elim hba (by exact hzb.symm)
  have h1d : ¬ G.Adj v1 d := by
    intro h
    rcases hN1 d h with h | h
    · exact hda h
    · exact hdP (h ▸ hzP)
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact I.short_not_adj_precolored hbP haP (by omega) hab.symm
  obtain ⟨cd,hcd⟩ := I.list_nonempty d
  obtain ⟨cb,hcb,hcbN⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({I.prescribed a,cd} : Finset C)) (t := I.lists b) (Finset.card_le_two.trans_lt (by omega))
  have hcba : cb≠I.prescribed a := fun h => hcbN (Finset.mem_insert.2 (Or.inl h))
  have hcbd : cb≠cd := fun h => hcbN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let f : V → C := fun x => if x=a then I.prescribed a else if x=v1 then I.prescribed v1 else if x=b then cb else cd
  have hfa : f a=I.prescribed a := by simp only [f,ite_true]
  have hf1 : f v1=I.prescribed v1 := by simp only [f,ite_eq_right h1a,ite_true]
  have hfb : f b=cb := by simp only [f,ite_eq_right hba,ite_eq_right hb1,ite_true]
  have hfd : f d=cd := by simp only [f,ite_eq_right hda,ite_eq_right hd1,ite_eq_right hbd.symm]
  have hfA : ∀ x ∈ A, f x ∈ I.lists x := by
    intro x hx
    rcases (hAmem x).1 hx with h | h | h | h
    · rw [h,hfa,I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [h,hf1,I.singleton v1 h1P]; exact Finset.mem_singleton_self _
    · rw [h,hfb]; exact hcb
    · rw [h,hfd]; exact hcd
  have hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x≠f y := by
    intro x hx y hy hxy
    rcases (hAmem x).1 hx with hx | hx | hx | hx <;> rcases (hAmem y).1 hy with hy | hy | hy | hy
    all_goals rw [hx,hy] at hxy ⊢
    all_goals first
      | exact (hxy.ne rfl).elim
      | exact (had hxy).elim
      | exact (had hxy.symm).elim
      | exact (h1b hxy).elim
      | exact (h1b hxy.symm).elim
      | exact (h1d hxy).elim
      | exact (h1d hxy.symm).elim
      | simpa only [hfa,hf1] using I.proper_on_precolored_vertices haP h1P hxy
      | simpa only [hfa,hf1] using I.proper_on_precolored_vertices h1P haP hxy
      | simpa only [hfa,hfb] using hcba.symm
      | simpa only [hfa,hfb] using hcba
      | simpa only [hfb,hfd] using hcbd
      | simpa only [hfb,hfd] using hcbd.symm
  have hEdgeRes : ∀ x, x ∉ A → x ∉ T → residual G I.lists A f x = residual G I.lists {b,d} f x := by
    intro x hx hxT
    have hNo := hNoEnds x hx hxT
    apply residual_eq_of_same_neighbours
    intro y hxy
    simp only [hAmem,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun h => (hNo.1 (h ▸ hxy)).elim)
      (fun h => h.elim (fun h => (hNo.2 (h ▸ hxy)).elim) id),fun h => Or.inr (Or.inr h)⟩
  have hResT : ∀ x ∈ T, residual G I.lists A f x = {I.prescribed x} := by
    intro x hx
    apply Finset.Subset.antisymm
    · have hs := residual_subset G I.lists A f x
      rwa [I.singleton x (hTP x hx)] at hs
    · apply Finset.singleton_subset_iff.2
      apply (mem_residual_iff I.lists A f x _).2
      refine ⟨by rw [I.singleton x (hTP x hx)]; exact Finset.mem_singleton_self _,?_⟩
      intro y hy hxy
      rcases (hAmem y).1 hy with hya | hy1 | hyb | hyd
      · rw [hya,hfa]
        exact I.proper_on_precolored_vertices (hTP x hx) haP (hya ▸ hxy)
      · rw [hy1,hf1]
        exact I.proper_on_precolored_vertices (hTP x hx) h1P (hy1 ▸ hxy)
      · have hbx : G.Adj b x := hyb ▸ hxy.symm
        rcases chordless_native_cycle_last_neighbours p hp hch ((hverts _).2 (I.on_outer x (hTP x hx))) hbx with h | h
        · exact ((hTne x hx).1 h).elim
        · exact (hdP (by change p.getVert (p.length-2) ∈ I.precolor.vertices; rw [← h]; exact hTP x hx)).elim
      · exact (I.short_not_adj_precolored hdP (hTP x hx) hsecond (hyd ▸ hxy.symm)).elim
  have hOldFree : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (I.lists x).card ≤ 2 →
      residual G I.lists A f x = I.lists x := by
    intro x hx hxP hxs
    apply residual_unchanged
    intro y hy hxy
    rcases (hAmem y).1 hy with hya | hy1 | hyb | hyd
    · exact I.short_not_adj_precolored hxP haP hxs (hya ▸ hxy)
    · exact I.short_not_adj_precolored hxP h1P hxs (hy1 ▸ hxy)
    · have hxF : OnOuterFace I.embedding I.outer x := by
        by_contra h
        have h3 := I.interior_lists x h
        omega
      have hbx : G.Adj b x := hyb ▸ hxy.symm
      rcases chordless_native_cycle_last_neighbours p hp hch ((hverts _).2 hxF) hbx with h | h
      · exact hx ((hAmem x).2 (Or.inl h))
      · exact hx ((hAmem x).2 (Or.inr (Or.inr (Or.inr h))))
    · have hxd : G.Adj x d := by rw [← hyd]; exact hxy
      exact hdP (I.precolor.endpoints_of_mem_edges (I.short_edges hxd hxs hsecond)).2
  have hTwo : ∀ x, x ∉ A → x ∉ Q → 2 ≤ (residual G I.lists A f x).card := by
    intro x hx hxQ
    have hxP := hOutsideP x hx hxQ
    by_cases hxs : (I.lists x).card ≤ 2
    · rw [hOldFree x hx hxP hxs]; exact I.outside_precolor_list_ge_two hxP
    · rw [hEdgeRes x hx (fun h => hxQ (Or.inr h))]
      exact residual_edge_card_ge_two I.girth hbdAdj I.lists f x (by omega)
  have huT : u ∉ T := fun h => huP (hTP u h)
  have hResU2 : 2 ≤ (residual G I.lists A f u).card := by
    rw [hEdgeRes u huA huT]
    exact residual_edge_card_ge_two I.girth hbdAdj I.lists f u (I.interior_lists u hu)
  obtain ⟨cu,hcu,hcuz⟩ := Finset.exists_mem_ne (s := residual G I.lists A f u) (by omega) (I.prescribed z)
  let g : V → C := fun x => if x=u then cu else I.prescribed x
  have hgu : g u=cu := by simp only [g,ite_true]
  have hgT : ∀ x ∈ T, g x=I.prescribed x := by
    intro x hx
    have hxu : x≠u := fun h => huT (by rw [← h]; exact hx)
    exact ite_eq_right hxu
  have hCross : ∀ x, x≠u → ¬ OnOuterFace I.embedding I.outer x →
      (G.Adj b x ∨ G.Adj d x) → ∀ y, y ∉ A → OnOuterFace I.embedding I.outer y → ¬ G.Adj x y := by
    intro x hxu hxF hxN y hy hyF hxy
    rcases hxN with hbx | hdx
    · by_cases hyP : y ∈ I.precolor.vertices
      · obtain ⟨_,hcase⟩ := I.interior_prescribed_and_free_neighbours_exceptional r hr hn hP (by omega)
          hbad hsmall x y b hxF hyP (hfFace (p.length-1)) hbP hxy hbx.symm
        rcases hcase with ⟨hy2,_⟩ | ⟨_,htb⟩
        · have he := common_neighbor_unique I.girth hzb.symm hbx (by change G.Adj (r.getVert 2) x; rw [← hy2]; exact hxy.symm) hub.symm hu2.symm
          exact hxu he
        · exact I.free_boundary_not_adjacent_both_prescribed_ends r hr hn hP (by omega) hbad hsmall
            b (hfFace (p.length-1)) hbP hab htb
      · have he := I.interior_unprescribed_neighbour_unique r hr hn hP (by omega) hbad hsmall x b y
          hxF (hfFace (p.length-1)) hyF hbP hyP hbx.symm hxy
        exact hy ((hAmem y).2 (Or.inr (Or.inr (Or.inl he.symm))))
    · have he := I.interior_neighbours_unique_at_short_free_boundary_vertex r hr hn hP (by omega) hbad hsmall
        x d y hxF (hfFace (p.length-2)) hyF hdP hsecond hdx.symm hxy
      exact hy ((hAmem y).2 (Or.inr (Or.inr (Or.inr he.symm))))
  have hNewFace : ∀ x, x ∉ A → OnOuterFace I.embedding I.outer x → (G.Adj b x ∨ G.Adj d x) → x=e := by
    intro x hx hxF hxN
    rcases hxN with hbx | hdx
    · rcases chordless_native_cycle_last_neighbours p hp hch ((hverts _).2 hxF) hbx with h | h
      · exact (hx ((hAmem x).2 (Or.inl h))).elim
      · exact (hx ((hAmem x).2 (Or.inr (Or.inr (Or.inr h))))).elim
    · rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) ((hverts _).2 hxF) hdx with h | h
      · simpa only [show p.length-2-1=p.length-3 by omega] using h
      · exact (hx ((hAmem x).2 (Or.inr (Or.inr (Or.inl (by simpa only [show p.length-2+1=p.length-1 by omega] using h)))))).elim
  have hNew : ∀ x, x ∉ A → x ∉ T → 3 ≤ (I.lists x).card → (residual G I.lists A f x).card ≤ 2 →
      G.Adj b x ∨ G.Adj d x := by
    intro x hx hxT hx3 hxs
    rw [hEdgeRes x hx hxT] at hxs
    exact short_residual_edge_neighbor I.lists f x hx3 hxs
  have hNoOld : ∀ x, x ∉ A → x≠u → 3 ≤ (I.lists x).card → (G.Adj b x ∨ G.Adj d x) →
      ∀ y, y ∉ A → (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hxu hx3 hxN y hy hys hxy
    have hyF : OnOuterFace I.embedding I.outer y := by
      by_contra h
      have h3 := I.interior_lists y h
      omega
    by_cases hxF : OnOuterFace I.embedding I.outer x
    · have he := hNewFace x hx hxF hxN
      have hey : G.Adj e y := by rwa [he] at hxy
      rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) ((hverts _).2 hyF) hey with h | h
      · have h3 : 3 ≤ (I.lists y).card := by simpa only [show p.length-3-1=p.length-4 by omega] using h ▸ hfourth
        omega
      · exact hy ((hAmem y).2 (Or.inr (Or.inr (Or.inr (by simpa only [show p.length-3+1=p.length-2 by omega] using h)))))
    · exact hCross x hxu hxF hxN y hy hyF hxy
  have hNoU : ∀ x, x ∉ A → x ∉ Q → (residual G I.lists A f x).card ≤ 2 → ¬ G.Adj x u := by
    intro x hx hxQ hxs hxu
    have hxP := hOutsideP x hx hxQ
    by_cases hxOld : (I.lists x).card ≤ 2
    · have hxF : OnOuterFace I.embedding I.outer x := by
        by_contra h
        have h3 := I.interior_lists x h
        omega
      rcases I.interior_at_most_two_boundary_neighbours r hr hn hP (by omega) hbad hsmall
        u b z x hu (hfFace (p.length-1)) (I.on_outer z hzP) hxF hub hu2 hxu.symm with h | h | h
      · exact hzb h.symm
      · exact hx ((hAmem x).2 (Or.inr (Or.inr (Or.inl h.symm))))
      · exact hxQ (Or.inr (h ▸ hzT))
    · have hxN := hNew x hx (fun h => hxQ (Or.inr h)) (by omega) hxs
      exact deleted_edge_neighbors_independent I.girth hbdAdj
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inr (Or.inl h)))))
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inr (Or.inr h))))) hubNe hud hxN (Or.inl hub.symm) hxu
  have hNoQ : ∀ x, x ∉ A → x ∉ Q → (residual G I.lists A f x).card ≤ 2 → ∀ y ∈ Q, ¬ G.Adj x y := by
    intro x hx hxQ hxs y hy hxy
    rcases hy with hyu | hyT
    · exact hNoU x hx hxQ hxs (hyu ▸ hxy)
    · have hxP := hOutsideP x hx hxQ
      by_cases hxOld : (I.lists x).card ≤ 2
      · exact I.short_not_adj_precolored hxP (hTP y hyT) hxOld hxy
      · exact hNoOld x hx (fun h => hxQ (Or.inl h)) (by omega)
          (hNew x hx (fun h => hxQ (Or.inr h)) (by omega) hxs) y (hTA y hyT)
          (by rw [I.singleton y (hTP y hyT),Finset.card_singleton]; omega) hxy
  have hInd : ∀ x, x ∉ A → x ∉ Q → ∀ y, y ∉ A → y ∉ Q →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hxQ y hy hyQ hxs hys hxy
    by_cases hxOld : (I.lists x).card ≤ 2 <;> by_cases hyOld : (I.lists y).card ≤ 2
    · exact hOutsideP x hx hxQ (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)).1
    · exact hNoOld y hy (fun h => hyQ (Or.inl h)) (by omega)
        (hNew y hy (fun h => hyQ (Or.inr h)) (by omega) hys) x hx hxOld hxy.symm
    · exact hNoOld x hx (fun h => hxQ (Or.inl h)) (by omega)
        (hNew x hx (fun h => hxQ (Or.inr h)) (by omega) hxs) y hy hyOld hxy
    · exact deleted_edge_neighbors_independent I.girth hbdAdj
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inr (Or.inl h)))))
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inr (Or.inr h)))))
        (fun h => hy ((hAmem y).2 (Or.inr (Or.inr (Or.inl h)))))
        (fun h => hy ((hAmem y).2 (Or.inr (Or.inr (Or.inr h)))))
        (hNew x hx (fun h => hxQ (Or.inr h)) (by omega) hxs)
        (hNew y hy (fun h => hyQ (Or.inr h)) (by omega) hys) hxy
  have hAconn : ConnSet G (↑A : Set V) := by
    have h := (((connSet_singleton G a).insert_adj (Set.mem_singleton a) ha1.symm).insert_adj
      (Set.mem_insert_of_mem v1 (Set.mem_singleton a)) hab.symm).insert_adj (Set.mem_insert b _) hbdAdj.symm
    convert h using 1
    ext x
    simp only [A,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hQconn : ConnSet G Q := (walk_support_connSet (r.drop 2)).insert_adj hzT hu2
  have hg : ∀ x ∈ Q, g x ∈ residual G I.lists A f x := by
    intro x hx
    rcases hx with h | hx
    · rw [h,hgu]; exact hcu
    · rw [hgT x hx,hResT x hx]; exact Finset.mem_singleton_self _
  have hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x≠g y := by
    have hUT : ∀ x ∈ T, G.Adj u x → g u≠g x := by
      intro x hx hux
      have he := I.interior_prescribed_neighbour_unique r hr hn hP hbad hsmall u x z hu (hTP x hx) hzP hux hu2
      rw [hgu,hgT x hx,he]
      exact hcuz
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · rw [hx]; exact hUT y hy (hx ▸ hxy)
    · rw [hy]; exact (hUT x hx (hy ▸ hxy.symm)).symm
    · rw [hgT x hx,hgT y hy]; exact I.proper_on_precolored_vertices (hTP x hx) (hTP y hy) hxy
  apply hbad
  apply I.colourable_of_connected_residual_prescription_with_pinning hG p hp hface hroot (fun x hx => (hverts x).2 hx)
    A ((hAmem a).2 (Or.inl rfl)) hAconn f hfA hproper Q hQconn hQA ?_ ?_ g hg hgp hTwo ?_ hsmall
  · intro x hx
    rcases hx with h | hx
    · exact Or.inr ⟨b,(hAmem b).2 (Or.inr (Or.inr (Or.inl rfl))),by rw [h]; exact hub⟩
    · exact Or.inl (I.on_outer x (hTP x hx))
  · intro x y w hw hs
    have hsub : w.support.toFinset ⊆ insert u (r.drop 2).support.toFinset := by
      intro z hz
      exact (hs z (List.mem_toFinset.1 hz)).elim (fun h => Finset.mem_insert.2 (Or.inl h))
        (fun h => Finset.mem_insert.2 (Or.inr (List.mem_toFinset.2 h)))
    have hcard := Finset.card_le_card hsub
    have hboundT : (r.drop 2).support.toFinset.card=4 := by
      rw [List.toFinset_card_of_nodup (hr.drop 2).support_nodup,Walk.length_support,Walk.drop_length,hrlen]
    have hboundQ := Finset.card_insert_le u (r.drop 2).support.toFinset
    rw [List.toFinset_card_of_nodup hw.support_nodup,Walk.length_support] at hcard
    omega
  · intro x hx y hy hxy hxs hys
    by_cases hxQ : x ∈ Q <;> by_cases hyQ : y ∈ Q
    · exact ⟨hxQ,hyQ⟩
    · exact (hNoQ y hy hyQ (hys.resolve_left hyQ) x hxQ hxy.symm).elim
    · exact (hNoQ x hx hxQ (hxs.resolve_left hxQ) y hyQ hxy).elim
    · exact (hInd x hx hxQ y hy hyQ (hxs.resolve_left hxQ) (hys.resolve_left hyQ) hxy).elim

end Thomassen.BoundaryInstance
