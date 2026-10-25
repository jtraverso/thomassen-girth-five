/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ThreeVertexSixFace

/-! Complete strict induction case for three prescribed vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- All native-face cases with three consecutive prescribed vertices are
closed. This includes the alternating short lists and the six-vertex face. -/
theorem colourable_of_three_vertex_prescribed_path_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=2)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support := fun x => (hverts x).2
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hPmem : ∀ x, x ∈ I.precolor.vertices ↔ x=a ∨ x=p.getVert 1 ∨ x=p.getVert 2 := by
    intro x
    have hPv : x ∈ I.precolor.vertices ↔ x ∈ r.support := by
      simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
    rw [hPv]
    constructor
    · intro hx
      obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 hx
      rcases (by omega : k=0 ∨ k=1 ∨ k=2) with he | he | he
      · left; simpa only [he,Walk.getVert_zero] using hk.symm
      · exact Or.inr (Or.inl (hk.symm.trans (by rw [he]; exact horder 1 (by omega))))
      · exact Or.inr (Or.inr (hk.symm.trans (by rw [he]; exact horder 2 (by omega))))
    · rintro (h | h | h)
      · exact h ▸ r.start_mem_support
      · rw [h,← horder 1 (by omega)]; exact r.getVert_mem_support 1
      · rw [h,← horder 2 (by omega)]; exact r.getVert_mem_support 2
  have hfirst : p.getVert 1 ∈ I.precolor.vertices := (hPmem _).2 (Or.inr (Or.inl rfl))
  by_cases hsecond : 3 ≤ (I.lists (p.getVert (p.length-2))).card
  · exact hbad (I.colourable_of_good_second_boundary_list_all_prescriptions hG p hp hface hroot hExact
      r hr hn hP hfirst hsecond hsmall)
  by_cases hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card
  · have hn5 : r.support.toFinset.card ≤ 5 := by
      rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support]
      omega
    exact hbad (I.colourable_of_short_path_short_second_good_fourth hG p hp hface hroot hExact
      r hr hn hP (by omega) hn5 horder (by omega) hfourth hsmall)
  by_cases hlarge : 8 ≤ p.length
  · exact hbad (I.colourable_of_three_vertex_path_short_fourth hG p hp hface hroot hExact hPmem hlarge (by omega) hsmall)
  by_cases hsix : p.length=6
  · exact hbad (I.colourable_of_three_prescribed_vertices_six_vertex_face p hp hface hroot hExact hPmem hsix hsmall)
  have hseven : p.length=7 := by omega
  have h3not : p.getVert 3 ∉ I.precolor.vertices := by
    intro h
    rcases (hPmem _).1 h with h | h | h
    · have he := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from Nat.zero_le _)
        (by simpa only [Walk.getVert_zero] using h)
      omega
    · have he := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega) (show 1 ≤ p.length-1 from by omega) h
      omega
    · have he := hp.getVert_injOn' (show 3 ≤ p.length-1 from by omega) (show 2 ≤ p.length-1 from by omega) h
      omega
  have h3short : (I.lists (p.getVert 3)).card ≤ 2 := by
    have h4 : (I.lists (p.getVert (p.length-4))).card ≤ 2 := by omega
    simpa only [hseven] using h4
  exact I.short_not_adj_precolored h3not ((hPmem _).2 (Or.inr (Or.inr rfl))) h3short
    (p.adj_getVert_succ (by omega : 2 < p.length)).symm

/-- The entire three-vertex prescribed-path case, with the original arbitrary
face and either native direction. Only the strict main induction is assumed. -/
theorem colourable_of_three_vertex_prescribed_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length=2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.colourable_of_three_vertex_prescribed_path_native_face hG p hp hface hroot r hr hn hP hrlen horder hsmall
  · exact I.mirror.colourable_of_three_vertex_prescribed_path_native_face hG p hp hface hroot r hr hn hP hrlen horder hsmall

/-- All nontrivial native prescriptions on at most three vertices are now
complete induction cases: an edge, or the three-vertex path above. -/
theorem colourable_of_nontrivial_prescribed_path_at_most_three (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hn3 : r.support.toFinset.card ≤ 3)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at hn3
  by_cases h1 : r.length=1
  · exact I.colourable_of_prescribed_edge r hr hn hP h1 hsmall
  · exact I.colourable_of_three_vertex_prescribed_path r hr hn hP (by omega) hsmall

end Thomassen.BoundaryInstance
