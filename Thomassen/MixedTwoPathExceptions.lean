/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedPrescribedTwoPath

/-! The only surviving mixed two-paths have a six-vertex prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- On the normalized native face a free boundary vertex cannot adjoin both
prescribed ends: that would leave a single free vertex, a case already closed. -/
theorem free_boundary_not_adjacent_both_prescribed_ends_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hab : G.Adj a b) (htb : G.Adj t b) : False := by
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hblast : b = p.getVert (p.length-1) := by
    rcases chordless_native_cycle_root_neighbours p hp hch ((hverts b).2 hb) hab with h | h
    · apply (hbP ?_).elim
      rw [h,← horder 1 (by omega)]
      exact (hPv _).2 (r.getVert_mem_support _)
    · exact h
  have htp : t ∈ p.support := (hverts t).2 (I.on_outer t ((hPv t).2 r.end_mem_support))
  have hlastt : G.Adj (p.getVert (p.length-1)) t := by rw [← hblast]; exact htb.symm
  rcases chordless_native_cycle_last_neighbours p hp hch htp hlastt with hta | htlast
  · have he := hr.nil_iff_eq.2 hta.symm
    have := he.length_eq_zero
    omega
  · have heq : p.getVert r.length = p.getVert (p.length-2) := by
      rw [← horder r.length le_rfl,Walk.getVert_length]; exact htlast
    have he := hp.getVert_injOn' (show r.length ≤ p.length-1 from by omega)
      (show p.length-2 ≤ p.length-1 from by omega) heq
    omega

/-- The two prescribed ends cannot share a free boundary neighbour, for the
original arbitrary embedding and either direction of the prescribed path. -/
theorem free_boundary_not_adjacent_both_prescribed_ends (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hab : G.Adj a b) (htb : G.Adj t b) : False := by
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.free_boundary_not_adjacent_both_prescribed_ends_on_native_face hG p hp hface hroot
      r hr hn hP hrpos horder hbad hsmall b hb hbP hab htb
  · exact I.mirror.free_boundary_not_adjacent_both_prescribed_ends_on_native_face hG p hp hface hroot
      r hr hn hP hrpos horder hbad hsmall b ((mirror_onOuterFace_iff I.embedding I.outer b).2 hb) hbP hab htb

/-- Every remaining two-path with one internal prescribed endpoint and one
free boundary endpoint has one of the two published six-vertex exceptions.
All other mixed configurations are complete strict-induction cases. -/
theorem mixed_interior_two_path_exceptional (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (i : ℕ) (hi : 0 < i) (hir : i < r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u b : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hui : G.Adj u (r.getVert i)) (hub : G.Adj u b) :
    r.length=5 ∧ ((i=2 ∧ G.Adj a b) ∨ (i=3 ∧ G.Adj t b)) := by
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hlen : r.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at hn
    omega
  have hau : a ≠ u := by
    intro h
    exact hu (h ▸ I.on_outer a ((hPv a).2 r.start_mem_support))
  have htu : t ≠ u := by
    intro h
    exact hu (h ▸ I.on_outer t ((hPv t).2 r.end_mem_support))
  have hNearStart : i=1 → ¬ G.Adj a b := by
    intro hi1 hab
    have h01 : G.Adj a (r.getVert i) := by
      rw [hi1]
      simpa only [Walk.getVert_zero] using r.adj_getVert_succ (by omega : 0 < r.length)
    have he := common_neighbor_unique I.girth hau h01 hui hab hub
    exact hbP ((hPv b).2 (he ▸ r.getVert_mem_support i))
  have hNearEnd : r.length-i=1 → ¬ G.Adj t b := by
    intro hdist htb
    have hit : i+1=r.length := by omega
    have hti : G.Adj t (r.getVert i) := by
      simpa only [hit,Walk.getVert_length] using (r.adj_getVert_succ hir).symm
    have he := common_neighbor_unique I.girth htu hti hui htb hub
    exact hbP ((hPv b).2 (he ▸ r.getVert_mem_support i))
  by_cases hi2 : i ≤ 2
  · have hab : G.Adj a b := by
      by_contra h
      exact hbad (I.colourable_of_mixed_two_path_short_prefix_arbitrary_face r hr hn hP i
        (by omega) hi2 hir b hb hbP h u hu hui hub hsmall)
    have hiEq : i=2 := by by_contra h; exact hNearStart (by omega) hab
    by_cases h5 : r.length=5
    · exact ⟨h5,Or.inl ⟨hiEq,hab⟩⟩
    · have htb : ¬ G.Adj t b := I.free_boundary_not_adjacent_both_prescribed_ends
        r hr hn hP (by omega) hbad hsmall b hb hbP hab
      exact (hbad (I.colourable_of_mixed_two_path_short_suffix_arbitrary_face r hr hn hP
        (r.length-i) (by omega) (by omega) (by omega) b hb hbP htb u hu
        (by simpa only [Nat.sub_sub_self (by omega : i ≤ r.length)] using hui) hub hsmall)).elim
  · have htb : G.Adj t b := by
      by_contra h
      exact hbad (I.colourable_of_mixed_two_path_short_suffix_arbitrary_face r hr hn hP
        (r.length-i) (by omega) (by omega) (by omega) b hb hbP h u hu
        (by simpa only [Nat.sub_sub_self (by omega : i ≤ r.length)] using hui) hub hsmall)
    have hdist : r.length-i=2 := by
      by_contra h
      exact hNearEnd (by omega) htb
    exact ⟨by omega,Or.inr ⟨by omega,htb⟩⟩

end Thomassen.BoundaryInstance
