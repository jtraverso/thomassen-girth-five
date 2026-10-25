/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexFiveFaceAttachments

/-! Delete a coloured free five-face while retaining the old prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- All residual-state conditions for a free inner five-face follow from
the proved geometric exclusions. The inputs describe only a concrete proper
colouring of the deleted cycle, preservation of old short lists, and the old
boundary lists adjacent to that cycle. -/
theorem colourable_of_free_inner_five_face_deletion_six (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length)
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (c : G.Walk a a) (hc : c.IsCycle) (hclen : c.length=5)
    (hC : ∀ z, z ∈ c.support ↔ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (f : V → C) (hf : ∀ z ∈ c.support, f z ∈ I.lists z)
    (hproper : ∀ z ∈ c.support, ∀ w ∈ c.support, G.Adj z w → f z ≠ f w)
    (hOldUnchanged : ∀ z, z ∉ c.support → (I.lists z).card ≤ 2 →
      residual G I.lists c.support.toFinset f z = I.lists z)
    (hBoundaryShort : ∀ z, z ∉ c.support → OnOuterFace I.embedding I.outer z →
      (∃ w ∈ c.support, G.Adj z w) → (I.lists z).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  let A := c.support.toFinset
  have hAmem : ∀ z, z ∈ A ↔ z ∈ c.support := fun _ => List.mem_toFinset
  have hPA : ∀ z ∈ I.precolor.vertices, z ∉ A := by
    intro z hz hzA
    have hzC := (hC z).1 ((hAmem z).1 hzA)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hzC
    rcases hzC with hza | hzd | hzb | hzx | hzy
    · exact haP (hza ▸ hz)
    · exact hdP (hzd ▸ hz)
    · exact hbP (hzb ▸ hz)
    · exact hx (I.on_outer x (hzx ▸ hz))
    · exact hy (I.on_outer y (hzy ▸ hz))
  have hResP : ∀ z ∈ I.precolor.vertices, residual G I.lists A f z = {I.prescribed z} := by
    intro z hz
    rw [hOldUnchanged z (fun h => hPA z hz ((hAmem z).2 h))
      (by rw [I.singleton z hz,Finset.card_singleton]; omega),I.singleton z hz]
  have hTwo : ∀ z, z ∉ A → z ∉ I.precolor.vertices → 2 ≤ (residual G I.lists A f z).card := by
    intro z hz hzP
    by_cases hzs : (I.lists z).card ≤ 2
    · rw [hOldUnchanged z (fun h => hz ((hAmem z).2 h)) hzs]
      exact I.outside_precolor_list_ge_two hzP
    · exact residual_native_five_cycle_card_ge_two I.girth c hc hclen I.lists f z
        (fun h => hz ((hAmem z).2 h)) (by omega)
  have hNew : ∀ z, z ∉ A → 3 ≤ (I.lists z).card → (residual G I.lists A f z).card ≤ 2 →
      ¬ OnOuterFace I.embedding I.outer z ∧ ∃ w ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj z w := by
    intro z hz hz3 hzs
    obtain ⟨w,hw,hwz⟩ := short_residual_neighbor I.lists A f z hz3 hzs
    have hwC := (hAmem w).1 hw
    refine ⟨?_,w,(hC w).1 hwC,hwz.symm⟩
    intro hzF
    have hs := hBoundaryShort z (fun h => hz ((hAmem z).2 h)) hzF ⟨w,hwC,hwz.symm⟩
    omega
  have hNoBoundary : ∀ u z, u ∉ A → 3 ≤ (I.lists u).card → (residual G I.lists A f u).card ≤ 2 →
      z ∉ A → OnOuterFace I.embedding I.outer z →
      ((z ∉ I.precolor.vertices ∧ (I.lists z).card ≤ 2) ∨ z=s ∨ z=t) → ¬ G.Adj u z := by
    intro u z hu hu3 hus hz hzF hforbidden
    obtain ⟨huF,huN⟩ := hNew u hu hu3 hus
    exact I.inner_five_face_attachment_no_forbidden_boundary_neighbour_six r hr hn hP hrpos p hp hface hroot
      haP hdP hbP x y hx hy hbx hya hbad hsmall u z huF hzF
      (fun h => hz ((hAmem z).2 ((hC z).2 h))) huN hforbidden
  have hIndependent : ∀ u, u ∉ A → u ∉ I.precolor.vertices → ∀ v2, v2 ∉ A → v2 ∉ I.precolor.vertices →
      (residual G I.lists A f u).card ≤ 2 → (residual G I.lists A f v2).card ≤ 2 → ¬ G.Adj u v2 := by
    intro u hu huP v2 hv hvP hus hvs huv
    by_cases huOld : (I.lists u).card ≤ 2 <;> by_cases hvOld : (I.lists v2).card ≤ 2
    · exact huP (I.precolor.endpoints_of_mem_edges (I.short_edges huv huOld hvOld)).1
    · have huF : OnOuterFace I.embedding I.outer u := by
        by_contra h
        have h3 := I.interior_lists u h
        omega
      exact hNoBoundary v2 u hv (by omega) hvs hu huF (Or.inl ⟨huP,huOld⟩) huv.symm
    · have hvF : OnOuterFace I.embedding I.outer v2 := by
        by_contra h
        have h3 := I.interior_lists v2 h
        omega
      exact hNoBoundary u v2 hu (by omega) hus hv hvF (Or.inl ⟨hvP,hvOld⟩) huv
    · obtain ⟨huF,huN⟩ := hNew u hu (by omega) hus
      obtain ⟨hvF,hvN⟩ := hNew v2 hv (by omega) hvs
      exact I.inner_five_face_interior_attachments_independent hG p hp hface hroot hlen x y hx hy hbx hxy hya
        hbad hsmall u v2 huF hvF (fun h => hu ((hAmem u).2 ((hC u).2 h)))
        (fun h => hv ((hAmem v2).2 ((hC v2).2 h))) huN hvN huv
  have hEnds : ∀ z, z ∉ A → z ∉ I.precolor.vertices → (residual G I.lists A f z).card ≤ 2 →
      ¬ G.Adj z s ∧ ¬ G.Adj z t := by
    intro z hz hzP hzs
    have hsP : s ∈ I.precolor.vertices := by rw [hP]; exact List.mem_toFinset.2 r.start_mem_support
    have htP : t ∈ I.precolor.vertices := by rw [hP]; exact List.mem_toFinset.2 r.end_mem_support
    by_cases hzOld : (I.lists z).card ≤ 2
    · exact ⟨I.short_not_adj_precolored hzP hsP hzOld,I.short_not_adj_precolored hzP htP hzOld⟩
    · exact ⟨hNoBoundary z s hz (by omega) hzs (hPA s hsP) (I.on_outer s hsP) (Or.inr (Or.inl rfl)),
        hNoBoundary z t hz (by omega) hzs (hPA t htP) (I.on_outer t htP) (Or.inr (Or.inr rfl))⟩
  have hrlen : r.length ≤ 5 := by
    have h := hn
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at h
    omega
  apply hbad
  apply I.colourable_of_residual_short_leaves_unique_parent hG p hp hface hroot r hr hn hP hrpos hrlen A
    ((hAmem a).2 c.start_mem_support) (by simpa only [A,List.coe_toFinset] using walk_support_connSet c)
    hPA f (fun z hz => hf z ((hAmem z).1 hz))
    (fun z hz w hw hzw => hproper z ((hAmem z).1 hz) w ((hAmem w).1 hw) hzw)
    hResP hTwo hIndependent hEnds ?_ hsmall
  intro x hx hxP hxs y hy z hz hxy hxz
  by_cases hxOld : (I.lists x).card ≤ 2
  · exact (I.short_not_adj_precolored hxP hy hxOld hxy).elim
  · obtain ⟨hxF,_⟩ := hNew x hx (by omega) hxs
    exact I.interior_prescribed_neighbour_unique r hr hn hP hbad hsmall x y z hxF hy hz hxy hxz

end Thomassen.BoundaryInstance
