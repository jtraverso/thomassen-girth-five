/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryPendantGeometry

/-! Deleting the sole unprescribed boundary vertex. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The actual facial case with one unprescribed boundary vertex, including a
six-vertex prescription on a seven-vertex face. New short neighbours attached
to the old path are coloured as pendant vertices; the complete auxiliary
induction handles their arbitrarily many branches and disconnected remainders. -/
theorem colourable_of_single_boundary_complement (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (haP : a ∉ I.precolor.vertices)
    (hcover : ∀ x, x ∈ p.support ↔ x = a ∨ x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let P : Set V := {x | x ∈ r.support}
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ P := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]; rfl
  have ha : a ∉ P := fun h => haP ((hPv a).2 h)
  have hb : b ∈ P := r.start_mem_support
  have ht : t ∈ P := r.end_mem_support
  have hplen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  let : NeZero p.length := ⟨by omega⟩
  let c := walkCycleVertices p
  have hc : IsCycleMap G c := walk_isCycleMap p hp
  have hcycleCover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x ∈ r.support := by
    intro x
    rw [walkCycleVertices_range p hp]
    change x ∈ p.support ↔ _
    rw [hcover]
    exact or_congr Iff.rfl (hPv x)
  have hfac : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support := by
    intro x
    exact (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).symm
  have hcard : p.length = r.length+2 := by
    have heq : p.support.toFinset = insert a r.support.toFinset := by
      ext x
      simp only [List.mem_toFinset,Finset.mem_insert,hcover]
      exact or_congr Iff.rfl (hPv x)
    have heqcard := congrArg Finset.card heq
    rw [cycle_support_card_eq_length p hp,Finset.card_insert_of_notMem (by
      simpa only [List.mem_toFinset,P,Set.mem_ofPred_eq] using ha),List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at heqcard
    omega
  have hlen : r.length ≤ 5 := by
    have h := hn
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at h
    omega
  have hbt : b ≠ t := by
    intro he
    have hz := (hr.nil_iff_eq.2 he).length_eq_zero
    omega
  have hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges := by
    intro x y hx hy hxy
    have he := I.short_edges hxy (by simp [I.singleton x ((hPv x).2 hx)])
      (by simp [I.singleton y ((hPv y).2 hy)])
    simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using he
  have hba : G.Adj b a := path_endpoint_adjacent_to_single_cycle_complement hc (by omega)
    r hr ha hcycleCover hedges
  have hta : G.Adj t a := path_endpoint_adjacent_to_single_cycle_complement hc (by omega)
    r.reverse hr.reverse (by simpa only [Walk.support_reverse,List.mem_reverse,P,Set.mem_ofPred_eq] using ha)
    (by simpa only [Walk.support_reverse,List.mem_reverse] using hcycleCover)
    (by
      intro x y hx hy hxy
      have hx' : x ∈ r.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
      have hy' : y ∈ r.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
      simpa only [Walk.edges_reverse,List.mem_reverse] using hedges hx' hy' hxy)
  have hcyclic : ∀ {x y}, x ∈ p.support → y ∈ p.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y := fun hx hy hxy =>
    (walkCycleVertices_edges p hp _ _).2 (hch.mem_edges hx hy hxy)
  have haNeighbours : ∀ x ∈ P, G.Adj a x → x = b ∨ x = t := by
    intro x hx hax
    have hroot0 : c 0 = a := by simp only [c,walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    have hbcyc := hcyclic p.start_mem_support ((hcover b).2 (Or.inr ((hPv b).2 hb))) hba.symm
    have htcyc := hcyclic p.start_mem_support ((hcover t).2 (Or.inr ((hPv t).2 ht))) hta.symm
    have hxcyc := hcyclic p.start_mem_support ((hcover x).2 (Or.inr ((hPv x).2 hx))) hax
    exact cyclicSubgraph_third_neighbour hc 0 (by simpa only [hroot0] using hbcyc)
      (by simpa only [hroot0] using htcyc) (by simpa only [hroot0] using hxcyc) hbt
  have ha3 : 3 ≤ (I.lists a).card := by
    have hbaShort := I.short_edges hba (by simp [I.singleton b ((hPv b).2 hb)])
    by_contra h
    have he := hbaShort (by omega)
    exact haP (I.precolor.endpoints_of_mem_edges he).2
  obtain ⟨ca,hca,hcaN⟩ : ∃ col ∈ I.lists a, col ∉ ({I.prescribed b,I.prescribed t} : Finset C) :=
    Finset.exists_mem_notMem_of_card_lt_card (Finset.card_le_two.trans_lt (by omega))
  have hcaB : ca ≠ I.prescribed b := fun h => hcaN (Finset.mem_insert.2 (Or.inl h))
  have hcaT : ca ≠ I.prescribed t := fun h => hcaN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let A : Finset V := {a}
  let f : V → C := fun _ => ca
  let L := residual G I.lists A f
  have hPcolour : ∀ x ∈ P, I.prescribed x ∈ L x := by
    intro x hx
    apply (mem_residual_iff I.lists A f x _).2
    refine ⟨by simp [I.singleton x ((hPv x).2 hx)], ?_⟩
    intro y hy hxy
    have he : y = a := Finset.mem_singleton.1 hy
    subst y
    change I.prescribed x ≠ ca
    rcases haNeighbours x hx hxy.symm with rfl | rfl
    · exact hcaB.symm
    · exact hcaT.symm
  have hInterior : ∀ x, x ≠ a → x ∉ P → ¬ OnOuterFace I.embedding I.outer x := by
    intro x hxa hxP hxface
    rcases (hcover x).1 ((hfac x).1 hxface) with h | h
    · exact hxa h
    · exact hxP ((hPv x).1 h)
  have hTwo : ∀ x, x ≠ a → x ∉ P → 2 ≤ (L x).card := by
    intro x hxa hxP
    exact residual_three_to_two I.lists A f x (I.interior_lists x (hInterior x hxa hxP))
      (by exact (Finset.card_filter_le _ _).trans (by simp only [A,Finset.card_singleton]; exact le_rfl))
  let N : Set V := {x | x ≠ a ∧ x ∉ P ∧ (L x).card ≤ 2}
  have hNadj : ∀ x ∈ N, G.Adj a x := by
    intro x hx
    by_contra h
    have hl : L x = I.lists x := residual_unchanged I.lists A f x (by
      intro y hy
      have he : y = a := Finset.mem_singleton.1 hy
      subst y; exact fun hxa => h hxa.symm)
    have h3 := I.interior_lists x (hInterior x hx.1 hx.2.1)
    have h2 := hx.2.2
    rw [hl] at h2
    omega
  have hNind : ∀ x ∈ N, ∀ y ∈ N, ¬ G.Adj x y := fun x hx y hy =>
    neighbors_nonadjacent I.girth (hNadj x hx) (hNadj y hy)
  have hNunique : ∀ x ∈ N, ∀ y ∈ P, ∀ z ∈ P, G.Adj x y → G.Adj x z → y = z := by
    intro x hx y hy z hz hxy hxz
    obtain ⟨i,hi⟩ := (hcycleCover y).2 (Or.inr hy)
    obtain ⟨j,hj⟩ := (hcycleCover z).2 (Or.inr hz)
    have hxcycle : x ∉ Set.range c := by
      rw [hcycleCover]
      exact not_or.2 ⟨hx.1,hx.2.1⟩
    have h0 : c 0 = a := by simp only [c,walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    have he := at_most_two_neighbours_on_short_cycle I.girth hc (by omega) (by omega) hxcycle
      0 i j (by rw [h0]; exact (hNadj x hx).symm) (by rwa [hi]) (by rwa [hj])
    rcases he with he | he | he
    · exact (ha (by rw [← h0,he,hi]; exact hy)).elim
    · exact (ha (by rw [← h0,he,hj]; exact hz)).elim
    · exact hi.symm.trans ((congrArg c he).trans hj)
  have hNends : ∀ x ∈ N, ¬ G.Adj x b ∧ ¬ G.Adj x t := fun x hx =>
    ⟨neighbors_nonadjacent I.girth (hNadj x hx) hba.symm,
      neighbors_nonadjacent I.girth (hNadj x hx) hta.symm⟩
  let R : Set V := {x | x ∈ N ∧ ∃ y ∈ P, G.Adj x y}
  let Q : Set V := P ∪ R
  have hRcol : ∀ x ∈ R, ∃ col ∈ L x, ∀ y ∈ P, G.Adj x y → col ≠ I.prescribed y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hx.2
    obtain ⟨col,hcol,hne⟩ := Finset.exists_mem_ne (s := L x)
      (by have := hTwo x hx.1.1 hx.1.2.1; omega) (I.prescribed y)
    exact ⟨col,hcol,fun z hz hxz => (hNunique x hx.1 y hy z hz hxy hxz) ▸ hne⟩
  let g : V → C := fun x => if hx : x ∈ R then (hRcol x hx).choose else I.prescribed x
  have hgR : ∀ x ∈ R, g x ∈ L x ∧ ∀ y ∈ P, G.Adj x y → g x ≠ I.prescribed y := by
    intro x hx
    simpa only [g,dite_eq_left hx] using (hRcol x hx).choose_spec
  have hgP : ∀ x ∈ P, g x = I.prescribed x := by
    intro x hx
    exact dite_eq_right (fun h => h.1.2.1 hx)
  have hg : ∀ x ∈ Q, g x ∈ L x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hgP x hx]; exact hPcolour x hx
    · exact (hgR x hx).1
  have hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hgP x hx,hgP y hy]
      exact I.proper_on_precolored_vertices ((hPv x).2 hx) ((hPv y).2 hy) hxy
    · rw [hgP x hx]; exact ((hgR y hy).2 x hx hxy.symm).symm
    · rw [hgP y hy]; exact (hgR x hx).2 y hy hxy
    · exact (hNind x hx.1 y hy.1 hxy).elim
  apply I.colourable_of_connected_residual_prescription hG p hp hface hroot
    (fun x hx => (hfac x).1 hx) A (Finset.mem_singleton_self a)
    (by simpa only [A,Finset.coe_singleton] using connSet_singleton G a) f
    (by intro x hx; have he : x = a := Finset.mem_singleton.1 hx; simpa only [he,f] using hca)
    (by intro x hx y hy hxy; have hx' := Finset.mem_singleton.1 hx; have hy' := Finset.mem_singleton.1 hy
        exact (hxy.ne (hx'.trans hy'.symm)).elim)
    Q (connSet_adjoin_attached_vertices P R (walk_support_connSet r) (fun _ hx => hx.2))
    (by intro x hx; simp only [A,Finset.mem_singleton]; rcases hx with hx | hx
        · exact fun he => ha (he ▸ hx)
        · exact hx.1.1)
    (by intro x hx; rcases hx with hx | hx
        · exact Or.inl (I.on_outer x ((hPv x).2 hx))
        · exact Or.inr ⟨a,Finset.mem_singleton_self a,(hNadj x hx.1).symm⟩)
    (fun q hq hsub => short_path_with_pendant_vertices_paths_short r hr hlen hbt hedges R
      (fun _ hx _ hy => hNind _ hx.1 _ hy.1)
      (fun _ hx => hNunique _ hx.1) (fun _ hx => hNends _ hx.1) q hq hsub)
    (by intro x hx; rcases hx with hx | hx
        · exact (Finset.card_le_card (residual_subset G I.lists A f x)).trans
            (by simp only [I.singleton x ((hPv x).2 hx),Finset.card_singleton]; omega)
        · exact hx.1.2.2)
    g hg hgp
    (by intro x hx hxQ; apply hTwo x (by simpa only [A,Finset.mem_singleton] using hx)
        exact fun h => hxQ (Or.inl h))
    (by intro x hx y hy hxy hxs hys
        have hxa : x ≠ a := by simpa only [A,Finset.mem_singleton] using hx
        have hya : y ≠ a := by simpa only [A,Finset.mem_singleton] using hy
        by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
        · exact ⟨Or.inl hxP,Or.inl hyP⟩
        · exact ⟨Or.inl hxP,Or.inr ⟨⟨hya,hyP,hys⟩,x,hxP,hxy.symm⟩⟩
        · exact ⟨Or.inr ⟨⟨hxa,hxP,hxs⟩,y,hyP,hxy⟩,Or.inl hyP⟩
        · exact (hNind x ⟨hxa,hxP,hxs⟩ y ⟨hya,hyP,hys⟩ hxy).elim)
    hsmall

/-- The full strict main-induction case when exactly one vertex of the
original selected outer face lies outside the prescribed native path.
Connectivity, chordlessness, facial placement and rebasing are all derived. -/
theorem colourable_of_unique_unprescribed_outer_vertex (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (x : V)
    (hxf : OnOuterFace I.embedding I.outer x) (hxP : x ∉ I.precolor.vertices)
    (hunique : ∀ y, OnOuterFace I.embedding I.outer y → y ∉ I.precolor.vertices → y = x)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,_,_,a,p,hp,_,_,hverts,hface,hroot⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hxrange : x ∈ Set.range (walkCycleVertices p) := by
    rw [walkCycleVertices_range p hp]
    exact (hverts x).2 hxf
  obtain ⟨i,hi⟩ := hxrange
  have hstart : p.getVert i.val = x := hi
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  obtain ⟨q,hq,_,_,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hpRoot i.val (ZMod.val_lt i)
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG q hq hqface hqroot hbad hsmall
  have hqcover : ∀ y, y ∈ q.support ↔ y = p.getVert i.val ∨ y ∈ I.precolor.vertices := by
    intro y
    rw [native_facial_cycle_support_iff I.embedding I.outer q hq hqface hqroot y]
    constructor
    · intro hy
      by_cases hyP : y ∈ I.precolor.vertices
      · exact Or.inr hyP
      · exact Or.inl ((hunique y hy hyP).trans hstart.symm)
    · rintro (he | hyP)
      · exact he ▸ (hstart.symm ▸ hxf)
      · exact I.on_outer y hyP
  exact hbad (I.colourable_of_single_boundary_complement hG q hq hch hqface hqroot
    r hr hn hP (hstart.symm ▸ hxP) hqcover hsmall)

end Thomassen.BoundaryInstance
