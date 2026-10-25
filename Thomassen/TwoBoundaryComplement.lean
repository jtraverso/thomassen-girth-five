/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.TwoBoundaryGeometry

/-! Completing the case with exactly two unprescribed outer vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The actual facial case with two unprescribed boundary vertices. Their
adjacency, compatible deleted colours and every residual-list condition are
derived. The old prescription may have all six permitted vertices. -/
theorem colourable_of_two_boundary_complement (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (d : V) (hadne : a ≠ d)
    (haP : a ∉ I.precolor.vertices) (hdP : d ∉ I.precolor.vertices)
    (hcover : ∀ x, x ∈ p.support ↔ x = a ∨ x = d ∨ x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have ha : a ∉ r.support := fun h => haP ((hPv a).2 h)
  have hd : d ∉ r.support := fun h => hdP ((hPv d).2 h)
  have hplen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  let : NeZero p.length := ⟨by omega⟩
  let c := walkCycleVertices p
  have hc : IsCycleMap G c := walk_isCycleMap p hp
  have hcycleCover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x = d ∨ x ∈ r.support := by
    intro x
    rw [walkCycleVertices_range p hp]
    change x ∈ p.support ↔ _
    rw [hcover,hPv]
  have hfac : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support := fun x =>
    (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).symm
  have hcard : p.length = r.length+3 := by
    have heq : p.support.toFinset = insert a (insert d r.support.toFinset) := by
      ext x
      simp only [List.mem_toFinset,Finset.mem_insert,hcover,hPv]
    have he := congrArg Finset.card heq
    rw [cycle_support_card_eq_length p hp,
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,List.mem_toFinset,not_or]; exact ⟨hadne,ha⟩),
      Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hd),
      List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at he
    omega
  have hlen : r.length ≤ 5 := by
    have h := hn
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at h
    omega
  have hbt : b ≠ t := by
    intro h
    have hz := (hr.nil_iff_eq.2 h).length_eq_zero
    omega
  have hcyclic : ∀ {x y}, x ∈ p.support → y ∈ p.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y := fun hx hy hxy =>
    (walkCycleVertices_edges p hp _ _).2 (hch.mem_edges hx hy hxy)
  have hrFace : ∀ x ∈ r.support, x ∈ p.support := fun x hx =>
    (hcover x).2 (Or.inr (Or.inr ((hPv x).2 hx)))
  have hrCyclic : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y →
      (cyclicSubgraph G c).Adj x y := fun hx hy hxy => hcyclic (hrFace _ hx) (hrFace _ hy) hxy
  have had : G.Adj a d := two_cycle_complement_adjacent I.girth hc (by omega)
    r hr ha hd hadne hbt hcycleCover hrCyclic
  have hadCyc : (cyclicSubgraph G c).Adj a d := hcyclic p.start_mem_support
    ((hcover d).2 (Or.inr (Or.inl rfl))) had
  obtain ⟨zA,hzA,hazA,huniqueA⟩ := cycle_complement_edge_endpoint_unique_path_neighbour hc (by omega)
    r ha hd hcycleCover hadCyc (fun x hx hax => hcyclic p.start_mem_support (hrFace x hx) hax)
  have hswap : ∀ x, x ∈ Set.range c ↔ x = d ∨ x = a ∨ x ∈ r.support := by
    intro x; rw [hcycleCover]; tauto
  obtain ⟨zD,hzD,hdzD,huniqueD⟩ := cycle_complement_edge_endpoint_unique_path_neighbour hc (by omega)
    r hd ha hswap hadCyc.symm (fun x hx hdx =>
      hcyclic ((hcover d).2 (Or.inr (Or.inl rfl))) (hrFace x hx) hdx)
  have ha3 : 3 ≤ (I.lists a).card := by
    by_contra h
    have he := I.short_edges hazA (by omega) (by simp [I.singleton zA ((hPv zA).2 hzA)])
    exact haP (I.precolor.endpoints_of_mem_edges he).1
  have hd3 : 3 ≤ (I.lists d).card := by
    by_contra h
    have he := I.short_edges hdzD (by omega) (by simp [I.singleton zD ((hPv zD).2 hzD)])
    exact hdP (I.precolor.endpoints_of_mem_edges he).1
  obtain ⟨ca,hca,hcaA⟩ := Finset.exists_mem_ne (s := I.lists a) (by omega) (I.prescribed zA)
  obtain ⟨cd,hcd,hcdN⟩ : ∃ col ∈ I.lists d, col ∉ ({I.prescribed zD,ca} : Finset C) :=
    Finset.exists_mem_notMem_of_card_lt_card (Finset.card_le_two.trans_lt (by omega))
  have hcdD : cd ≠ I.prescribed zD := fun h => hcdN (Finset.mem_insert.2 (Or.inl h))
  have hcdA : cd ≠ ca := fun h => hcdN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let A : Finset V := {a,d}
  let f : V → C := fun x => if x = a then ca else cd
  let L := residual G I.lists A f
  have hAmem : ∀ x, x ∈ A ↔ x = a ∨ x = d := fun x => by
    simp only [A,Finset.mem_insert,Finset.mem_singleton]
  have hnotA : ∀ x, x ∉ A ↔ x ≠ a ∧ x ≠ d := fun x => by rw [hAmem]; exact not_or
  have hAP : ∀ x ∈ I.precolor.vertices, x ∉ A := by
    intro x hx
    exact (hnotA x).2 ⟨fun h => haP (h ▸ hx),fun h => hdP (h ▸ hx)⟩
  have hPcolour : ∀ x ∈ I.precolor.vertices, I.prescribed x ∈ L x := by
    intro x hx
    apply (mem_residual_iff I.lists A f x _).2
    refine ⟨by simp [I.singleton x hx],?_⟩
    intro y hy hxy
    rcases (hAmem y).1 hy with hya | hyd
    · have hyf : f y = ca := by simp only [f,hya,ite_true]
      rw [hyf,huniqueA x ((hPv x).1 hx) (hya ▸ hxy.symm)]
      exact hcaA.symm
    · have hyf : f y = cd := by simp only [f,hyd,ite_eq_right hadne.symm]
      rw [hyf,huniqueD x ((hPv x).1 hx) (hyd ▸ hxy.symm)]
      exact hcdD.symm
  have hInterior : ∀ x, x ∉ A → x ∉ I.precolor.vertices → ¬ OnOuterFace I.embedding I.outer x := by
    intro x hx hxP hxf
    rcases (hcover x).1 ((hfac x).1 hxf) with h | h | h
    · exact hx ((hAmem x).2 (Or.inl h))
    · exact hx ((hAmem x).2 (Or.inr h))
    · exact hxP h
  have hTwo : ∀ x, x ∉ A → x ∉ I.precolor.vertices → 2 ≤ (L x).card := by
    intro x hx hxP
    exact residual_edge_card_ge_two I.girth had I.lists f x (I.interior_lists x (hInterior x hx hxP))
  let N : Set V := {x | x ∉ A ∧ x ∉ I.precolor.vertices ∧ (L x).card ≤ 2}
  have hNadjOr : ∀ x ∈ N, G.Adj a x ∨ G.Adj d x := fun x hx =>
    short_residual_edge_neighbor I.lists f x (I.interior_lists x (hInterior x hx.1 hx.2.1)) hx.2.2
  have hNadj : ∀ x ∈ N, ∃ y ∈ A, G.Adj x y := by
    intro x hx
    rcases hNadjOr x hx with h | h
    · exact ⟨a,(hAmem a).2 (Or.inl rfl),h.symm⟩
    · exact ⟨d,(hAmem d).2 (Or.inr rfl),h.symm⟩
  have hNind : ∀ x ∈ N, ∀ y ∈ N, ¬ G.Adj x y := by
    intro x hx y hy
    exact deleted_edge_neighbors_independent I.girth had
      ((hnotA x).1 hx.1).1 ((hnotA x).1 hx.1).2
      ((hnotA y).1 hy.1).1 ((hnotA y).1 hy.1).2 (hNadjOr x hx) (hNadjOr y hy)
  have hNunique : ∀ x ∈ N, ∀ y ∈ I.precolor.vertices, ∀ z ∈ I.precolor.vertices,
      G.Adj x y → G.Adj x z → y = z := by
    intro x hx y hy z hz hxy hxz
    obtain ⟨w,hwA,hxw⟩ := hNadj x hx
    have hwRange : w ∈ Set.range c := by
      rcases (hAmem w).1 hwA with h | h
      · exact (hcycleCover w).2 (Or.inl h)
      · exact (hcycleCover w).2 (Or.inr (Or.inl h))
    obtain ⟨i,hi⟩ := hwRange
    obtain ⟨j,hj⟩ := (hcycleCover y).2 (Or.inr (Or.inr ((hPv y).1 hy)))
    obtain ⟨l,hl⟩ := (hcycleCover z).2 (Or.inr (Or.inr ((hPv z).1 hz)))
    have hxCycle : x ∉ Set.range c := by
      intro h
      rcases (hcycleCover x).1 h with h | h | h
      · exact hx.1 ((hAmem x).2 (Or.inl h))
      · exact hx.1 ((hAmem x).2 (Or.inr h))
      · exact hx.2.1 ((hPv x).2 h)
    have he := at_most_two_neighbours_on_short_cycle I.girth hc (by omega) (by omega) hxCycle
      i j l (by rwa [hi]) (by rwa [hj]) (by rwa [hl])
    rcases he with he | he | he
    · have hwyeq : w = y := hi.symm.trans ((congrArg c he).trans hj)
      exact (hAP y hy (hwyeq ▸ hwA)).elim
    · have hwzeq : w = z := hi.symm.trans ((congrArg c he).trans hl)
      exact (hAP z hz (hwzeq ▸ hwA)).elim
    · exact hj.symm.trans ((congrArg c he).trans hl)
  have hSetCover : ∀ x, x ∈ Set.range c ↔ x ∈ (↑A : Set V) ∨ x ∈ r.support := by
    intro x
    change x ∈ Set.range c ↔ x ∈ A ∨ x ∈ r.support
    rw [hcycleCover,hAmem]; tauto
  have hrEdges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges := by
    intro x y hx hy hxy
    have he := I.short_edges hxy (by simp [I.singleton x ((hPv x).2 hx)])
      (by simp [I.singleton y ((hPv y).2 hy)])
    simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using he
  obtain ⟨vb,hvb,hbvb⟩ := path_endpoint_has_cycle_complement_neighbour hc (by omega) r hr
    (↑A : Set V) hSetCover hrEdges
  obtain ⟨vt,hvt,htvt⟩ := path_endpoint_has_cycle_complement_neighbour hc (by omega) r.reverse hr.reverse
    (↑A : Set V) (by simpa only [Walk.support_reverse,List.mem_reverse] using hSetCover)
    (by
      intro x y hx hy hxy
      have hx' : x ∈ r.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
      have hy' : y ∈ r.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hy
      simpa only [Walk.edges_reverse,List.mem_reverse] using hrEdges hx' hy' hxy)
  have hbAttach : G.Adj a b ∨ G.Adj d b := by
    rcases (hAmem vb).1 hvb with h | h
    · exact Or.inl (h ▸ hbvb.symm)
    · exact Or.inr (h ▸ hbvb.symm)
  have htAttach : G.Adj a t ∨ G.Adj d t := by
    rcases (hAmem vt).1 hvt with h | h
    · exact Or.inl (h ▸ htvt.symm)
    · exact Or.inr (h ▸ htvt.symm)
  have hbnotA := (hnotA b).1 (hAP b ((hPv b).2 r.start_mem_support))
  have htnotA := (hnotA t).1 (hAP t ((hPv t).2 r.end_mem_support))
  have hNends : ∀ x ∈ N, ¬ G.Adj x b ∧ ¬ G.Adj x t := by
    intro x hx
    have hxnotA := (hnotA x).1 hx.1
    exact ⟨deleted_edge_neighbors_independent I.girth had hxnotA.1 hxnotA.2
      hbnotA.1 hbnotA.2 (hNadjOr x hx) hbAttach,
      deleted_edge_neighbors_independent I.girth had hxnotA.1 hxnotA.2
      htnotA.1 htnotA.2 (hNadjOr x hx) htAttach⟩
  apply I.colourable_of_pendant_residual_neighbours hG p hp hface hroot r hr hn hP hbt A
    ((hAmem a).2 (Or.inl rfl)) ?_ hAP f ?_ ?_ hPcolour hTwo N (fun _ => Iff.rfl)
    hNadj hNind hNunique hNends hsmall
  · have he := connSet_singleton G d |>.insert_adj (Set.mem_singleton d) had
    simpa only [A,Finset.coe_insert,Finset.coe_singleton] using he
  · intro x hx
    rcases (hAmem x).1 hx with rfl | rfl
    · simpa only [f,ite_true] using hca
    · simpa only [f,ite_eq_right hadne.symm] using hcd
  · intro x hx y hy hxy
    rcases (hAmem x).1 hx with rfl | rfl <;> rcases (hAmem y).1 hy with rfl | rfl
    · exact (hxy.ne rfl).elim
    · simpa only [f,ite_true,ite_eq_right hadne.symm] using hcdA.symm
    · simpa only [f,ite_true,ite_eq_right hadne.symm] using hcdA
    · exact (hxy.ne rfl).elim

/-- The complete strict main-induction case for an arbitrary original face
with exactly two unprescribed vertices. Connectivity, chordlessness, adjacency
of the free pair and facial orientation are not supplied as assumptions. -/
theorem colourable_of_two_unprescribed_outer_vertices (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (x y : V) (hxy : x ≠ y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hcover : ∀ z, OnOuterFace I.embedding I.outer z ↔
      z = x ∨ z = y ∨ z ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,_,_,a,p,hp,_,_,hverts,hface,hroot⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hxf : OnOuterFace I.embedding I.outer x := (hcover x).2 (Or.inl rfl)
  have hxrange : x ∈ Set.range (walkCycleVertices p) := by
    rw [walkCycleVertices_range p hp]
    exact (hverts x).2 hxf
  obtain ⟨i,hi⟩ := hxrange
  have hstart : p.getVert i.val = x := hi
  have hpRoot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) := by rw [hroot]
  obtain ⟨q,hq,_,_,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hpRoot i.val (ZMod.val_lt i)
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG q hq hqface hqroot hbad hsmall
  have hqcover : ∀ z, z ∈ q.support ↔ z = p.getVert i.val ∨ z = y ∨ z ∈ I.precolor.vertices := by
    intro z
    rw [native_facial_cycle_support_iff I.embedding I.outer q hq hqface hqroot z,hcover,hstart]
  exact hbad (I.colourable_of_two_boundary_complement hG q hq hch hqface hqroot r hr hn hP y
    (hstart.symm ▸ hxy) (hstart.symm ▸ hxP) hyP hqcover hsmall)

/-- A prescribed native path cannot contain the whole simple outer cycle.
In a smallest counterexample its endpoint must have a neighbour outside that
path. This eliminates the zero-vertex boundary complement as well. -/
theorem colourable_of_all_outer_vertices_in_prescribed_path (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hAll : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨_,_,_,a,p,hp,_,_,hverts,_,_⟩ :=
    I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
    intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hcycleCover : ∀ x, x ∈ Set.range (walkCycleVertices p) ↔ x ∈ (∅ : Set V) ∨ x ∈ r.support := by
    intro x
    rw [walkCycleVertices_range p hp]
    change x ∈ p.support ↔ _
    simp only [Set.mem_empty_iff_false,false_or]
    exact ⟨fun hx => (hPv x).1 (hAll x ((hverts x).1 hx)),
      fun hx => (hverts x).2 (I.on_outer x ((hPv x).2 hx))⟩
  obtain ⟨x,hx,_⟩ := path_endpoint_has_cycle_complement_neighbour (walk_isCycleMap p hp) hlen r hr
    ∅ hcycleCover (by
      intro x y hx hy hxy
      have he := I.short_edges hxy (by simp [I.singleton x ((hPv x).2 hx)])
        (by simp [I.singleton y ((hPv y).2 hy)])
      simpa only [hP,BoundaryPrecolor.edges,List.mem_toFinset] using he)
  exact hx

/-- All cases with at most two unprescribed outer vertices are complete.
No placement or cardinality witness for the individual free vertices is needed. -/
theorem colourable_of_at_most_two_unprescribed_outer_vertices (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hcard : (Finset.univ.filter (fun x => OnOuterFace I.embedding I.outer x ∧
      x ∉ I.precolor.vertices)).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let F := Finset.univ.filter (fun x => OnOuterFace I.embedding I.outer x ∧ x ∉ I.precolor.vertices)
  have hF : ∀ x, x ∈ F ↔ OnOuterFace I.embedding I.outer x ∧ x ∉ I.precolor.vertices := by
    intro x; simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hne : F.Nonempty
  · obtain ⟨x,hx⟩ := hne
    by_cases hother : ∃ y ∈ F, y ≠ x
    · obtain ⟨y,hy,hyx⟩ := hother
      have hpair : F = {x,y} := by
        have hsubset : ({x,y} : Finset V) ⊆ F := by
          intro z hz
          rcases Finset.mem_insert.1 hz with h | h
          · exact h ▸ hx
          · exact (Finset.mem_singleton.1 h) ▸ hy
        exact (Finset.eq_of_subset_of_card_le hsubset
          (by rw [Finset.card_pair hyx.symm]; exact hcard)).symm
      apply I.colourable_of_two_unprescribed_outer_vertices r hr hn hP x y hyx.symm
        ((hF x).1 hx).2 ((hF y).1 hy).2 ?_ hsmall
      intro z
      constructor
      · intro hz
        by_cases hzP : z ∈ I.precolor.vertices
        · exact Or.inr (Or.inr hzP)
        · have hzF := (hF z).2 ⟨hz,hzP⟩
          rw [hpair,Finset.mem_insert,Finset.mem_singleton] at hzF
          exact hzF.elim Or.inl (fun h => Or.inr (Or.inl h))
      · rintro (hzx | hzy | hzP)
        · simpa only [hzx] using ((hF x).1 hx).1
        · simpa only [hzy] using ((hF y).1 hy).1
        · exact I.on_outer z hzP
    · apply I.colourable_of_unique_unprescribed_outer_vertex r hr hn hP x
        ((hF x).1 hx).1 ((hF x).1 hx).2 ?_ hsmall
      intro y hy hyP
      by_contra hyx
      exact hother ⟨y,(hF y).2 ⟨hy,hyP⟩,hyx⟩
  · apply I.colourable_of_all_outer_vertices_in_prescribed_path r hr hn hP ?_ hsmall
    intro x hx
    by_contra hxP
    exact hne ⟨x,(hF x).2 ⟨hx,hxP⟩⟩

/-- A remaining counterexample with a prescribed path has at least three
free boundary vertices. Its actual native facial cycle is longer than that
path by at least four edges. This is the short-complement normalization used
before selecting the remaining two- and three-path separators. -/
theorem prescribed_path_outer_cycle_length_lower_bound (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hverts : ∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) :
    r.length+4 ≤ p.length := by
  let F := p.support.toFinset \ I.precolor.vertices
  have hF : F = Finset.univ.filter (fun x => OnOuterFace I.embedding I.outer x ∧
      x ∉ I.precolor.vertices) := by
    ext x
    simp only [F,Finset.mem_sdiff,List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,hverts]
  have hFree : 3 ≤ F.card := by
    by_contra h
    apply hbad
    apply I.colourable_of_at_most_two_unprescribed_outer_vertices r hr hn hP ?_ hsmall
    rw [← hF]
    omega
  have hsub : I.precolor.vertices ⊆ p.support.toFinset := by
    intro x hx
    exact List.mem_toFinset.2 ((hverts x).2 (I.on_outer x hx))
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  change F.card + I.precolor.vertices.card = p.support.toFinset.card at hcount
  rw [cycle_support_card_eq_length p hp,hP,BoundaryPrecolor.vertices,
    List.toFinset_card_of_nodup hr.support_nodup,r.length_support] at hcount
  omega

end Thomassen.BoundaryInstance
