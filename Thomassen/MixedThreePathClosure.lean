/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedPrescribedThreePath

/-! Interior three-path cuts through a short end of the old prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The short-prefix mixed reduction applies to the arbitrary original face
in either orientation. Native facial placement of the unprescribed endpoint
is recovered internally. -/
theorem colourable_of_mixed_three_path_short_prefix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2) (u v2 : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert i)) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  have hdo : ∀ (J : BoundaryInstance G C), J.lists = I.lists → J.precolor = I.precolor →
      OnOuterFace J.embedding J.outer b → (¬ OnOuterFace J.embedding J.outer u) →
      (¬ OnOuterFace J.embedding J.outer v2) →
      ∀ (p : G.Walk a a) (hp : p.IsCycle),
      IsFacialCycleAlong J.embedding (walk_isCycleMap p hp) Set.univ →
      SameCycle J.embedding.facePerm J.outer (walkArcRoot p hp) →
      (∀ k ≤ r.length, r.getVert k = p.getVert k) → ListColourable G J.lists := by
    intro J hJL hJP hbJ huJ hzJ p hp hface hroot horder
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
    exact J.colourable_of_mixed_three_path_short_prefix hG p hp hface hroot r hr hn
      (hJP.trans hP) horder i k.val hi2 hir hrk hkp
      (by simpa only [hJL,hkv] using hbShort) u v2 huJ hzJ hui huz (by rwa [hkv]) hsmall
  apply hbad
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact hdo I rfl rfl hb hu hz p hp hface hroot horder
  · exact hdo I.mirror rfl rfl ((mirror_onOuterFace_iff I.embedding I.outer b).2 hb)
      (fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h))
      (fun h => hz ((mirror_onOuterFace_iff I.embedding I.outer v2).1 h)) p hp hface hroot horder

/-- The same mixed reduction is available at the terminal end of the old
prescription. Reversal preserves every old list, edge and singleton colour. -/
theorem colourable_of_mixed_three_path_short_suffix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2) (u v2 : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert (r.length-i))) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
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
  apply J.colourable_of_mixed_three_path_short_prefix_arbitrary_face r.reverse hr.reverse hnrev rfl
    i hi2 (by simpa only [Walk.length_reverse] using hir) b hb
    (fun h => hbP ((hPv b).1 h)) hbShort u v2 hu hz ?_ huz hzb hsmall
  simpa only [Walk.getVert_reverse] using hui

/-- Every mixed interior three-path from a prescribed vertex to a free
boundary vertex with an old short list is a complete strict-induction case.
No exception for six prescribed vertices remains in this three-path case. -/
theorem colourable_of_mixed_three_path_short_free_endpoint (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hxR : x ∈ r.support := by simpa only [hP,BoundaryPrecolor.vertices,List.mem_toFinset] using hx
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hxR
  have hlen : r.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at hn
    omega
  by_cases hprefix : i ≤ 2 ∧ i < r.length
  · exact I.colourable_of_mixed_three_path_short_prefix_arbitrary_face r hr hn hP i hprefix.1 hprefix.2
      b hb hbP hbShort u v2 hu hz (by rwa [hi]) huz hzb hsmall
  · apply I.colourable_of_mixed_three_path_short_suffix_arbitrary_face r hr hn hP (r.length-i)
      (by omega) (by omega) b hb hbP hbShort u v2 hu hz ?_ huz hzb hsmall
    rw [Nat.sub_sub_self hil,hi]
    exact hux

end Thomassen.BoundaryInstance
