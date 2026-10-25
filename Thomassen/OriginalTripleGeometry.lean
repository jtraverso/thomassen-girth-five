/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFiveFaceAttachments

/-! Classification of residual short edges in original step (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Old short vertices and exposed neighbours remaining after a finite deletion. -/
def exposedShortSet (G : SimpleGraph V) (A : Set V) (D : Finset V) : Set V :=
  {z | z ∉ D ∧ (z ∈ A ∨ ∃ w ∈ D, G.Adj z w)}

namespace OriginalBoundaryInstance
variable [Fintype V]

/-- After deleting positions 0,1,2, every residual short edge joins genuinely
new short vertices attached to opposite ends of that deleted path. The endpoint
attached to position 0 is interior. This proves the first classification in
original step (10), using the preceding short vertex from step (9). -/
theorem triple_short_edge_crossing (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htA : p.getVert (p.length-1) ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False)
    {u v : V}
    (hu : u ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hv : v ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}) (huv : G.Adj u v) :
    u ∉ I.short ∧ v ∉ I.short ∧
      ((G.Adj (p.getVert 2) u ∧ G.Adj a v ∧ ¬ OnOuterFace I.embedding I.outer v) ∨
       (G.Adj a u ∧ G.Adj (p.getVert 2) v ∧ ¬ OnOuterFace I.embedding I.outer u)) := by
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have h01 : G.Adj a (p.getVert 1) := by
    simpa only [Walk.getVert_zero,zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
  have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega : 1 < p.length)
  let D : Finset V := {a,p.getVert 1,p.getVert 2}
  have hne : ∀ z, z ∉ D → z ≠ a ∧ z ≠ p.getVert 1 ∧ z ≠ p.getVert 2 := by
    intro z hz
    simpa only [D,Finset.mem_insert,Finset.mem_singleton,not_or] using hz
  have hOldNew : ∀ z, z ∉ D → z ∈ I.short → ∀ w, w ∉ D → w ∉ I.short →
      (∃ t ∈ D, G.Adj w t) → ¬ G.Adj z w := by
    intro z hzD hzA w hwD hwA hwn hzw
    obtain ⟨t,ht,hwt⟩ := hwn
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht
    · subst t
      by_cases hwface : OnOuterFace I.embedding I.outer w
      · rcases chordless_native_cycle_root_neighbours p hp hch ((hverts w).2 hwface) hwt.symm with hw | hw
        · exact (hne w hwD).2.1 hw
        · exact hwA (hw ▸ htA)
      · exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall z a w hzA
          ((hverts a).1 p.start_mem_support) (hne z hzD).1 hwface hzw.symm hwt
    · subst t
      by_cases hwface : OnOuterFace I.embedding I.outer w
      · rcases chordless_native_cycle_vertex_neighbours p hp hch 1 (by omega) (by omega)
          ((hverts w).2 hwface) hwt.symm with hw | hw
        · exact (hne w hwD).1 (by simpa only [Nat.sub_self,Walk.getVert_zero] using hw)
        · exact (hne w hwD).2.2 hw
      · exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall z (p.getVert 1) w hzA
          (I.on_outer _ hyA) (hne z hzD).2.1 hwface hzw.symm hwt
    · subst t
      exact no_common_neighbour_of_no_two_path (p.getVert 2) I.short hNoX hzA
        (hne z hzD).2.2.symm hwt.symm hzw.symm
  have hnew : ∀ z, z ∈ exposedShortSet G I.short D → ∀ w,
      w ∈ exposedShortSet G I.short D → G.Adj z w → z ∉ I.short := by
    intro z hz w hw hzw hzA
    by_cases hwA : w ∈ I.short
    · rcases hedge z hzA w hwA hzw with h | h
      · exact (hne z hz.1).2.2 h.1
      · exact (hne z hz.1).2.1 h.1
    · exact hOldNew z hz.1 hzA w hw.1 hwA (hw.2.resolve_left hwA) hzw
  have huNew := hnew u hu v hv huv
  have hvNew := hnew v hv u hu huv.symm
  have hattach : ∀ z, z ∈ exposedShortSet G I.short D → z ∉ I.short →
      G.Adj a z ∨ G.Adj (p.getVert 1) z ∨ G.Adj (p.getVert 2) z := by
    intro z hz hzA
    obtain ⟨t,ht,hzt⟩ := hz.2.resolve_left hzA
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl hzt.symm
    · exact Or.inr (Or.inl hzt.symm)
    · exact Or.inr (Or.inr hzt.symm)
  have hInterior : ∀ z, z ∈ exposedShortSet G I.short D → z ∉ I.short → G.Adj a z →
      ¬ OnOuterFace I.embedding I.outer z := by
    intro z hz hzA haz hzf
    rcases chordless_native_cycle_root_neighbours p hp hch ((hverts z).2 hzf) haz with he | he
    · exact (hne z hz.1).2.1 he
    · exact hzA (he ▸ htA)
  refine ⟨huNew,hvNew,?_⟩
  rcases deleted_two_edge_path_adjacent_neighbors I.girth h01 h12 hu.1 hv.1
      (hattach u hu huNew) (hattach v hv hvNew) huv with h | h
  · exact Or.inr ⟨h.1,h.2,hInterior u hu huNew h.1⟩
  · exact Or.inl ⟨h.1,h.2,hInterior v hv hvNew h.2⟩

/-- All residual short edges from that triple deletion coincide. The proof
includes the possibility that the first attachment is the next old-boundary
vertex, which cannot be treated by an interior-only three-path lemma. -/
theorem triple_short_edge_unique (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htA : p.getVert (p.length-1) ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False)
    {q₁ q₂ : V}
    (hq₁ : q₁ ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₂ : q₂ ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (h2q : G.Adj (p.getVert 2) q₁) (hqq : G.Adj q₁ q₂) (hqa : G.Adj q₂ a) :
    ∀ u ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2},
      ∀ v ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}, G.Adj u v →
        (u=q₁ ∧ v=q₂) ∨ (u=q₂ ∧ v=q₁) := by
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hq1ne : q₁ ≠ p.getVert 1 := by
    intro h
    exact hq₁.1 (by simp [h])
  have hq2inner : ¬ OnOuterFace I.embedding I.outer q₂ := by
    obtain ⟨_,_,h | h⟩ := I.triple_short_edge_crossing hbad hsmall p hp hch hface hroot hyA hxA htA hedge hNoX hq₁ hq₂ hqq
    · exact h.2.2
    · exact (neighbors_nonadjacent I.girth hqa hqq.symm h.1).elim
  intro u hu v hv huv
  have hune : u ≠ p.getVert 1 := by intro h; exact hu.1 (by simp [h])
  have hvne : v ≠ p.getVert 1 := by intro h; exact hv.1 (by simp [h])
  obtain ⟨_,_,h | h⟩ := I.triple_short_edge_crossing hbad hsmall p hp hch hface hroot hyA hxA htA hedge hNoX hu hv huv
  · obtain ⟨h₁,h₂⟩ := I.three_path_across_two_face_edges_unique_allow_boundary hG p hp hch hface hroot hlen
      q₁ q₂ u v hq1ne hune hq2inner h.2.2 h2q hqq hqa h.1 huv h.2.1.symm hbad hsmall
    exact Or.inl ⟨h₁.symm,h₂.symm⟩
  · obtain ⟨h₁,h₂⟩ := I.three_path_across_two_face_edges_unique_allow_boundary hG p hp hch hface hroot hlen
      q₁ q₂ v u hq1ne hvne hq2inner h.2.2 h2q hqq hqa h.2.1 huv.symm h.1.symm hbad hsmall
    exact Or.inr ⟨h₂.symm,h₁.symm⟩

end OriginalBoundaryInstance
end Thomassen
