/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ThreeVertexAlternatingLists

/-! Compatible colouring of the six-cycle with three prescribed vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- Three consecutive prescribed vertices on an actual six-vertex face
extend: colour the middle free vertex first, then its two three-list neighbours.
The existing compatible full-cycle theorem handles all interior vertices. -/
theorem colourable_of_three_prescribed_vertices_six_vertex_face (I : BoundaryInstance G C)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x=a ∨ x=p.getVert 1 ∨ x=p.getVert 2)
    (hlen : p.length=6)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hne : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (by change i ≤ p.length-1; omega) (by change j ≤ p.length-1; omega) he)
  have hna : ∀ i, 0 < i → i < 6 → p.getVert i ≠ a := by
    intro i hi hil
    simpa only [Walk.getVert_zero] using hne i 0 hil (by omega) (by omega)
  have hnotP : ∀ i, 3 ≤ i → i < 6 → p.getVert i ∉ I.precolor.vertices := by
    intro i hi hil hx
    rcases (hP _).1 hx with h | h | h
    · exact hna i (by omega) hil h
    · exact hne i 1 hil (by omega) (by omega) h
    · exact hne i 2 hil (by omega) (by omega) h
  have haP := (hP a).2 (Or.inl rfl)
  have h1P := (hP (p.getVert 1)).2 (Or.inr (Or.inl rfl))
  have h2P := (hP (p.getVert 2)).2 (Or.inr (Or.inr rfl))
  have h3three : 3 ≤ (I.lists (p.getVert 3)).card := by
    by_contra h
    exact I.short_not_adj_precolored (hnotP 3 (by omega) (by omega)) h2P (by omega)
      (p.adj_getVert_succ (by omega : 2 < p.length)).symm
  have h5three : 3 ≤ (I.lists (p.getVert 5)).card := by
    by_contra h
    exact I.short_not_adj_precolored (hnotP 5 (by omega) (by omega)) haP (by omega)
      (by simpa only [show 5+1=6 by rfl,← hlen,Walk.getVert_length] using p.adj_getVert_succ (by omega : 5 < p.length))
  obtain ⟨c4,hc4⟩ := I.list_nonempty (p.getVert 4)
  have hchoice : ∀ x, 3 ≤ (I.lists x).card → ∀ c d : C, ∃ e ∈ I.lists x, e ≠ c ∧ e ≠ d := by
    intro x hx c d
    obtain ⟨e,he,hen⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({c,d} : Finset C)) (t := I.lists x) (Finset.card_le_two.trans_lt (by omega))
    have hn : e ≠ c ∧ e ≠ d := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hen
    exact ⟨e,he,hn⟩
  obtain ⟨c3,hc3,hc32,hc34⟩ := hchoice (p.getVert 3) h3three (I.prescribed (p.getVert 2)) c4
  obtain ⟨c5,hc5,hc50,hc54⟩ := hchoice (p.getVert 5) h5three (I.prescribed a) c4
  let F : V → C := fun x => if x=p.getVert 3 then c3 else if x=p.getVert 4 then c4
    else if x=p.getVert 5 then c5 else I.prescribed x
  have hfOld : ∀ x ∈ I.precolor.vertices, F x = I.prescribed x := by
    intro x hx
    simp only [F,ite_eq_right (fun (h:x=p.getVert 3) => hnotP 3 (by omega) (by omega) (h ▸ hx)),
      ite_eq_right (fun (h:x=p.getVert 4) => hnotP 4 (by omega) (by omega) (h ▸ hx)),
      ite_eq_right (fun (h:x=p.getVert 5) => hnotP 5 (by omega) (by omega) (h ▸ hx))]
  have hf0 : F (p.getVert 0) = I.prescribed a := by simpa only [Walk.getVert_zero] using hfOld a haP
  have hf1 : F (p.getVert 1) = I.prescribed (p.getVert 1) := hfOld _ h1P
  have hf2 : F (p.getVert 2) = I.prescribed (p.getVert 2) := hfOld _ h2P
  have hf3 : F (p.getVert 3) = c3 := by simp only [F,ite_true]
  have hf4 : F (p.getVert 4) = c4 := by simp only [F,ite_eq_right (hne 4 3 (by omega) (by omega) (by omega)),ite_true]
  have hf5 : F (p.getVert 5) = c5 := by simp only [F,ite_eq_right (hne 5 3 (by omega) (by omega) (by omega)),
    ite_eq_right (hne 5 4 (by omega) (by omega) (by omega)),ite_true]
  have hf6 : F (p.getVert 6) = I.prescribed a := by simpa only [← hlen,Walk.getVert_length] using hfOld a haP
  have hFmem : ∀ x ∈ p.support, F x ∈ I.lists x := by
    intro x hx
    obtain ⟨i,hix,hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6) with he | he | he | he | he | he | he
    all_goals subst i; rw [← hix]
    · rw [hf0,Walk.getVert_zero,I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [hf1,I.singleton _ h1P]; exact Finset.mem_singleton_self _
    · rw [hf2,I.singleton _ h2P]; exact Finset.mem_singleton_self _
    · rw [hf3]; exact hc3
    · rw [hf4]; exact hc4
    · rw [hf5]; exact hc5
    · rw [hf6,← hlen,Walk.getVert_length,I.singleton a haP]; exact Finset.mem_singleton_self _
  have hedge : ∀ i, i < p.length → F (p.getVert i) ≠ F (p.getVert (i+1)) := by
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5) with he | he | he | he | he | he
    all_goals subst i
    · simpa only [hf0,hf1] using I.proper_on_precolored_vertices haP h1P
        (by simpa only [Walk.getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length))
    · simpa only [hf1,hf2] using I.proper_on_precolored_vertices h1P h2P (p.adj_getVert_succ (by omega : 1 < p.length))
    · simpa only [hf2,hf3] using hc32.symm
    · simpa only [hf3,hf4] using hc34
    · simpa only [hf4,hf5] using hc54.symm
    · simpa only [hf5,hf6] using hc50
  have hch : p.IsChordless := by
    let : NeZero p.length := ⟨by omega⟩
    have hc := short_cycle_isChordless I.girth (walk_isCycleMap p hp) hp.three_le_length (by omega)
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    apply (walkCycleVertices_edges p hp x y).1
    apply cyclicSubgraph_of_chordless hc
    · rw [walkCycleVertices_range p hp]; exact hx
    · rw [walkCycleVertices_range p hp]; exact hy
    · exact hxy
  apply I.colourable_of_compatible_short_facial_cycle p hp hface hroot hExact (by omega) F hFmem ?_ hsmall
  intro x hx y hy hxy
  obtain ⟨i,hi,he⟩ := p.mk_mem_edges_iff_exists.1 (hch.mem_edges hx hy hxy)
  rcases Sym2.eq_iff.1 he with he | he
  · simpa only [he.1,he.2] using hedge i hi
  · simpa only [he.1,he.2] using (hedge i hi).symm

end Thomassen.BoundaryInstance
