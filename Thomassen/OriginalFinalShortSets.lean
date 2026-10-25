/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalSecondObstruction

/-! Actual augmented short sets for the two final-cut choices in source (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- On a cut omitting both old exceptional vertices, adding the next
boundary vertex to the short set gives an independent short set, provided
its other boundary neighbour is not short. -/
theorem final_cut_next_short_set (I : OriginalBoundaryInstance G C)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (h4 : p.getVert 4 ∉ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r=p.getVert 2 ∧ s=p.getVert 1) ∨ (r=p.getVert 1 ∧ s=p.getVert 2))
    (T : Set V) (h1T : p.getVert 1 ∉ T) (h2T : p.getVert 2 ∉ T) :
    OriginalShortSet (G.induce T) {x : T | x.1 ∈ I.short ∨ x.1 = p.getVert 3} := by
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hNext : ∀ x ∈ I.short, G.Adj (p.getVert 3) x → x ∉ T := by
    intro x hx h3x hxT
    rcases chordless_native_cycle_vertex_neighbours p hp hch 3 (by omega) (by omega)
      ((hverts x).2 (I.on_outer x hx)) h3x with h | h
    · exact h2T (h ▸ hxT)
    · exact h4 (h ▸ hx)
  left
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rcases hedge x.1 hx y.1 hy hxy with h | h
    · exact h2T (h.1 ▸ x.2)
    · exact h1T (h.1 ▸ x.2)
  · exact hNext x.1 hx (hy ▸ hxy.symm) x.2
  · exact hNext y.1 hy (hx ▸ hxy) y.2
  · exact hxy.ne (Subtype.ext (hx.trans hy.symm))

/-- On the other final-cut side, adding the predecessor of the old
exceptional edge leaves at most the edge to its own predecessor. The
source-(4) exclusion and the original unique-edge condition prove the
required two-path exclusion for that newly marked vertex. -/
theorem final_cut_predecessor_short_set (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r=p.getVert 2 ∧ s=p.getVert 1) ∨ (r=p.getVert 1 ∧ s=p.getVert 2))
    (T : Set V) (h1T : p.getVert 1 ∉ T) (h2T : p.getVert 2 ∉ T) :
    OriginalShortSet (G.induce T) {x : T | x.1 ∈ I.short ∨ x.1=a} := by
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have haFace : OnOuterFace I.embedding I.outer a := (hverts a).1 p.start_mem_support
  have holdInd : ∀ x : T, x.1 ∈ I.short → ∀ y : T, y.1 ∈ I.short → ¬ G.Adj x.1 y.1 := by
    intro x hx y hy hxy
    rcases hedge x.1 hx y.1 hy hxy with h | h
    · exact h2T (h.1 ▸ x.2)
    · exact h1T (h.1 ▸ x.2)
  have hNeighbour : ∀ x : T, x.1 ∈ I.short → G.Adj a x.1 →
      x.1 = p.getVert (p.length-1) := by
    intro x hx hax
    exact (chordless_native_cycle_root_neighbours p hp hch ((hverts x.1).2 (I.on_outer x.1 hx)) hax).resolve_left
      (fun h => h1T (h ▸ x.2))
  by_cases haT : a ∈ T
  · let aT : T := ⟨a,haT⟩
    by_cases hN : ∃ y : T, y.1 ∈ I.short ∧ G.Adj a y.1
    · obtain ⟨t,ht,hat⟩ := hN
      refine Or.inr ⟨aT,t,Or.inr rfl,Or.inl ht,hat,?_,?_⟩
      · intro x hx y hy hxy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact (holdInd x hx y hy hxy).elim
        · exact Or.inr ⟨Subtype.ext ((hNeighbour x hx (hy ▸ hxy.symm)).trans (hNeighbour t ht hat).symm),Subtype.ext hy⟩
        · exact Or.inl ⟨Subtype.ext hx,Subtype.ext ((hNeighbour y hy (hx ▸ hxy)).trans (hNeighbour t ht hat).symm)⟩
        · exact (hxy.ne (Subtype.ext (hx.trans hy.symm))).elim
      · intro z hz r hr hrl
        obtain ⟨hne,w,haw,hwz⟩ := (exists_two_path_iff_common_neighbour aT z).1 ⟨r,hr,hrl⟩
        rcases hz with hz | hz
        · by_cases hwface : OnOuterFace I.embedding I.outer w.1
          · rcases chordless_native_cycle_root_neighbours p hp hch ((hverts w.1).2 hwface) haw with hw | hw
            · exact h1T (hw ▸ w.2)
            · have he : w=t := Subtype.ext (hw.trans (hNeighbour t ht hat).symm)
              exact holdInd t ht z hz (he ▸ hwz)
          · exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall z.1 a w.1
              hz haFace (fun h => hne (Subtype.ext h.symm)) hwface hwz haw.symm
        · exact hne (Subtype.ext hz.symm)
    · left
      intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact holdInd x hx y hy hxy
      · exact hN ⟨x,hx,hy ▸ hxy.symm⟩
      · exact hN ⟨y,hy,hx ▸ hxy⟩
      · exact hxy.ne (Subtype.ext (hx.trans hy.symm))
  · left
    intro x hx y hy hxy
    exact holdInd x (hx.resolve_right (fun h => haT (h ▸ x.2)))
      y (hy.resolve_right (fun h => haT (h ▸ y.2))) hxy

end Thomassen.OriginalBoundaryInstance
