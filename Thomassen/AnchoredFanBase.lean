/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanCutvertex

/-! Bounded anchored fans retain their original prescribed path. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance

/-- A prescribed path of at most two edges, attached at its endpoint, plus
one further short neighbour of the root is a native induced path of at most
five vertices. The girth and old short-edge conditions supply chordlessness. -/
theorem rootStar_extension_of_attached_short_path (I : BoundaryInstance G C)
    {a t : V} (p : G.Walk a t) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ p.support)
    (b : V) (hbP : b ∉ I.precolor.vertices) (hba : G.Adj b a)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hproper : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (x : V) (hbx : G.Adj b x) (hxa : x ≠ a)
    (hbound : ∀ y, G.Adj b y → (I.lists y).card ≤ 2 → y = a ∨ y = x)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I b f := by
  have hbp : b ∉ p.support := fun h => hbP ((hP b).2 h)
  have hxp : x ∉ p.support := by
    intro h
    exact hxa (short_path_endpoint_neighbour_unique I.girth p hp hlen hbp hba x h hbx)
  have hbase : (Walk.cons hba p).IsPath := by
    apply Walk.IsPath.mk'
    exact List.nodup_cons.2 ⟨hbp, hp.support_nodup⟩
  by_cases hxs : (I.lists x).card ≤ 2
  · let q := Walk.cons hbx.symm (Walk.cons hba p)
    have hq : q.IsPath := by
      apply Walk.IsPath.mk'
      exact List.nodup_cons.2 ⟨by
        simp only [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hbx.ne.symm, hxp⟩, hbase.support_nodup⟩
    have hqbound : q.length ≤ 4 := by simp only [q, Walk.length_cons]; omega
    have hxt : ¬ G.Adj x t := I.short_not_adj_precolored
      (fun h => hxp ((hP x).1 h)) ((hP t).2 p.end_mem_support) hxs
    apply I.rootStar_extension_of_prescribed_path b hbface f hf hproper q hq (by omega)
      (four_edge_path_isChordless I.girth q hq hqbound hxt) ?_ N hN hsmall
    intro y
    simp only [q, Walk.support_cons, List.mem_cons]
    constructor
    · rintro (rfl | rfl | hy)
      · exact Or.inr (Or.inr ⟨hbx, hxs⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ((hP y).2 hy)
    · rintro (hyP | rfl | ⟨hby, hys⟩)
      · exact Or.inr (Or.inr ((hP y).1 hyP))
      · exact Or.inr (Or.inl rfl)
      · rcases hbound y hby hys with rfl | rfl
        · exact Or.inr (Or.inr p.start_mem_support)
        · exact Or.inl rfl
  · let q := Walk.cons hba p
    have hqbound : q.length ≤ 3 := by simp only [q, Walk.length_cons]; omega
    apply I.rootStar_extension_of_prescribed_path b hbface f hf hproper q hbase (by omega)
      (short_path_isChordless I.girth q hbase hqbound) ?_ N hN hsmall
    intro y
    simp only [q, Walk.support_cons, List.mem_cons]
    constructor
    · rintro (rfl | hy)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ((hP y).2 hy)
    · rintro (hyP | rfl | ⟨hby, hys⟩)
      · exact Or.inr ((hP y).1 hyP)
      · exact Or.inl rfl
      · rcases hbound y hby hys with rfl | rfl
        · exact Or.inr p.start_mem_support
        · exact (hxs hys).elim

end BoundaryInstance
end Thomassen
