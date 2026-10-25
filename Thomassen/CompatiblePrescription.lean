/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EndpointResidualConflicts

/-! Strict induction with a compatible replacement prescription. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Replace a prescribed path/cycle on a proper induced piece. Every changed
list and edge condition is checked before strict induction. The replacement
retains the old prescribed vertices of the piece and avoids all other old short
lists; its colours are compatible with the original lists. -/
theorem colourable_induced_with_compatible_prescription (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (P : BoundaryPrecolor G) (hPS : ∀ x ∈ P.vertices, x ∈ S)
    (f : V → C) (hf : ∀ x ∈ P.vertices, f x ∈ I.lists x)
    (hproper : ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, G.Adj x y → f x ≠ f y)
    (hch : ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, G.Adj x y → s(x,y) ∈ P.edges)
    (hOldP : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ P.vertices)
    (hface : ∀ x : S, x.1 ∈ P.vertices → OnOuterFace M o x)
    (hInterior : ∀ x : S, ¬ OnOuterFace M o x → 3 ≤ (I.lists x.1).card)
    (hCapture : ∀ x ∈ S, x ∉ P.vertices → (I.lists x).card ≤ 2 →
      ∀ y ∈ P.vertices, ¬ G.Adj x y)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ P.vertices → c x = f x.1 := by
  let Q := P.induce S hPS
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices := BoundaryPrecolor.mem_vertices_induce P S hPS
  let L : S → Finset C := fun x => if x.1 ∈ P.vertices then {f x.1} else I.lists x.1
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := M
    outer := o
    precolor := Q
    lists := L
    prescribed := fun x => f x.1
    on_outer := fun x hx => hface x ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact hproper x.1 ((hQv x).1 hends.1) y.1 ((hQv y).1 hends.2) (Q.adj_of_mem_edges he)
    boundary_lists := by
      intro x _ hx
      have hxP : x.1 ∉ P.vertices := fun h => hx ((hQv x).2 h)
      simpa only [L, ite_eq_right hxP] using I.outside_precolor_list_ge_two
        (fun h => hxP (hOldP x.1 x.2 h))
    interior_lists := by
      intro x hx
      have hxP : x.1 ∉ P.vertices := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hxP] using hInterior x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxP : x.1 ∈ P.vertices <;> by_cases hyP : y.1 ∈ P.vertices
      · exact (BoundaryPrecolor.mem_edges_induce P S hPS x y).2 (hch x.1 hxP y.1 hyP hxy)
      · have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyP] using hy
        exact (hCapture y.1 y.2 hyP hyOld x.1 hxP hxy.symm).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxP] using hx
        exact (hCapture x.1 x.2 hxP hxOld y.1 hyP hxy).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxP] using hx
        have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyP] using hy
        exact (hxP (hOldP x.1 x.2 (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)).1)).elim }
  obtain ⟨c, hc⟩ := hsmall S (G.induce S) J hSsmall
  change ∀ x : S, c x ∈ L x at hc
  have hfixed : ∀ x : S, x.1 ∈ P.vertices → c x = f x.1 := by
    intro x hx
    exact Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hx] using hc x)
  refine ⟨c, ?_, hfixed⟩
  intro x
  by_cases hx : x.1 ∈ P.vertices
  · rw [hfixed x hx]
    exact hf x.1 hx
  · simpa only [L, ite_eq_right hx] using hc x

end Thomassen.BoundaryInstance
