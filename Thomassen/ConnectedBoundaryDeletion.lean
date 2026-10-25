/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ComponentBoundaryDeletion

/-! Residual-list induction after a possibly disconnecting boundary deletion. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Restrict an entire retained prescription to a retained component. Its
connected native path/cycle lies wholly in that component if it meets it. -/
lemma BoundaryPrecolor.exists_induce_component (Q : BoundaryPrecolor G) (S : Set V)
    (hQS : ∀ x ∈ Q.vertices, x ∈ S) (K : (G.induce S).ConnectedComponent) :
    ∃ P : BoundaryPrecolor (G.induce (componentVertexSet S K)),
      (∀ x : componentVertexSet S K, x ∈ P.vertices ↔ x.1 ∈ Q.vertices) ∧
      (∀ x y : componentVertexSet S K, s(x,y) ∈ P.edges ↔ s(x.1,y.1) ∈ Q.edges) := by
  let T := componentVertexSet S K
  by_cases hmeet : ∃ x ∈ T, x ∈ Q.vertices
  · obtain ⟨x, ⟨a, haK, hax⟩, hxQ⟩ := hmeet
    have hQT : ∀ y ∈ Q.vertices, y ∈ T := by
      intro y hyQ
      let P := Q.induce S hQS
      have haP : a ∈ P.vertices := (BoundaryPrecolor.mem_vertices_induce Q S hQS a).2 (hax.symm ▸ hxQ)
      have hyP : (⟨y, hQS y hyQ⟩ : S) ∈ P.vertices := (BoundaryPrecolor.mem_vertices_induce Q S hQS _).2 hyQ
      have heq := ConnectedComponent.sound (P.reachable_vertices haP hyP)
      exact ⟨⟨y, hQS y hyQ⟩, heq.symm.trans haK, rfl⟩
    exact ⟨Q.induce T hQT, BoundaryPrecolor.mem_vertices_induce Q T hQT, BoundaryPrecolor.mem_edges_induce Q T hQT⟩
  · refine ⟨.empty, ?_, ?_⟩
    · intro x
      exact iff_of_false (by simp)
        (fun h => hmeet ⟨x.1, x.2, h⟩)
    · intro x y
      exact iff_of_false (by simp)
        (fun h => hmeet ⟨x.1, x.2, (Q.endpoints_of_mem_edges h).1⟩)

namespace BoundaryInstance

/-- A connected deletion meeting the old face can disconnect the remainder.
Exact residual singleton, two-list and short-edge conditions suffice to build a
valid instance on every nontrivial retained component. Isolated vertices are
coloured directly and all original colours are restored by residual gluing. -/
theorem colourable_of_connected_boundary_deletion (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (Q : BoundaryPrecolor G) (hQA : ∀ x ∈ Q.vertices, x ∉ A)
    (hQface : ∀ x ∈ Q.vertices, OnOuterFace I.embedding I.outer x)
    (hQproper : ∀ {x y}, s(x,y) ∈ Q.edges → I.prescribed x ≠ I.prescribed y)
    (hSingleton : ∀ x ∈ Q.vertices, residual G I.lists A f x = {I.prescribed x})
    (hTwo : ∀ x, x ∉ A → x ∉ Q.vertices → 2 ≤ (residual G I.lists A f x).card)
    (hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → s(x,y) ∈ Q.edges)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let S : Set V := (↑A : Set V)ᶜ
  let r := residual G I.lists A f
  have hnonempty : ∀ x ∈ S, (r x).Nonempty := by
    intro x hx
    change (residual G I.lists A f x).Nonempty
    by_cases hxQ : x ∈ Q.vertices
    · rw [hSingleton x hxQ]
      exact Finset.singleton_nonempty _
    · exact Finset.card_pos.1 (by have := hTwo x hx hxQ; omega)
  have hcomponent : ∀ K : (G.induce S).ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, ∀ x, c x ∈ r x.1.1 := by
    intro K
    let T := componentVertexSet S K
    let φ := componentInduceIso S K
    have hc : ListColourable (G.induce T) (fun x => r x.1) := by
      by_cases hnt : Nontrivial T
      · let : Nontrivial T := hnt
        obtain ⟨o, hold, hnew⟩ := exists_outer_component_after_connected_boundary_deletion I.embedding I.outer hG
          p hp hface hroot hExact (↑A : Set V) ha hA K
        obtain ⟨P, hPv, hPe⟩ := Q.exists_induce_component S hQA K
        let J : BoundaryInstance (G.induce T) C := {
          girth := five_le_egirth_induce T I.girth
          embedding := inducedPlaneMap I.embedding T
          outer := o
          precolor := P
          lists := fun x => r x.1
          prescribed := fun x => I.prescribed x.1
          on_outer := fun x hx => hold x (hQface x.1 ((hPv x).1 hx))
          singleton := fun x hx => hSingleton x.1 ((hPv x).1 hx)
          proper_precolor := fun {x y} he => hQproper ((hPe x y).1 he)
          boundary_lists := fun x _ hx => hTwo x.1 (componentVertexSet_subset S K x.2) (fun h => hx ((hPv x).2 h))
          interior_lists := by
            intro x hx
            have hnotface : ¬ OnOuterFace I.embedding I.outer x.1 := fun h => hx (hold x h)
            have hr : r x.1 = I.lists x.1 := by
              apply residual_unchanged
              intro y hy hxy
              exact hx (hnew x ⟨y, hy, hxy⟩)
            rw [hr]
            exact I.interior_lists x.1 hnotface
          short_edges := by
            intro x y hxy hx hy
            exact (hPe x y).2 (hShort x.1 (componentVertexSet_subset S K x.2) y.1
              (componentVertexSet_subset S K y.2) hxy hx hy) }
        exact hsmall T (G.induce T) J (card_induced_vertices_lt T
          (x := a) (fun h => (componentVertexSet_subset S K h) ha))
      · let c : T → C := fun x => (hnonempty x.1 (componentVertexSet_subset S K x.2)).choose
        exact ⟨Coloring.mk c (fun {x y} hxy => (hnt hxy.nontrivial).elim), fun x =>
          (hnonempty x.1 (componentVertexSet_subset S K x.2)).choose_spec⟩
    obtain ⟨c, hc⟩ := hc
    exact ⟨c.comp φ.toHom, fun x => hc (φ x)⟩
  let c : (G.induce S).Coloring C := (G.induce S).homOfConnectedComponents (fun K => (hcomponent K).choose)
  have hc : ∀ x : S, c x ∈ r x.1 := fun x =>
    (hcomponent ((G.induce S).connectedComponentMk x)).choose_spec ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  let d : V → C := fun x => if hx : x ∈ A then f x else c ⟨x, hx⟩
  have hne : ∀ x ∈ Finset.univ \ A, x ∉ A := fun x hx => (Finset.mem_sdiff.1 hx).2
  apply (col_univ_iff I.lists).1
  apply glue_residual Finset.univ A I.lists f d hf hproper
  · intro x hx
    simpa only [d, dite_eq_right (hne x hx)] using hc ⟨x, hne x hx⟩
  · intro x hx y hy hxy
    simpa only [d, dite_eq_right (hne x hx), dite_eq_right (hne y hy)] using
      c.valid (show (G.induce S).Adj ⟨x, hne x hx⟩ ⟨y, hne y hy⟩ from hxy)

end BoundaryInstance
end Thomassen
