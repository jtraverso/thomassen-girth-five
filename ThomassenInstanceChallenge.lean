/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedEmbedding

/-!
# Contracts for boundary instances on a smaller vertex type

The prescribed walk, its edges and every list condition are transported together.
The whole-component hypothesis is essential for retaining the chosen old face.
This contract imports the already checked instance and induced-embedding
prerequisites, but not `Thomassen.InducedInstance`. The disconnected result
assumes induction only at strictly smaller cardinalities.
-/

@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma support_induce_card {a b : V} (p : G.Walk a b) (S : Set V)
    (h : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S h).support.toFinset.card = p.support.toFinset.card := by
  sorry

namespace BoundaryPrecolor

/-- Lift the same prescribed path or cycle; no edges or colours are changed. -/
noncomputable def induce (P : BoundaryPrecolor G) (S : Set V)
    (h : ∀ x ∈ P.vertices, x ∈ S) : BoundaryPrecolor (G.induce S) := by
  classical
  cases P with
  | empty => exact .empty
  | path p hp hn =>
    have hs : ∀ x ∈ p.support, x ∈ S := fun x hx => h x (List.mem_toFinset.2 hx)
    exact .path (p.induce S hs)
      (Walk.IsPath.of_map (f := (Embedding.induce S).toHom)
        (by simpa using hp))
      (by convert (support_induce_card p S hs).trans_le hn using 1
          apply congrArg Finset.card
          ext x
          simp)
  | cycle p hp hn =>
    have hs : ∀ x ∈ p.support, x ∈ S := fun x hx => h x (List.mem_toFinset.2 hx)
    exact .cycle (p.induce S hs)
      (Walk.IsCycle.of_map (f := (Embedding.induce S).toHom)
        (by simpa using hp))
      (by convert (support_induce_card p S hs).trans_le hn using 1
          apply congrArg Finset.card
          ext x
          simp)

lemma mem_vertices_induce (P : BoundaryPrecolor G) (S : Set V)
    (h : ∀ x ∈ P.vertices, x ∈ S) (x : S) :
    x ∈ (P.induce S h).vertices ↔ x.1 ∈ P.vertices := by
  sorry

lemma mem_edges_induce (P : BoundaryPrecolor G) (S : Set V)
    (h : ∀ x ∈ P.vertices, x ∈ S) (x y : S) :
    s(x, y) ∈ (P.induce S h).edges ↔ s(x.1, y.1) ∈ P.edges := by
  sorry

end BoundaryPrecolor

lemma reachable_of_onOuterFace [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {x : V} (hx : OnOuterFace M outer x) : G.Reachable outer.fst x := by
  sorry

namespace BoundaryInstance

variable [Fintype V]

/-- Restrict an instance to whole components containing its chosen outer dart
and all its prescribed vertices. Every original boundary condition is retained. -/
noncomputable def induceClosed (I : BoundaryInstance G C) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    (houter : I.outer.fst ∈ S) (hP : ∀ x ∈ I.precolor.vertices, x ∈ S) :
    BoundaryInstance (G.induce S) C := by
  let outer : (restrict G S).Dart :=
    ⟨I.outer.toProd, I.outer.adj, houter, hclosed _ houter _ I.outer.adj⟩
  have hface : ∀ x : S,
      OnOuterFace (inducedPlaneMap I.embedding S) (induceDartEquiv G S outer) x ↔
        OnOuterFace I.embedding I.outer x.1 :=
    inducedPlaneMap_onOuterFace_of_closed I.embedding S hclosed outer
  refine {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := induceDartEquiv G S outer
    precolor := I.precolor.induce S hP
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := ?_
    singleton := ?_
    proper_precolor := ?_
    boundary_lists := ?_
    interior_lists := ?_
    short_edges := ?_ }
  · intro x hx
    exact (hface x).2 (I.on_outer x.1
      ((BoundaryPrecolor.mem_vertices_induce _ S hP x).1 hx))
  · intro x hx
    exact I.singleton x.1 ((BoundaryPrecolor.mem_vertices_induce _ S hP x).1 hx)
  · intro x y hxy
    exact I.proper_precolor ((BoundaryPrecolor.mem_edges_induce _ S hP x y).1 hxy)
  · intro x hx hxp
    exact I.boundary_lists x.1 ((hface x).1 hx)
      (fun hp => hxp ((BoundaryPrecolor.mem_vertices_induce _ S hP x).2 hp))
  · intro x hx
    exact I.interior_lists x.1 (fun hf => hx ((hface x).2 hf))
  · intro x y hxy hx hy
    exact (BoundaryPrecolor.mem_edges_induce _ S hP x y).2
      (I.short_edges hxy hx hy)

/-- Every other component has full three-lists: the chosen face and its shorter
boundary lists belong to the component of the outer dart. -/
lemma list_ge_three_of_not_reachable (I : BoundaryInstance G C) {x : V}
    (hx : ¬ G.Reachable I.outer.fst x) : 3 ≤ (I.lists x).card := by
  sorry

/-- The disconnected case of the boundary-extension induction. The hypothesis
is induction only on strictly smaller vertex types, not extension at this size. -/
lemma colourable_of_disconnected (I : BoundaryInstance G C)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (hdisc : ¬ G.Preconnected) : ListColourable G I.lists := by
  sorry

end BoundaryInstance

end Thomassen
