/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedEmbedding

/-!
# Boundary instances on a smaller vertex type

The prescribed walk, its edges and every list condition are transported together.
The whole-component hypothesis is essential for retaining the chosen old face.
No list-colouring extension theorem is assumed by these constructions.
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
  classical
  have hi : (p.induce S h).support.toFinset.image Subtype.val = p.support.toFinset := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset, Walk.support_induce,
      List.mem_attachWith]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h x hx⟩, hx, rfl⟩
  rw [← hi, Finset.card_image_of_injective _ Subtype.val_injective]

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
  classical
  cases P with
  | empty => simp [induce]
  | path p hp hn => simp [induce, vertices, Walk.support_induce]
  | cycle p hp hn => simp [induce, vertices, Walk.support_induce]

lemma mem_edges_induce (P : BoundaryPrecolor G) (S : Set V)
    (h : ∀ x ∈ P.vertices, x ∈ S) (x y : S) :
    s(x, y) ∈ (P.induce S h).edges ↔ s(x.1, y.1) ∈ P.edges := by
  classical
  cases P with
  | empty => simp [induce]
  | path p hp hn =>
    have hs : ∀ x ∈ p.support, x ∈ S := fun x hx => h x (List.mem_toFinset.2 hx)
    have hm := congrArg Walk.edges (p.map_induce hs)
    simp only [Walk.edges_map] at hm
    simp only [induce, edges, List.mem_toFinset]
    have hm' : List.map (Sym2.map (Subtype.val : S → V))
        (p.induce S hs).edges = p.edges := by
      simpa [Embedding.induce, Embedding.comap] using hm
    have hi := Sym2.map.injective (f := (Subtype.val : S → V)) Subtype.val_injective
    have hmem := congrArg (fun es => s(x.1, y.1) ∈ es) hm'
    rw [List.mem_map] at hmem
    apply Iff.trans ?_ (iff_of_eq hmem)
    constructor
    · intro he
      exact ⟨s(x, y), he, rfl⟩
    · rintro ⟨e, he, heq⟩
      have heq' : Sym2.map (Subtype.val : S → V) e =
          Sym2.map (Subtype.val : S → V) s(x, y) := by simpa using heq
      exact hi heq' ▸ he
  | cycle p hp hn =>
    have hs : ∀ x ∈ p.support, x ∈ S := fun x hx => h x (List.mem_toFinset.2 hx)
    have hm := congrArg Walk.edges (p.map_induce hs)
    simp only [Walk.edges_map] at hm
    simp only [induce, edges, List.mem_toFinset]
    have hm' : List.map (Sym2.map (Subtype.val : S → V))
        (p.induce S hs).edges = p.edges := by
      simpa [Embedding.induce, Embedding.comap] using hm
    have hi := Sym2.map.injective (f := (Subtype.val : S → V)) Subtype.val_injective
    have hmem := congrArg (fun es => s(x.1, y.1) ∈ es) hm'
    rw [List.mem_map] at hmem
    apply Iff.trans ?_ (iff_of_eq hmem)
    constructor
    · intro he
      exact ⟨s(x, y), he, rfl⟩
    · rintro ⟨e, he, heq⟩
      have heq' : Sym2.map (Subtype.val : S → V) e =
          Sym2.map (Subtype.val : S → V) s(x, y) := by simpa using heq
      exact hi heq' ▸ he

end BoundaryPrecolor

lemma reachable_of_onOuterFace [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {x : V} (hx : OnOuterFace M outer x) : G.Reachable outer.fst x := by
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
  have hwalk : ∀ k : ℕ, G.Reachable outer.fst ((M.facePerm ^ k) outer).fst := by
    intro k
    induction k with
    | zero => exact Reachable.refl _
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hf : (M.facePerm ((M.facePerm ^ k) outer)).fst =
          ((M.facePerm ^ k) outer).snd :=
        M.isRotationSystem.fst_apply _
      rw [hf]
      exact ih.trans ((M.facePerm ^ k) outer).adj.reachable
  simpa only [hn] using hwalk n

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
    (hx : ¬ G.Reachable I.outer.fst x) : 3 ≤ (I.lists x).card :=
  I.interior_lists x (fun hf => hx (reachable_of_onOuterFace I.embedding I.outer hf))

/-- The disconnected case of the boundary-extension induction. The hypothesis
is induction only on strictly smaller vertex types, not extension at this size. -/
lemma colourable_of_disconnected (I : BoundaryInstance G C)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (hdisc : ¬ G.Preconnected) : ListColourable G I.lists := by
  classical
  let S : Set V := {x | G.Reachable I.outer.fst x}
  have hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S :=
    fun _ ha _ hab => ha.trans hab.reachable
  have hroot : I.outer.fst ∈ S := Reachable.refl _
  have hout : ∃ x, x ∉ S := by
    by_contra h
    have hall : ∀ x, G.Reachable I.outer.fst x := by simpa [S] using h
    exact hdisc (fun x y => (hall x).symm.trans (hall y))
  obtain ⟨x, hx⟩ := hout
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ S :=
    fun x hxp => reachable_of_onOuterFace I.embedding I.outer (I.on_outer x hxp)
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) (I.induceClosed S hclosed hroot hP)
    (card_induced_vertices_lt S hx)
  have hTsmall : Nat.card (Sᶜ : Set V) < Nat.card V :=
    card_induced_vertices_lt Sᶜ (by simpa using hroot)
  have hTlists : ∀ y : (Sᶜ : Set V), 3 ≤ (I.lists y.1).card :=
    fun y => I.list_ge_three_of_not_reachable y.2
  have hTcolour : ListColourable (G.induce Sᶜ) (fun y => I.lists y.1) := by
    by_cases hedge : ∃ a b : (Sᶜ : Set V), (G.induce Sᶜ).Adj a b
    · obtain ⟨a, b, hab⟩ := hedge
      exact hsmall (Sᶜ : Set V) (G.induce Sᶜ)
        (of_three_lists (inducedPlaneMap I.embedding Sᶜ) ⟨(a, b), hab⟩
          (five_le_egirth_induce Sᶜ I.girth) (fun y => I.lists y.1) hTlists
          (fun y => I.prescribed y.1)) hTsmall
    · let f : (Sᶜ : Set V) → C := fun y => (I.list_nonempty y.1).choose
      exact ⟨Coloring.mk f (fun {a b} hab => False.elim (hedge ⟨a, b, hab⟩)),
        fun y => (I.list_nonempty y.1).choose_spec⟩
  obtain ⟨cT, hcT⟩ := hTcolour
  let f : V → C := fun y => if hy : y ∈ S then cS ⟨y, hy⟩ else cT ⟨y, hy⟩
  refine ⟨Coloring.mk f ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ S
    · have hb := hclosed a ha b hab
      have h := cS.valid (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      simpa only [f, dite_eq_left ha, dite_eq_left hb] using h
    · have hb : b ∉ S := fun hb => ha (hclosed b hb a hab.symm)
      have h := cT.valid (show (G.induce Sᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      simpa only [f, dite_eq_right ha, dite_eq_right hb] using h
  · intro y
    change f y ∈ I.lists y
    by_cases hy : y ∈ S
    · simpa only [f, dite_eq_left hy, induceClosed] using hcS ⟨y, hy⟩
    · simpa only [f, dite_eq_right hy] using hcT ⟨y, hy⟩

end BoundaryInstance

end Thomassen
