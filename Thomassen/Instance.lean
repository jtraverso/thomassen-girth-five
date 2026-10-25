/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Grotzsch.Regions
public import Thomassen.Minimal

/-!
# The boundary precolouring invariant

The outer face is an actual orbit of the face permutation of a plane map.
The precoloured subgraph is empty, a simple path, or a simple cycle, with at most
six vertices. Short-list edges must be edges of that subgraph, not just edges
joining arbitrary precoloured vertices.

This file specifies instances and proves elementary consequences. It does not
assert that all instances extend.
-/

@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Vertices incident with the face containing the specified dart. -/
def OnOuterFace (M : PlaneMap G) (outer : G.Dart) (x : V) : Prop :=
  ∃ e : G.Dart, Equiv.Perm.SameCycle M.facePerm outer e ∧ e.fst = x

lemma onOuterFace_self (M : PlaneMap G) (outer : G.Dart) :
    OnOuterFace M outer outer.fst :=
  ⟨outer, Equiv.Perm.SameCycle.refl _ _, rfl⟩

/-- The actual path or cycle to be precoloured; its edge set matters. -/
inductive BoundaryPrecolor (G : SimpleGraph V) where
  | empty
  | path {a b : V} (walk : G.Walk a b) (simple : walk.IsPath)
      (small : walk.support.toFinset.card ≤ 6)
  | cycle {a : V} (walk : G.Walk a a) (simple : walk.IsCycle)
      (small : walk.support.toFinset.card ≤ 6)

namespace BoundaryPrecolor

noncomputable def vertices : BoundaryPrecolor G → Finset V
  | .empty => ∅
  | .path p _ _ => p.support.toFinset
  | .cycle p _ _ => p.support.toFinset

noncomputable def edges : BoundaryPrecolor G → Finset (Sym2 V)
  | .empty => ∅
  | .path p _ _ => p.edges.toFinset
  | .cycle p _ _ => p.edges.toFinset

@[simp] lemma vertices_empty : (empty : BoundaryPrecolor G).vertices = ∅ := rfl
@[simp] lemma edges_empty : (empty : BoundaryPrecolor G).edges = ∅ := rfl

lemma card_vertices_le (P : BoundaryPrecolor G) : P.vertices.card ≤ 6 := by
  cases P with
  | empty => simp
  | path _ _ h => exact h
  | cycle _ _ h => exact h

lemma adj_of_mem_edges (P : BoundaryPrecolor G) {x y : V}
    (h : s(x, y) ∈ P.edges) : G.Adj x y := by
  cases P with
  | empty => simp at h
  | path p _ _ => exact p.adj_of_mem_edges (List.mem_toFinset.1 h)
  | cycle p _ _ => exact p.adj_of_mem_edges (List.mem_toFinset.1 h)

lemma endpoints_of_mem_edges (P : BoundaryPrecolor G) {x y : V}
    (h : s(x, y) ∈ P.edges) : x ∈ P.vertices ∧ y ∈ P.vertices := by
  cases P with
  | empty => simp at h
  | path p _ _ =>
    exact ⟨List.mem_toFinset.2 (p.fst_mem_support_of_mem_edges (List.mem_toFinset.1 h)),
      List.mem_toFinset.2 (p.snd_mem_support_of_mem_edges (List.mem_toFinset.1 h))⟩
  | cycle p _ _ =>
    exact ⟨List.mem_toFinset.2 (p.fst_mem_support_of_mem_edges (List.mem_toFinset.1 h)),
      List.mem_toFinset.2 (p.snd_mem_support_of_mem_edges (List.mem_toFinset.1 h))⟩

end BoundaryPrecolor

/-- The stronger invariant used by the short precolouring-extension proof.
No extension or list-colourability assumption is a field of this structure. -/
structure BoundaryInstance (G : SimpleGraph V) (C : Type v) where
  girth : 5 ≤ G.egirth
  embedding : PlaneMap G
  outer : G.Dart
  precolor : BoundaryPrecolor G
  lists : V → Finset C
  prescribed : V → C
  on_outer : ∀ x ∈ precolor.vertices, OnOuterFace embedding outer x
  singleton : ∀ x ∈ precolor.vertices, lists x = {prescribed x}
  proper_precolor : ∀ {x y}, s(x, y) ∈ precolor.edges → prescribed x ≠ prescribed y
  boundary_lists : ∀ x, OnOuterFace embedding outer x → x ∉ precolor.vertices →
    2 ≤ (lists x).card
  interior_lists : ∀ x, ¬ OnOuterFace embedding outer x → 3 ≤ (lists x).card
  short_edges : ∀ {x y}, G.Adj x y → (lists x).card ≤ 2 → (lists y).card ≤ 2 →
    s(x, y) ∈ precolor.edges

namespace BoundaryInstance

lemma list_nonempty (I : BoundaryInstance G C) (x : V) : (I.lists x).Nonempty := by
  by_cases hx : x ∈ I.precolor.vertices
  · rw [I.singleton x hx]
    exact Finset.singleton_nonempty _
  · by_cases hb : OnOuterFace I.embedding I.outer x
    · have h := I.boundary_lists x hb hx
      exact Finset.card_pos.1 (by omega)
    · have h := I.interior_lists x hb
      exact Finset.card_pos.1 (by omega)

lemma proper_on_precolored_vertices (I : BoundaryInstance G C) {x y : V}
    (hx : x ∈ I.precolor.vertices) (hy : y ∈ I.precolor.vertices)
    (hxy : G.Adj x y) : I.prescribed x ≠ I.prescribed y := by
  apply I.proper_precolor
  apply I.short_edges hxy
  · simp [I.singleton x hx]
  · simp [I.singleton y hy]

lemma outside_precolor_list_ge_two (I : BoundaryInstance G C) {x : V}
    (hx : x ∉ I.precolor.vertices) : 2 ≤ (I.lists x).card := by
  by_cases hb : OnOuterFace I.embedding I.outer x
  · exact I.boundary_lists x hb hx
  · exact (by omega : 2 ≤ 3).trans (I.interior_lists x hb)

lemma singleton_iff_precolored (I : BoundaryInstance G C) (x : V) :
    (I.lists x).card = 1 ↔ x ∈ I.precolor.vertices := by
  constructor
  · intro h
    by_contra hx
    have := I.outside_precolor_list_ge_two hx
    omega
  · intro hx
    simp [I.singleton x hx]

/-- A short-list edge is exactly an edge of the prescribed path or cycle. -/
lemma short_edge_iff (I : BoundaryInstance G C) {x y : V} (hxy : G.Adj x y) :
    (I.lists x).card ≤ 2 ∧ (I.lists y).card ≤ 2 ↔ s(x, y) ∈ I.precolor.edges := by
  constructor
  · exact fun h => I.short_edges hxy h.1 h.2
  · intro h
    obtain ⟨hx, hy⟩ := I.precolor.endpoints_of_mem_edges h
    simp [I.singleton x hx, I.singleton y hy]

/-- Vertices with two-list bounds outside the prescribed subgraph cannot be
adjacent to any precoloured vertex. -/
lemma short_not_adj_precolored (I : BoundaryInstance G C) {x y : V}
    (hx : x ∉ I.precolor.vertices) (hy : y ∈ I.precolor.vertices)
    (hshort : (I.lists x).card ≤ 2) : ¬ G.Adj x y := by
  intro hxy
  have he := I.short_edges hxy hshort (by simp [I.singleton y hy])
  exact hx (I.precolor.endpoints_of_mem_edges he).1

/-- The base case with every vertex already prescribed is unconditional. -/
lemma colourable_of_all_precolored (I : BoundaryInstance G C)
    (hP : ∀ x, x ∈ I.precolor.vertices) : ListColourable G I.lists := by
  refine ⟨Coloring.mk I.prescribed (fun {x y} hxy =>
    I.proper_on_precolored_vertices (hP x) (hP y) hxy), ?_⟩
  intro x
  change I.prescribed x ∈ I.lists x
  simp [I.singleton x (hP x)]

/-- A list colouring already extends the prescribed singleton lists. -/
lemma extends_prescribed (I : BoundaryInstance G C) (c : G.Coloring C)
    (hc : ∀ x, c x ∈ I.lists x) : ∀ x ∈ I.precolor.vertices, c x = I.prescribed x := by
  intro x hx
  simpa [I.singleton x hx] using hc x

/-- Initialization from a three-list assignment uses the empty precoloured graph.
This does not supply the still-missing extension theorem. -/
noncomputable def of_three_lists (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card) (c : V → C) : BoundaryInstance G C where
  girth := hg
  embedding := M
  outer := outer
  precolor := .empty
  lists := L
  prescribed := c
  on_outer := by simp
  singleton := by simp
  proper_precolor := by simp
  boundary_lists := fun x _ _ => by have := hL x; omega
  interior_lists := fun x _ => hL x
  short_edges := by
    intro x y _ hx _
    have := hL x
    omega

end BoundaryInstance
end Thomassen
