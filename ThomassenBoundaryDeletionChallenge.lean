/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedInteriorTwoPath

/-! Independent contracts for component face exposure, connected boundary
removal, the short-second/good-fourth-list branch and short face completion.
None of the four new proof modules is imported. The main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section ComponentBoundaryDeletionContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Flattened component vertices stay in the original induced vertex set. -/
lemma componentVertexSet_subset (S : Set V) (K : (G.induce S).ConnectedComponent) :
    componentVertexSet S K ⊆ S := by
  sorry

/-- An edge between retained vertices stays in its retained component. -/
lemma componentVertexSet_adj_closed (S : Set V) (K : (G.induce S).ConnectedComponent)
    {x y : V} (hx : x ∈ componentVertexSet S K) (hy : y ∈ S) (hxy : G.Adj x y) :
    y ∈ componentVertexSet S K := by
  sorry

/-- Every forward edge of the native old face has the original face orbit. -/
lemma native_facial_step_sameCycle [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (i : ℕ) (hi : i < p.length) :
    SameCycle M.facePerm outer ⟨(p.getVert i, p.getVert (i+1)), p.adj_getVert_succ hi⟩ := by
  sorry

/-- A component meeting the old native face has a forward old facial edge
entering the deleted set. Its last retained native index supplies that edge. -/
lemma native_cycle_component_exit {a : V} (p : G.Walk a a) (A : Set V) (ha : a ∈ A)
    (K : (G.induce Aᶜ).ConnectedComponent)
    (hmeet : ∃ x ∈ componentVertexSet Aᶜ K, x ∈ p.support) :
    ∃ i, ∃ _hi : i < p.length, p.getVert i ∈ componentVertexSet Aᶜ K ∧ p.getVert (i+1) ∈ A := by
  sorry

/-- Every retained component has an edge to the deleted set in a connected
original graph, even if that component meets no old face vertex. -/
lemma component_has_deleted_neighbour (hG : G.Preconnected) (A : Set V) (hA : A.Nonempty)
    (K : (G.induce Aᶜ).ConnectedComponent) :
    ∃ x ∈ componentVertexSet Aᶜ K, ∃ y ∈ A, G.Adj x y := by
  sorry

/-- A connected deletion touching the original native facial cycle exposes
its remaining neighbours on an actual face of every nontrivial component.
The old face incidences in that component are retained. No connectivity of the
whole remainder is assumed. -/
theorem exists_outer_component_after_connected_boundary_deletion [Fintype V]
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace M outer x → x ∈ p.support)
    (A : Set V) (ha : a ∈ A) (hA : ConnSet G A)
    (K : (G.induce Aᶜ).ConnectedComponent) [Nontrivial (componentVertexSet Aᶜ K)] :
    ∃ o : (G.induce (componentVertexSet Aᶜ K)).Dart,
      (∀ x : componentVertexSet Aᶜ K, OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M (componentVertexSet Aᶜ K)) o x) ∧
      (∀ x : componentVertexSet Aᶜ K, (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M (componentVertexSet Aᶜ K)) o x) := by
  sorry

end Thomassen

end ComponentBoundaryDeletionContracts

section ConnectedBoundaryDeletionContracts
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
  sorry

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
  sorry

end BoundaryInstance
end Thomassen

end ConnectedBoundaryDeletionContracts

section ShortBoundaryDeletionContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- At a noninitial native position, chordlessness gives the two actual
cyclic neighbours without indexing a supplied neighbour. -/
lemma chordless_native_cycle_vertex_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (i : ℕ) (hi : 0 < i) (hil : i + 1 ≤ p.length) {y : V}
    (hy : y ∈ p.support) (hadj : G.Adj (p.getVert i) y) :
    y = p.getVert (i-1) ∨ y = p.getVert (i+1) := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- For a prescription on the first old face edge, a smallest counterexample
has no interior vertex with two distinct old boundary neighbours. The remaining
old arc is proved prescription-free by actual native rebasing. -/
lemma interior_boundary_neighbour_unique_of_prescribed_edge (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (z u w : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hzu : G.Adj z u) (hzw : G.Adj z w) : u = w := by
  sorry

/-- Delete the prescribed initial vertex and its next two backward boundary
vertices. For a prescribed edge, a short second backward list and a three-list
at the fourth backward vertex suffice. Both kinds of residual short-edge
conflicts are excluded by the checked two/three-path cuts. The remainder may
have arbitrarily many components. -/
theorem colourable_of_prescribed_edge_short_second_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hlen : 6 ≤ p.length)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The remaining short-second-list branch must also have a short fourth
backward boundary list. This records the unresolved alternating-list pattern. -/
lemma prescribed_edge_fourth_boundary_list_le_two (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hlen : 6 ≤ p.length) (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-4))).card ≤ 2 := by
  sorry

/-- The prescribed-edge case with an actual six-vertex outer face is closed
under the strict main induction. The fourth backward vertex is adjacent to the
other prescribed endpoint and therefore cannot have a short list. -/
theorem colourable_of_prescribed_edge_six_vertex_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices) (hlen : p.length = 6)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end ShortBoundaryDeletionContracts

section ShortFaceCompletionContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V] {a : V}

/-- A compatible colouring of an actual outer cycle on at most six vertices
extends by the already proved full-prescribed-cycle case. The new instance
retains all original private three-lists and restores every original list. -/
theorem colourable_of_compatible_short_facial_cycle (I : BoundaryInstance G C)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hlen : p.length ≤ 6) (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ I.lists x)
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- With only an edge prescribed, an actual five-vertex outer face can be
coloured compatibly: choose its middle unprescribed colour first and then its
two three-list neighbours. The checked full-cycle reduction handles the interior. -/
theorem colourable_of_prescribed_edge_five_vertex_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : p.length = 5)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end ShortFaceCompletionContracts
