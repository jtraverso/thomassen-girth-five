/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EndpointResidualConflicts

/-! Independent contracts for compatible replacement prescriptions and the
prescribed-prefix two-path cuts. Neither new proof module is imported.
The unconditional main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section CompatiblePrescriptionContracts
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
  sorry

end Thomassen.BoundaryInstance

end CompatiblePrescriptionContracts

section PrescribedInteriorTwoPathContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- An interior two-path from the initial prescribed endpoint to internal
position three or four is a complete induction case when the prescription
follows the forward native facial order. The inner cycle has at most six
vertices; replacing its prescribed prefix leaves a path on at most five. -/
theorem colourable_of_prescribed_prefix_interior_two_path (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (d : ℕ) (hd : d = 3 ∨ d = 4) (hdr : d < r.length)
    (x : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hxa : G.Adj x a) (hxd : G.Adj x (r.getVert d))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The first forward boundary vertex being prescribed fixes the orientation
of the whole original prescribed path. This uses its actual native edge set
and the previously checked facial path-order theorem. -/
lemma prescribed_path_forward_of_first_face_vertex (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ k ≤ r.length, r.getVert k = p.getVert k := by
  sorry

/-- Once the first forward boundary vertex is prescribed, no interior
vertex can join that prescribed endpoint to any other old boundary vertex in a
smallest counterexample. This includes all internal prescribed vertices. -/
theorem no_interior_two_path_from_forward_prescribed_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  sorry

/-- With the good second backward boundary list, a prescribed endpoint has
no neighbour outside the prescription adjacent to another prescribed vertex.
Both interior positions three/four are resolved by actual strict cuts. -/
lemma prescribed_endpoint_no_shared_prescribed_neighbour (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ x, x ∉ r.support → G.Adj a x → ∀ y ∈ r.support, y ≠ a → ¬ G.Adj x y := by
  sorry

/-- The good-second-boundary-list endpoint-deletion branch is complete for
all original prescribed paths of at most six vertices. Neither endpoint conflict
is assumed: both exclusions follow from the actual boundary and strict cuts. -/
theorem colourable_of_good_second_boundary_list_all_prescriptions (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsecond : 3 ≤ (I.lists (p.getVert (p.length - 2))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- In every smallest counterexample with this orientation of the prescribed
path, the second backward boundary vertex has at most two available colours. -/
lemma prescribed_second_boundary_list_le_two (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length - 2))).card ≤ 2 := by
  sorry

end Thomassen.BoundaryInstance

end PrescribedInteriorTwoPathContracts
