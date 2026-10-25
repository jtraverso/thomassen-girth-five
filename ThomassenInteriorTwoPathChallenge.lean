/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryChordReduction

/-! Independent contracts for native spliced-face geometry, optional short
neighbours and the prescription-free interior two-path reduction.
None of the five proof modules implementing these contracts is imported.
The unconditional main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section FacialPathSpliceContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Follow the original face for `n` edges, then return along the supplied
path. The original walk and closing path retain their actual vertex types. -/
def spliceFacePath (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a) : G.Walk a a :=
  (p.take n).append q

lemma spliceFacePath_length (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) : (spliceFacePath p n q).length = n + q.length := by
  sorry

lemma spliceFacePath_getVert_prefix (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) {i : ℕ} (hi : i ≤ n) :
    (spliceFacePath p n q).getVert i = p.getVert i := by
  sorry

/-- Internal disjointness from the original face makes the spliced walk an
actual simple cycle. The original arc is nontrivial and is strictly shorter
than the original facial cycle. -/
lemma spliceFacePath_isCycle (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    (spliceFacePath p n q).IsCycle := by
  sorry

/-- The native returning suffix has precisely the original separator path's
vertices. This avoids identifying walks whose endpoint proof terms differ. -/
lemma spliceFacePath_drop_support (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) :
    ∀ x, x ∈ ((spliceFacePath p n q).drop n).support ↔ x ∈ q.support := by
  sorry

/-- On the original arc the new indexed cycle still has the original native
vertices, without a cyclic index cast changing the vertex. -/
lemma spliceFacePath_cycleVertex_prefix (p : G.Walk a a) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hn : n ≤ p.length) {i : ℕ} (hi : i ≤ n) :
    walkCycleVertices (spliceFacePath p n q) (i : ZMod (spliceFacePath p n q).length) = p.getVert i := by
  sorry

/-- The arc that is removed by the separator is exactly the original face
arc; the closing path changes none of its vertices. -/
lemma spliceFacePath_arc (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : 2 ≤ n) (hnp : n ≤ p.length) :
    cycleInterval (walkCycleVertices (spliceFacePath p n q)) 1 (n - 2) =
      cycleInterval (walkCycleVertices p) 1 (n - 2) := by
  sorry

/-- A vertex of the complementary old face arc remains outside the spliced
cycle. Both cut pieces will consequently have strictly fewer vertices. -/
lemma spliceFacePath_misses_next_vertex (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    p.getVert (n + 1) ∉ (spliceFacePath p n q).support := by
  sorry

/-- All old corners inside the retained face prefix are unchanged by the
closing path. The new and old actual darts, not only the vertices, coincide. -/
theorem spliceFacePath_isFacialAlong (M : PlaneMap G) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hqpos : 0 < q.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    IsFacialCycleAlong M (walk_isCycleMap (spliceFacePath p n q) (spliceFacePath_isCycle p hp n q hq hn hnp hmeet))
      (cycleInterval (walkCycleVertices (spliceFacePath p n q)) 1 (n - 2)) := by
  sorry

/-- The spliced cycle begins at precisely the same old dart as the original
face cycle. Its relation to the selected face is therefore inherited exactly. -/
lemma spliceFacePath_root (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    walkArcRoot (spliceFacePath p n q) (spliceFacePath_isCycle p hp n q hq hn hnp hmeet) = walkArcRoot p hp := by
  sorry

end Thomassen

end FacialPathSpliceContracts

section InteriorFacePathCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Every vertex of the actual full face cycle lies on its original selected
face. This transports the face-permutation orbit, not just the vertex range. -/
lemma native_facial_cycle_vertices_on_outer (M : PlaneMap G) (outer : G.Dart)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) :
    ∀ x ∈ p.support, OnOuterFace M outer x := by
  sorry

/-- An interior closing path meets the original facial cycle only at its
specified two endpoints. No disjointness witness is supplied separately. -/
lemma closing_path_intersection_of_interior (M : PlaneMap G) (outer : G.Dart)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n := by
  sorry

variable [Fintype V]

/-- An original facial prefix closed by a one/two/three-edge interior path
has an actual strict induced cut. All spliced corners, face roots, nonempty
complement witnesses and path-support identifications are proved internally. -/
theorem interior_face_path_cut (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ q.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x, x ∈ (p.take n).support ∨ x ∈ q.support → x ∈ S) ∧
      (∀ x, OnOuterFace M outer x → x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ (p.take n).support ∨ x.1 ∈ q.support) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) := by
  sorry

end Thomassen

end InteriorFacePathCutContracts

section OptionalShortEndsContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- One additional short neighbour suffices for a separator of at most two
edges. No short-list hypothesis is needed at the other endpoint. -/
theorem colourable_of_two_path_one_short_end (I : BoundaryInstance G C)
    (S T : Set V) {a b x : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqlen : q.length ≤ 2) (hxa : G.Adj x a) (hxq : x ∉ q.support)
    (hxS : x ∈ S) (hxs : (I.lists x).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTc : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x → OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z → 3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → (I.lists z).card ≤ 2 → ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every combination of zero, one or two endpoint short neighbours is
handled. Neighbours whose original list is longer are left unprescribed. -/
theorem colourable_of_two_path_optional_short_ends (I : BoundaryInstance G C)
    (S T : Set V) {a b x y : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqlen : q.length ≤ 2)
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxq : x ∉ q.support) (hyq : y ∉ q.support)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTc : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x ∨ z.1 = y → OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z → 3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end OptionalShortEndsContracts

section InteriorTwoPathSelectionContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Before the final face vertex, adjacency in a chordless native facial
cycle forces consecutive natural indices, with no cyclic wrap ambiguity. -/
lemma chordless_cycle_prefix_adjacent_indices (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (i j : ℕ) (hi : i + 1 < p.length) (hj : j + 1 < p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) : j = i + 1 ∨ i = j + 1 := by
  sorry

/-- Select the first other neighbour of the interior vertex on the specified
facial arc. Girth forces distance at least three, and minimality eliminates
every incidence to an internal vertex of the selected arc. -/
lemma first_interior_two_path_neighbour (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace M outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n)) :
    ∃ j : ℕ, 3 ≤ j ∧ j ≤ n ∧ G.Adj z (p.getVert j) ∧
      ∀ t, 0 < t → t < j → ¬ G.Adj z (p.getVert t) := by
  sorry

end Thomassen

end InteriorTwoPathSelectionContracts

section InteriorTwoPathReductionContracts
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A two-edge interior path cutting off an old facial arc free of the
prescription is a complete induction case. The first interior incidence selects
the cut, and chordlessness captures every remaining short neighbour. Neither
minimality, spliced corner equations nor a capture hypothesis is supplied. -/
theorem colourable_of_interior_two_path_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n))
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Any remaining interior two-edge path must cut through the prescription
on the chosen facial arc. The entire prescription-free case is closed. -/
lemma interior_two_path_arc_meets_prescription_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n)) :
    ∃ x ∈ I.precolor.vertices, x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
  sorry

end Thomassen.BoundaryInstance

end InteriorTwoPathReductionContracts
