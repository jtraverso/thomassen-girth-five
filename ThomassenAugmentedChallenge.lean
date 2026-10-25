/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortPathColouring
public import Thomassen.FaceBoundary
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Independent contracts for augmented prescriptions and actual facial cycles.
None of the four new proof modules is imported. Capture, deletion connectivity
and strict cardinality-decrease conditions remain explicit in these contracts.
The unconditional boundary-extension theorem is not asserted. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section AugmentedPathColouringContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}
lemma four_edge_path_isChordless (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 4) (hends : ¬ G.Adj a b) : q.IsChordless := by
  sorry

lemma endpoint_neighbour_unique_of_chordless_cons {a b x : V}
    (q : G.Walk a b) (hx : x ∉ q.support) (hxa : G.Adj x a)
    (hch : (Walk.cons hxa q).IsChordless) :
    ∀ z ∈ q.support, G.Adj x z → z = a := by
  sorry

lemma short_path_endpoint_neighbour_unique (hg : 5 ≤ G.egirth) {a b x : V}
    (q : G.Walk a b) (hp : q.IsPath) (hlen : q.length ≤ 2)
    (hx : x ∉ q.support) (hxa : G.Adj x a) :
    ∀ z ∈ q.support, G.Adj x z → z = a := by
  sorry


namespace BoundaryInstance
variable {C : Type v} [Fintype V]
omit [Fintype V] in
lemma extend_colouring_over_short_set (I : BoundaryInstance G C) (T A : Set V)
    (hdisjoint : Disjoint T A) (hnotP : ∀ x ∈ A, x ∉ I.precolor.vertices)
    (hshort : ∀ x ∈ A, (I.lists x).card ≤ 2)
    (c : (G.induce T).Coloring C)
    (hone : ∀ x ∈ A, ∃ y : T, ∀ z : T, G.Adj x z.1 → z = y) :
    ∃ f : V → C, (∀ x : T, f x.1 = c x) ∧
      (∀ x ∈ A, f x ∈ I.lists x) ∧
      (∀ x ∈ A ∪ T, ∀ y ∈ A ∪ T, G.Adj x y → f x ≠ f y) := by
  sorry

theorem colourable_of_augmented_short_path_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) {c d : V} (r : G.Walk c d) (hr : r.IsPath)
    (hrshort : r.length ≤ 5) (hrchordless : r.IsChordless)
    (hqr : ∀ x ∈ q.support, x ∈ r.support) (hrS : ∀ x ∈ r.support, x ∈ S)
    (hExtra : ∀ x ∈ r.support, x ∉ q.support → (I.lists x).card ≤ 2)
    (hAttach : ∀ x ∈ r.support, x ∉ q.support →
      ∃ y ∈ q.support, ∀ z ∈ q.support, G.Adj x z → z = y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ r.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hInterior : ∀ x : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS x → 3 ≤ (I.lists x.1).card)
    (hCapture : ∀ x ∈ S, x ∉ r.support → (I.lists x).card ≤ 2 →
      ∀ y ∈ q.support, ¬ G.Adj x y)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_short_path_with_two_short_ends (I : BoundaryInstance G C)
    (S T : Set V) {a b x y : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 2)
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxq : x ∉ q.support) (hyq : y ∉ q.support)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hxshort : (I.lists x).card ≤ 2) (hyshort : (I.lists y).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x ∨ z.1 = y →
      OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z →
      3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_short_path_with_one_short_end (I : BoundaryInstance G C)
    (S T : Set V) {a b x : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hxa : G.Adj x a) (hxq : x ∉ q.support) (hxS : x ∈ S)
    (hxshort : (I.lists x).card ≤ 2) (hbshort : (I.lists b).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x →
      OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z →
      3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
end AugmentedPathColouringContracts

section NativeAugmentedPathCutsContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

namespace BoundaryInstance
variable {C : Type v} [Fintype V]
theorem colourable_of_native_short_path_with_one_short_end (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) {x : V} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxArc : x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxa : G.Adj x (p.getVert n)) (hxq : x ∉ (p.drop n).support)
    (hxshort : (I.lists x).card ≤ 2)
    (hashort : (I.lists a).card ≤ 2)
    (hCaptureArc : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2),
      z ≠ x → (I.lists z).card ≤ 2 →
      ∀ w ∈ (p.drop n).support, ¬ G.Adj z w)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_native_short_path_with_two_short_ends (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) {x y : V} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm2 : m ≤ 2) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxArc : x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hxa : G.Adj x (p.getVert n)) (hxq : x ∉ (p.drop n).support)
    (hxshort : (I.lists x).card ≤ 2)
    (hyArc : y ∈ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hby : G.Adj a y) (hyq : y ∉ (p.drop n).support) (hyshort : (I.lists y).card ≤ 2)
    (hCaptureArc : ∀ z ∈ cycleInterval (walkCycleVertices p) 1 (n - 2),
      z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ (p.drop n).support, ¬ G.Adj z w)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
end NativeAugmentedPathCutsContracts

section CycleMapWalkContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}
lemma exists_walk_of_cycleMap {k : ℕ} (hk : 3 ≤ k) {c : ZMod k → V}
    (hc : IsCycleMap G c) :
    ∃ p : G.Walk (c 0) (c 0), p.IsCycle ∧ p.length = k ∧
      ∀ i ≤ k, p.getVert i = c (i : ZMod k) := by
  sorry

end Thomassen
end CycleMapWalkContracts

section FaceOrbitCycleContracts
namespace Thomassen
open Classical
variable {V : Type u} [instFinite : Finite V] {G : SimpleGraph V}
noncomputable def faceOrbitLength (M : PlaneMap G) (o : G.Dart) : ℕ :=
  Function.minimalPeriod M.facePerm o

noncomputable def faceOrbitDart (M : PlaneMap G) (o : G.Dart) :
    ZMod (faceOrbitLength M o) → G.Dart := fun i => M.facePerm^[i.val] o

noncomputable def faceOrbitVertex (M : PlaneMap G) (o : G.Dart) :
    ZMod (faceOrbitLength M o) → V := fun i => (faceOrbitDart M o i).fst

include instFinite

lemma faceOrbitLength_pos (M : PlaneMap G) (o : G.Dart) : 0 < faceOrbitLength M o := by
  sorry

lemma faceOrbitLength_three_le (M : PlaneMap G)
    (hdeg : ∀ x, 2 ≤ Nat.card {y // G.Adj x y}) (o : G.Dart) :
    3 ≤ faceOrbitLength M o := by
  sorry

omit [Finite V] in
lemma faceOrbitDart_sameCycle (M : PlaneMap G) (o : G.Dart) (i : ZMod (faceOrbitLength M o)) :
    SameCycle M.facePerm o (faceOrbitDart M o i) := by
  sorry

lemma faceOrbitDart_injective (M : PlaneMap G) (o : G.Dart) :
    Function.Injective (faceOrbitDart M o) := by
  sorry

omit [Finite V] in
lemma faceOrbitDart_next (M : PlaneMap G) (o : G.Dart) (hk : 1 < faceOrbitLength M o)
    (i : ZMod (faceOrbitLength M o)) :
    faceOrbitDart M o (i + 1) = M.facePerm (faceOrbitDart M o i) := by
  sorry

lemma faceOrbitVertex_injective (M : PlaneMap G) (o : G.Dart)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    Function.Injective (faceOrbitVertex M o) := by
  sorry

lemma faceOrbitVertex_isCycleMap (M : PlaneMap G) (o : G.Dart)
    (hk : 1 < faceOrbitLength M o)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsCycleMap G (faceOrbitVertex M o) := by
  sorry

lemma faceOrbitVertex_range (M : PlaneMap G) (o : G.Dart) :
    Set.range (faceOrbitVertex M o) = {x | OnOuterFace M o x} := by
  sorry

lemma faceOrbitVertex_isFacial (M : PlaneMap G) (o : G.Dart)
    (hk : 1 < faceOrbitLength M o)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsFacialCycleAlong M (faceOrbitVertex_isCycleMap M o hk hconn) Set.univ := by
  sorry

theorem exists_native_face_cycle (M : PlaneMap G) (o : G.Dart)
    (hdeg : ∀ x, 2 ≤ Nat.card {y // G.Adj x y})
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength M o ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace M o x) ∧
      IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = o := by
  sorry

lemma two_le_card_neighbours_of_delete_preconnected (hG : G.Preconnected)
    (hcard : 3 ≤ Nat.card V)
    (hdelete : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∀ x, 2 ≤ Nat.card {y // G.Adj x y} := by
  sorry

theorem exists_native_face_cycle_of_delete_preconnected (M : PlaneMap G) (o : G.Dart)
    (hG : G.Preconnected) (hcard : 3 ≤ Nat.card V)
    (hdelete : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength M o ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace M o x) ∧
      IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = o := by
  sorry

end Thomassen
end FaceOrbitCycleContracts
