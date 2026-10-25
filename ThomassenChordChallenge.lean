/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Thomassen.ConnectedInstance

/-! Contracts over previously checked cycle geometry and instance infrastructure.
Neither ChordSeparation nor PrescribedChordReduction is imported here.
Face-arc equations, smaller-cardinality induction and the case restriction on
prescribed vertices are explicit in the contracts.
-/

@[expose] public section
section ChordSeparationContracts
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Removing a set preserves connectivity if its neighbours in the remainder
belong to one connected surviving boundary. The old paths are rerouted through
that boundary using the registered reachability transport lemma. -/
lemma connSet_sdiff_of_connected_boundary (T A B : Set V) (hT : ConnSet G T)
    (hB : ConnSet G B) (hBW : B ⊆ T \ A)
    (hboundary : ∀ x ∈ A, ∀ y ∈ T \ A, G.Adj x y → y ∈ B) :
    ConnSet G (T \ A) := by
  sorry

/-- Move a duplicated boundary arc to one piece. No edge is lost, and the new
intersection is the old intersection with precisely that arc removed. -/
lemma trim_separation (S T C A : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = C)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hAC : A ⊆ C) (hnoexit : ∀ x ∈ A, ∀ y ∈ T \ C, ¬ G.Adj x y) :
    S ∪ (T \ A) = Set.univ ∧ S ∩ (T \ A) = C \ A ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T \ A ∧ y ∈ T \ A)) := by
  sorry

variable [Fintype V]

/-- Only the predecessor step of a particular gap is needed to certify that
the gap is empty; the rest of the smaller face need not be preserved. -/
lemma eq_of_isNextH_of_preserved_predecessor (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    {d : G.Dart} {e : H.Dart}
    (hstep : M.facePerm (toDart hH ((restrictMap M hH).facePerm⁻¹ e)) = toDart hH e)
    (hd : IsNextH M hH d e) : d = toDart hH e := by
  sorry

variable {k : ℕ} [NeZero k] {c : ZMod k → V}

/-- The old boundary arc omits only the closing edge from `c (-1)` to `c 0`. -/
def cycleArcInterior (c : ZMod k → V) : Set V := Set.range c \ {c 0, c (-1)}

/-- At each internal vertex the cyclic arc follows the actual old face.
These are local face-permutation equations, not assumptions about a cut. -/
def IsFacialCycleArc (M : PlaneMap G) (hc : IsCycleMap G c) : Prop :=
  ∀ i, c i ≠ c 0 → c i ≠ c (-1) →
    M.facePerm (toDart cyclicSubgraph_le (cycleForward hc (i - 1))) =
      toDart cyclicSubgraph_le (cycleForward hc i)

/-- No extra dart can occupy the old face corner along the retained arc. -/
lemma cycle_arc_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) {d : G.Dart} {e : (cyclicSubgraph G c).Dart}
    (hx : d.fst ∈ cycleArcInterior c)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm (cycleForward hc 0) e)
    (hn : IsNextH M cyclicSubgraph_le d e) : d = toDart cyclicSubgraph_le e := by
  sorry

/-- An internal old-arc vertex has no neighbour strictly on the exterior side. -/
lemma cycle_arc_no_exterior_neighbour (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) {x y : V} (hx : x ∈ cycleArcInterior c)
    (hy : y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) \ Set.range c) :
    ¬ G.Adj x y := by
  sorry

omit [Fintype V] in
/-- All vertices of the cyclic arc, including both ends, are on its original
face. The last endpoint is reached by the last old arc edge, not by the chord. -/
lemma cycle_arc_vertices_on_outer (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) : ∀ x ∈ Set.range c,
    OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x := by
  sorry

/-- All additional chords have an endpoint in the old arc. They therefore
occupy its interior side, as do all components attached at those vertices. -/
lemma facial_arc_inside_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc)
    (d : (restrict G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))).Dart)
    (e : (cyclicSubgraph G c).Dart)
    (hn : IsNextH M cyclicSubgraph_le
      (toDart (restrict_le G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))) d) e)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm (cycleForward hc 0) e) :
    (cyclicSubgraph G c).Adj d.fst d.snd := by
  sorry

/-- Exact face transport once the actual cycle face steps are preserved in a
retained graph. The preservation proof is supplied geometrically below. -/
lemma cycle_face_after_restriction (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    {N : SimpleGraph V} (hN : N ≤ G) (hHN : cyclicSubgraph G c ≤ N)
    (o : (cyclicSubgraph G c).Dart)
    (hface : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm o e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e)) (x : V) :
    OnOuterFace (restrictMap M hN) (toDart hHN o) x ↔ x ∈ Set.range c := by
  sorry

/-- Cut along the closing chord of a cycle whose other edges form
an original face arc. Removing that arc from the exterior piece leaves exactly
the chord endpoints in the intersection, with no edge lost. Both pieces are
strictly smaller when the old face has a vertex outside the cycle. -/
theorem facial_arc_chord_separation (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) (hconn : G.Preconnected)
    (houtside : ∃ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x ∧
      x ∉ Set.range c) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {c 0, c (-1)} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ Set.range c, x ∈ S) ∧
      (∀ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x →
        x ∉ cycleArcInterior c → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ Set.range c) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 →
          OnOuterFace (inducedPlaneMap M T) o x) := by
  sorry

def walkArcRoot {a : V} (p : G.Walk a a) (hp : p.IsCycle) : G.Dart :=
  toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) 0)

/-- Every internal corner of the native arc follows the original face. -/
def IsFacialWalkArc (M : PlaneMap G) {a : V} (p : G.Walk a a) (hp : p.IsCycle) : Prop :=
  IsFacialCycleArc M (walk_isCycleMap p hp)

omit [NeZero k] in
/-- Native-walk version of the chord cut. The closing edge joins the starting
vertex to the penultimate vertex. The old arc is removed only from the exterior
piece, so their intersection consists of exactly those two vertices. -/
theorem facial_walk_chord_separation (M : PlaneMap G) (outer : G.Dart)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hArc : IsFacialWalkArc M p hp)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace M outer x ∧ x ∉ p.support) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {a, p.penultimate} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ p.support, x ∈ S) ∧
      (∀ x, OnOuterFace M outer x →
        x ∉ ({z | z ∈ p.support} \ {a, p.penultimate}) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 → OnOuterFace (inducedPlaneMap M T) o x) := by
  sorry

end Thomassen

end ChordSeparationContracts


section PrescribedChordReductionContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- Cut along an already prescribed edge, when all other prescribed vertices
are retained in the second piece. The first piece has exactly that native edge
as its prescribed path. No changed-list or extension hypothesis is assumed. -/
theorem colourable_of_prescribed_edge_separation (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (hab : G.Adj a b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∈ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Connected) (hTconn : (G.induce T).Connected)
    (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The complete facial-chord reduction when both ends are already prescribed
and no other prescribed vertex belongs to the arc being removed from the
exterior piece. The cut itself is obtained from the original face equations. -/
theorem colourable_of_prescribed_facial_chord (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hArc : IsFacialWalkArc I.embedding p hp)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (haP : a ∈ I.precolor.vertices) (hbP : p.penultimate ∈ I.precolor.vertices)
    (hPoutside : ∀ x ∈ I.precolor.vertices,
      x ∉ ({z | z ∈ p.support} \ {a, p.penultimate}))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end PrescribedChordReductionContracts
