/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RegionSeparation
public import Thomassen.CutPrecolor

/-! Contracts over the previously checked geometry and instance infrastructure.
None of CycleSeparation, CycleWalk or ShortCycleReduction is imported here.
The final reduction explicitly assumes only strict smaller-instance induction.
-/

@[expose] public section
section CycleSeparationContracts
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- The spanning graph consisting exactly of the specified cyclic edges. -/
def cyclicSubgraph (G : SimpleGraph V) (c : ZMod k → V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ i, (x = c i ∧ y = c (i + 1)) ∨
    (x = c (i + 1) ∧ y = c i)
  symm := ⟨fun _ _ ⟨h, i, hi⟩ => ⟨h.symm, i, hi.elim (Or.inr ∘ And.symm)
    (Or.inl ∘ And.symm)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma cyclicSubgraph_le : cyclicSubgraph G c ≤ G := by
  sorry

def cycleForward (hc : IsCycleMap G c) (i : ZMod k) : (cyclicSubgraph G c).Dart :=
  ⟨(c i, c (i + 1)), hc.adj i, i, Or.inl ⟨rfl, rfl⟩⟩

def cycleBackward (hc : IsCycleMap G c) (i : ZMod k) : (cyclicSubgraph G c).Dart :=
  ⟨(c i, c (i - 1)), by simpa using (hc.adj (i - 1)).symm,
    i - 1, Or.inr ⟨by simp, rfl⟩⟩

lemma cyclicSubgraph_subVerts (hc : IsCycleMap G c) :
    subVerts (cyclicSubgraph G c) = Set.range c := by
  sorry

lemma cyclicSubgraph_of_chordless (hch : IsChordless G c) {x y : V}
    (hx : x ∈ Set.range c) (hy : y ∈ Set.range c) (hxy : G.Adj x y) :
    (cyclicSubgraph G c).Adj x y := by
  sorry

lemma cycleForward_symm (hc : IsCycleMap G c) (i : ZMod k) :
    (cycleForward hc i).symm = cycleBackward hc (i + 1) := by
  sorry

lemma cycleBackward_symm (hc : IsCycleMap G c) (i : ZMod k) :
    (cycleBackward hc i).symm = cycleForward hc (i - 1) := by
  sorry

lemma cyclic_dart_cases (hc : IsCycleMap G c) (d : (cyclicSubgraph G c).Dart) :
    (∃ i, d = cycleForward hc i) ∨ (∃ i, d = cycleBackward hc i) := by
  sorry

lemma cycleForward_ne_backward (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    cycleForward hc i ≠ cycleBackward hc i := by
  sorry

/-- At every cycle vertex the restricted rotation exchanges its two darts. -/
lemma cycle_rot_forward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.rot (cycleForward hc i) = cycleBackward hc i := by
  sorry

lemma cycle_rot_backward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.rot (cycleBackward hc i) = cycleForward hc i := by
  sorry

lemma cycle_face_forward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.facePerm (cycleForward hc i) = cycleForward hc (i + 1) := by
  sorry

lemma cycle_face_backward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.facePerm (cycleBackward hc i) = cycleBackward hc (i - 1) := by
  sorry

variable [NeZero k]

lemma cyclicSubgraph_reachable (hc : IsCycleMap G c) (i j : ZMod k) :
    (cyclicSubgraph G c).Reachable (c i) (c j) := by
  sorry

lemma cyclicSubgraph_connected (hc : IsCycleMap G c) :
    ∀ a ∈ subVerts (cyclicSubgraph G c), ∀ b ∈ subVerts (cyclicSubgraph G c),
      (cyclicSubgraph G c).Reachable a b := by
  sorry

lemma cycle_forward_sameCycle (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    SameCycle M.facePerm (cycleForward hc 0) (cycleForward hc i) := by
  sorry

lemma cycle_backward_sameCycle (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    SameCycle M.facePerm (cycleBackward hc 0) (cycleBackward hc i) := by
  sorry

lemma cycle_faces_distinct [Fintype V] (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    ¬ SameCycle M.facePerm (cycleForward hc 0) (cycleBackward hc 0) := by
  sorry

lemma cycle_two_faces (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (d : (cyclicSubgraph G c).Dart) :
    SameCycle M.facePerm (cycleForward hc 0) d ∨
      SameCycle M.facePerm (cycleBackward hc 0) d := by
  sorry

lemma cycle_outer_forward_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (x : V) :
    OnOuterFace M (cycleForward hc 0) x ↔ x ∈ Set.range c := by
  sorry

lemma cycle_outer_backward_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (x : V) :
    OnOuterFace M (cycleBackward hc 0) x ↔ x ∈ Set.range c := by
  sorry

lemma cycle_outer_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (o : (cyclicSubgraph G c).Dart) (x : V) :
    OnOuterFace M o x ↔ x ∈ Set.range c := by
  sorry

variable [Fintype V]

lemma cycle_subface_forward (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceVertices M cyclicSubgraph_le (cycleForward hc 0) = Set.range c := by
  sorry

lemma cycle_subface_backward (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceVertices M cyclicSubgraph_le (cycleBackward hc 0) = Set.range c := by
  sorry

omit [NeZero k] [Fintype V] in
lemma rIn_univ_of_reachable {x y : V} (h : G.Reachable x y) : RIn G Set.univ x y := by
  sorry

/-- The two actual cycle faces account for all components outside the cycle. -/
lemma cycle_sides_cover (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) :
    subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∪
      subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) = Set.univ := by
  sorry

lemma cycle_sides_inter (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∩
      subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) = Set.range c := by
  sorry

lemma cycle_sides_no_crossing (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) {x y : V} (hxy : G.Adj x y) :
    (x ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∧
      y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0)) ∨
    (x ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) ∧
      y ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0)) := by
  sorry

omit [NeZero k] in
/-- A face walk connects its boundary vertices within that boundary. -/
lemma onOuterFace_connSet (M : PlaneMap G) (o : G.Dart) :
    ConnSet G {x | OnOuterFace M o x} := by
  sorry

omit [NeZero k] in
/-- A closed face side is connected: its attached components meet its connected
face boundary. No assertion about extension of colours is used. -/
lemma subfaceSide_connSet (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    (o : H.Dart) : ConnSet G (subfaceSide M hH o) := by
  sorry

lemma cycle_subface_vertices (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    subfaceVertices M cyclicSubgraph_le o = Set.range c := by
  sorry

lemma cyclicSubgraph_le_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    cyclicSubgraph G c ≤ restrict G (subfaceSide M cyclicSubgraph_le o) := by
  sorry

/-- An edge kept in one side cannot enter a gap belonging to the other side.
Chordlessness accounts for edges with both ends on the cycle. -/
lemma cycle_opposite_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c)
    (hch : IsChordless G c) (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right)
    (d : (restrict G (subfaceSide M cyclicSubgraph_le left)).Dart)
    (e : (cyclicSubgraph G c).Dart)
    (hn : IsNextH M cyclicSubgraph_le
      (toDart (restrict_le G (subfaceSide M cyclicSubgraph_le left)) d) e)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm right e) :
    (cyclicSubgraph G c).Adj d.fst d.snd := by
  sorry

omit [NeZero k] in
/-- Every dart of a preserved face in the larger map comes from the smaller
face. This is the converse orbit transport needed for an exact boundary. -/
lemma exists_dart_of_preserved_subface (M : PlaneMap G) {H N : SimpleGraph V}
    (hN : N ≤ G) (hHN : H ≤ N) (o : H.Dart)
    (hface : ∀ e, SameCycle (restrictMap M (hHN.trans hN)).facePerm o e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M (hHN.trans hN)).facePerm e))
    {d : N.Dart}
    (hd : SameCycle (restrictMap M hN).facePerm (toDart hHN o) d) :
    ∃ e : H.Dart, SameCycle (restrictMap M (hHN.trans hN)).facePerm o e ∧
      toDart hHN e = d := by
  sorry

/-- Each induced side of a chordless cycle has exactly that cycle as the
boundary of its selected face, in the actual induced rotation system. -/
lemma cycle_side_outer_iff (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hch : IsChordless G c) (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right)
    (x : subfaceSide M cyclicSubgraph_le left) :
    OnOuterFace (inducedPlaneMap M (subfaceSide M cyclicSubgraph_le left))
      (induceDartEquiv G (subfaceSide M cyclicSubgraph_le left)
        (toDart (cyclicSubgraph_le_side M hc hk left) right)) x ↔
      x.1 ∈ Set.range c := by
  sorry

omit [NeZero k] in
lemma mem_subfaceSide_congr (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    {left right : H.Dart} (h : SameCycle (restrictMap M hH).facePerm left right) (x : V) :
    x ∈ subfaceSide M hH left ↔ x ∈ subfaceSide M hH right := by
  sorry

/-- If an old face meets the cycle, all its vertices project to the same cycle
side. Excursions off the cycle are followed until their last cycle incidence. -/
lemma cycle_original_face_subset_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (outer : G.Dart) {d : G.Dart} {e : (cyclicSubgraph G c).Dart}
    (hdface : SameCycle M.facePerm outer d) (hnext : IsNextH M cyclicSubgraph_le d e) :
    ∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le e := by
  sorry

/-- An original face lies on one of the two closed cycle sides. -/
lemma cycle_original_face_one_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) (outer : G.Dart) :
    (∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0)) ∨
    (∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0)) := by
  sorry

/-- A concrete Jordan separation for a chordless cycle. Both pieces are actual
connected induced graphs, their common vertices are precisely the cycle, every
edge lies in a piece, and their selected face boundaries are exactly the cycle. -/
theorem chordless_cycle_separation (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hch : IsChordless G c) (hconn : G.Preconnected) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ∩ T = Set.range c ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ Set.range c) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ Set.range c) := by
  sorry

end Thomassen

end CycleSeparationContracts


section CycleWalkContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

def walkCycleVertices (p : G.Walk a a) : ZMod p.length → V := fun i => p.getVert i.val

lemma walkCycleVertices_next (p : G.Walk a a) (hp : 1 < p.length) (i : ZMod p.length) :
    walkCycleVertices p (i + 1) = p.getVert (i.val + 1) := by
  sorry

lemma walk_isCycleMap (p : G.Walk a a) (hp : p.IsCycle) :
    IsCycleMap G (walkCycleVertices p) := by
  sorry

lemma walkCycleVertices_range (p : G.Walk a a) (hp : p.IsCycle) :
    Set.range (walkCycleVertices p) = {x | x ∈ p.support} := by
  sorry

lemma walkCycleVertices_edges (p : G.Walk a a) (hp : p.IsCycle) (x y : V) :
    (cyclicSubgraph G (walkCycleVertices p)).Adj x y ↔ s(x, y) ∈ p.edges := by
  sorry

lemma cycle_support_card_eq_length (p : G.Walk a a) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  sorry

variable {k : ℕ} {c : ZMod k → V}

lemma zmod_two_ne_zero_of_three_le (hk : 3 ≤ k) : (2 : ZMod k) ≠ 0 := by
  sorry

lemma cycle_no_chord_two (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c) (i : ZMod k) :
    ¬ G.Adj (c i) (c (i + 2)) := by
  sorry

lemma cycle_no_chord_three (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (i : ZMod k) : ¬ G.Adj (c i) (c (i + 3)) := by
  sorry

/-- Every cycle of length at most six in girth at least five is chordless. -/
lemma short_cycle_isChordless [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hsmall : k ≤ 6) : IsChordless G c := by
  sorry

/-- The concrete two-side separation needed for a native prescribed cycle of
at most six vertices. Girth supplies chordlessness, so no geometric separation
or chordlessness assumption is left to the caller. -/
theorem short_native_cycle_separation [Fintype V] (M : PlaneMap G)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hsmall : p.support.toFinset.card ≤ 6) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ p.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ p.support) := by
  sorry

variable [Fintype V]

/-- Both open face regions of the native cycle contain a vertex. -/
def NativeCycleSeparates (M : PlaneMap G) (p : G.Walk a a) (hp : p.IsCycle) : Prop :=
  (∃ x, inSubface M cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) 0) x) ∧
    (∃ x, inSubface M cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) 0) x)

/-- An oriented proper cut: the first side contains the original face, both
induced vertex types are strictly smaller, and the common selected boundary is
the native cycle. Separation is supplied by two actual nonempty face regions. -/
theorem short_native_cycle_proper_cut (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hsmall : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates M p hp) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      (∀ x, OnOuterFace M outer x → x ∈ S) ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ p.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ p.support) := by
  sorry

end Thomassen

end CycleWalkContracts


section ShortCycleReductionContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- A separating cycle of at most six vertices cannot occur in a smallest
counterexample to boundary extension. All geometric cuts and changed list
conditions are proved; induction is used only on strictly smaller graphs. -/
theorem colourable_of_separating_short_cycle (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hbound : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates I.embedding p hp)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end Thomassen.BoundaryInstance

end ShortCycleReductionContracts
