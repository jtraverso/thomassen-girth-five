/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FaceRestriction
public import Thomassen.ChordSeparation
public import Thomassen.ConnectedInstance
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

/-! Independent contracts over previously verified face, chord and instance
prerequisites. None of FaceMerge, ArcPathSeparation, CycleIntervals,
NativeArcPathCut or ShortPathColouring is imported. Actual face-corner equations
remain explicit. The colouring cases require either three-lists on the trimmed arc or
short arc lists avoiding the separator with the prescription outside the arc.
Neither that condition in every cut nor the unconditional main theorem is asserted. -/

@[expose] public section
section FaceMergeContracts
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

/-- Two face incidences entering the same deleted component project to the
same face of a connected retained subgraph. -/
lemma onOuterFace_restrict_of_deleted_connection (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer : G.Dart) {d t : G.Dart} {e : H.Dart}
    (htface : SameCycle M.facePerm outer t)
    (hd : d.fst ∈ subVerts H) (ht : t.fst ∈ subVerts H)
    (hdout : d.snd ∉ subVerts H) (htout : t.snd ∉ subVerts H)
    (hpath : RIn G (subVerts H)ᶜ d.snd t.snd) (he : IsNextH M hH d e)
    {x : V} (hx : x ∈ subVerts H) (hface : OnOuterFace M outer x) :
    OnOuterFace (restrictMap M hH) e x := by
  sorry

/-- Deleting a connected set merges every incident old face into one new face.
The selected old face and all remaining neighbours of the deleted set are
retained too. Connectivity is required only for the actual remaining graph. -/
lemma exists_outer_induced_merging_deleted_faces (M : PlaneMap G) (outer : G.Dart)
    (A : Set V) [Nontrivial (Aᶜ : Set V)]
    (hremain : (G.induce Aᶜ).Preconnected) (hA : ConnSet G A)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∉ A) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce Aᶜ).Dart,
      (∀ x : (Aᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ x : (Aᶜ : Set V), (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∉ A → t.snd ∈ A →
        ∀ x : (Aᶜ : Set V), OnOuterFace M inner x.1 →
          OnOuterFace (inducedPlaneMap M Aᶜ) o x) := by
  sorry

/-- Retaining a connected induced set merges old faces incident with any one
connected omitted set. Other omitted components may remain as well. -/
lemma exists_outer_induced_merging_connected_set (M : PlaneMap G) (outer : G.Dart)
    (S A : Set V) [Nontrivial S] (hremain : (G.induce S).Preconnected)
    (hA : ConnSet G A) (hAS : ∀ x ∈ A, x ∉ S)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∈ S) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce S).Dart,
      (∀ x : S, OnOuterFace M outer x.1 → OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∀ x : S, (∃ y ∈ A, G.Adj x.1 y) → OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∈ S → t.snd ∈ A →
        ∀ x : S, OnOuterFace M inner x.1 → OnOuterFace (inducedPlaneMap M S) o x) := by
  sorry

end Thomassen

end FaceMergeContracts

section ArcPathSeparationContracts
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {k : ℕ} [NeZero k] {c : ZMod k → V}

/-- Actual old-face corners at all vertices of the arc to be trimmed. -/
def IsFacialCycleAlong (M : PlaneMap G) (hc : IsCycleMap G c) (A : Set V) : Prop :=
  ∀ i, c i ∈ A → M.facePerm (toDart cyclicSubgraph_le (cycleForward hc (i - 1))) =
    toDart cyclicSubgraph_le (cycleForward hc i)

lemma cycle_gap_empty_along (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (A : Set V) (hArc : IsFacialCycleAlong M hc A)
    {d : G.Dart} {e : (cyclicSubgraph G c).Dart} (hx : d.fst ∈ A)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm (cycleForward hc 0) e)
    (hn : IsNextH M cyclicSubgraph_le d e) : d = toDart cyclicSubgraph_le e := by
  sorry

lemma cycle_no_exterior_neighbour_along (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (A : Set V) (hAC : A ⊆ Set.range c) (hArc : IsFacialCycleAlong M hc A) {x y : V} (hx : x ∈ A)
    (hy : y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) \ Set.range c) :
    ¬ G.Adj x y := by
  sorry

/-- If no extra edge joins two separator vertices, every chord outside the
cycle subgraph has an endpoint on the old facial arc. -/
lemma arc_path_inside_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (A : Set V) (hArc : IsFacialCycleAlong M hc A)
    (hB : ∀ {x y}, x ∈ Set.range c \ A → y ∈ Set.range c \ A → G.Adj x y →
      (cyclicSubgraph G c).Adj x y)
    (d : (restrict G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))).Dart)
    (e : (cyclicSubgraph G c).Dart)
    (hn : IsNextH M cyclicSubgraph_le
      (toDart (restrict_le G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))) d) e)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm (cycleForward hc 0) e) :
    (cyclicSubgraph G c).Adj d.fst d.snd := by
  sorry

/-- The graph of one closed cycle side with only noncycle chords removed.
Those edges may be retained in the other induced piece of an arc cut. -/
def cycleSideSkeleton (M : PlaneMap G) (c : ZMod k → V)
    (o : (cyclicSubgraph G c).Dart) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ subfaceSide M cyclicSubgraph_le o ∧
    y ∈ subfaceSide M cyclicSubgraph_le o ∧
    (x ∉ Set.range c ∨ y ∉ Set.range c ∨ (cyclicSubgraph G c).Adj x y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    rcases h.2.2.2 with hx | hy | he
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hy
    · exact Or.inr (Or.inr he.symm)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

omit [NeZero k] in
lemma cycleSideSkeleton_le (M : PlaneMap G) (o : (cyclicSubgraph G c).Dart) :
    cycleSideSkeleton M c o ≤ G := by
  sorry

lemma cyclicSubgraph_le_skeleton (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) : cyclicSubgraph G c ≤ cycleSideSkeleton M c o := by
  sorry

/-- Removing just the extra chords does not disconnect a closed cycle side:
a missing edge is replaced by a walk along the retained cycle. -/
lemma cycleSideSkeleton_connSet (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    ConnSet (cycleSideSkeleton M c o) (subfaceSide M cyclicSubgraph_le o) := by
  sorry

/-- No skeleton edge can enter a gap of the opposite cycle face. In contrast
to an induced side, it contains no extra chord between cycle vertices. -/
lemma cycleSideSkeleton_opposite_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c)
    (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right)
    (d : (cycleSideSkeleton M c left).Dart) (e : (cyclicSubgraph G c).Dart)
    (hn : IsNextH M cyclicSubgraph_le (toDart (cycleSideSkeleton_le M left) d) e)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm right e) :
    (cyclicSubgraph G c).Adj d.fst d.snd := by
  sorry

/-- The opposite cycle face is an actual face in the skeleton map. -/
lemma cycleSideSkeleton_face_iff (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right) (x : V) :
    OnOuterFace (restrictMap M (cycleSideSkeleton_le M left))
      (toDart (cyclicSubgraph_le_skeleton M hc hk left) right) x ↔ x ∈ Set.range c := by
  sorry

/-- A facial arc can be cut off along a connected chordless separator path.
The two actual induced graphs meet exactly in the separator. The exterior map
is constructed by deleting the arc from the exterior skeleton, so its selected
face contains both the surviving old boundary and every separator vertex. -/
theorem facial_arc_path_separation (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (A : Set V) (hAC : A ⊆ Set.range c) (hArc : IsFacialCycleAlong M hc A)
    (hAconn : ConnSet (cyclicSubgraph G c) A)
    (hBconn : ConnSet (cyclicSubgraph G c) (Set.range c \ A))
    (hBedge : ∀ {x y}, x ∈ Set.range c \ A → y ∈ Set.range c \ A → G.Adj x y →
      (cyclicSubgraph G c).Adj x y)
    (h0 : c 0 ∉ A) (h1 : c 1 ∈ A) (hback : c (-1) ∉ A)
    (j : ZMod k) (hj : c j ∉ A) (hjprev : c (j - 1) ∈ A)
    (hconn : G.Preconnected)
    (houtside : ∃ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x ∧
      x ∉ Set.range c) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = Set.range c \ A ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ Set.range c, x ∈ S) ∧
      (∀ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x → x ∉ A → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ Set.range c) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 ∨ x.1 ∈ Set.range c \ A →
          OnOuterFace N o x) := by
  sorry

end Thomassen

end ArcPathSeparationContracts

section CycleIntervalsContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V}

/-- The vertices of a consecutive segment of the actual indexed cycle. -/
def cycleInterval (c : ZMod k → V) (start length : ℕ) : Set V :=
  {x | ∃ i : ℕ, i ≤ length ∧ c ((start + i : ℕ) : ZMod k) = x}

omit [NeZero k] in
lemma cycleInterval_zero (start : ℕ) : cycleInterval c start 0 = {c (start : ZMod k)} := by
  sorry

omit [NeZero k] in
lemma cycleInterval_succ (start length : ℕ) :
    cycleInterval c start (length + 1) =
      insert (c ((start + (length + 1) : ℕ) : ZMod k)) (cycleInterval c start length) := by
  sorry

omit [NeZero k] in
/-- These are connected sets in the cycle graph itself, not only in G. -/
lemma cycleInterval_connSet (hc : IsCycleMap G c) (start length : ℕ) :
    ConnSet (cyclicSubgraph G c) (cycleInterval c start length) := by
  sorry

omit [NeZero k] in
lemma cycleInterval_subset (start length : ℕ) : cycleInterval c start length ⊆ Set.range c := by
  sorry

/-- Splitting the cycle into an open old arc and a closed returning path gives
an exact partition. Only the genuine cycle indices are used. -/
lemma cycleInterval_partition (hc : IsCycleMap G c) {n m : ℕ} (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hk : k = n + m) :
    Set.range c \ cycleInterval c 1 (n - 2) = cycleInterval c n m := by
  sorry

omit [NeZero k] in
/-- Girth excludes all nonconsecutive edges in a returning path of at most
three edges. This discharges the separator chord condition geometrically. -/
lemma cycleInterval_short_complete (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (start length : ℕ) (hlen : length ≤ 3)
    {x y : V} (hx : x ∈ cycleInterval c start length) (hy : y ∈ cycleInterval c start length)
    (hxy : G.Adj x y) : (cyclicSubgraph G c).Adj x y := by
  sorry

variable [Fintype V]

/-- Concrete path cut with a separator of at most three edges. The arc and
separator are explicit consecutive cycle intervals. Girth supplies the absence
of extra separator chords; their connectivity and exact partition are proved. -/
theorem short_arc_path_separation (M : PlaneMap G) (hg : 5 ≤ G.egirth)
    (hc : IsCycleMap G c) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hk : k = n + m) (hArc : IsFacialCycleAlong M hc (cycleInterval c 1 (n - 2)))
    (hconn : G.Preconnected)
    (houtside : ∃ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x ∧
      x ∉ Set.range c) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = cycleInterval c n m ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ Set.range c, x ∈ S) ∧
      (∀ x, OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x →
        x ∉ cycleInterval c 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ Set.range c) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 ∨
          x.1 ∈ cycleInterval c n m → OnOuterFace N o x) := by
  sorry

end Thomassen


end CycleIntervalsContracts

section NativeArcPathCutContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

lemma walkCycleVertices_nat_le (p : G.Walk a a) {i : ℕ} (hi : i ≤ p.length) :
    walkCycleVertices p (i : ZMod p.length) = p.getVert i := by
  sorry

/-- The closed indexed interval is exactly the support of the native suffix. -/
lemma walk_drop_support_cycleInterval (p : G.Walk a a) (n m : ℕ) (hlen : p.length = n + m) :
    cycleInterval (walkCycleVertices p) n m = {x | x ∈ (p.drop n).support} := by
  sorry

variable [Fintype V]

/-- Cut a facial arc and its native closing path of one, two or three edges.
The separator is exactly the support of that path. Its vertices and the old
remaining boundary lie on one actual outer face of the exterior piece. -/
theorem native_short_arc_path_cut (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong M (walk_isCycleMap p hp) (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle M.facePerm outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace M outer x ∧ x ∉ p.support) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ (p.drop n).support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x ∈ p.support, x ∈ S) ∧
      (∀ x, OnOuterFace M outer x → x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ (p.drop n).support → OnOuterFace N o x) := by
  sorry

end Thomassen

end NativeArcPathCutContracts

section ShortPathColouringContracts
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Every simple path of at most three edges is induced in girth at least five. -/
lemma short_path_isChordless (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 3) : q.IsChordless := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Colour the prescription side first and prescribe its separator path on the
other side. Old short lists may remain if they have no neighbour on that path.
Every list condition is verified before invoking strict induction. -/
theorem colourable_of_short_path_without_short_neighbours (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hInterior : ∀ x : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS x → 3 ≤ (I.lists x.1).card)
    (hNoShort : ∀ x ∈ S, x ∉ q.support → (I.lists x).card ≤ 2 →
      ∀ y ∈ q.support, ¬ G.Adj x y)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The private three-list case follows from the general short-neighbour cut. -/
theorem colourable_of_three_list_short_path_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (hprivate : ∀ x ∈ S, x ∉ q.support → 3 ≤ (I.lists x).card)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The short-path induction case allowing old two-lists on the trimmed arc,
provided they avoid the separator and the old prescription lies outside the arc.
Its induced faces and all other instance conditions follow from the actual cut. -/
theorem colourable_of_short_path_with_independent_short_arc (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hNoShortArc : ∀ x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), (I.lists x).card ≤ 2 →
      ∀ y ∈ (p.drop n).support, ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- If the whole trimmed arc has three-lists, the short-neighbour condition
holds automatically. -/
theorem colourable_of_short_path_with_three_list_arc (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hArcThree : ∀ x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), 3 ≤ (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end ShortPathColouringContracts
