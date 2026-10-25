module
public import Thomassen.OriginalInstance
public import Thomassen.FacialCycleRebase

/-! Independent contracts for strict original-invariant reductions.
The shared input invariant has no extension field. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
theorem OriginalBoundaryInstance.extends_of_glued_colourings (I : OriginalBoundaryInstance G C)
    (S T : Set V) (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x, cS x ∈ I.lists x.1) (hcT : ∀ x, cT x ∈ I.lists x.1)
    (hagree : ∀ (x : V) (hx : x ∈ S) (hy : x ∈ T), cS ⟨x,hx⟩ = cT ⟨x,hy⟩)
    (hca : cS ⟨I.a,haS⟩ = I.ta) (hcb : cS ⟨I.b,hbS⟩ = I.tb) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extend_vertex_on_induced_face_of_smaller (I : OriginalBoundaryInstance G C)
    (S : Set V) (outer : (G.induce S).Dart)
    (hAface : ∀ x : S, x.1 ∈ I.short → OnOuterFace (inducedPlaneMap I.embedding S) outer x)
    (w : S) (hw : OnOuterFace (inducedPlaneMap I.embedding S) outer w)
    (tw : C) (htw : tw ∈ I.lists w.1) (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧ c w = tw := by
  sorry

theorem OriginalBoundaryInstance.extends_of_cutvertex (I : OriginalBoundaryInstance G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_edge_separation (I : OriginalBoundaryInstance G C)
    (S T : Set V) (u w : V) (huw : G.Adj u w)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_edge_cut (I : OriginalBoundaryInstance G C)
    (S T : Set V) (u w : V) (huw : G.Adj u w)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_boundary_chord (I : OriginalBoundaryInstance G C)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ) (hG : G.Preconnected)
    (houter : ∀ i, OnOuterFace I.embedding I.outer (c i))
    (i j : ZMod k) (hadj : G.Adj (c i) (c j))
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem OriginalBoundaryInstance.extends_of_card_le_two (I : OriginalBoundaryInstance G C) (hcard : Nat.card V ≤ 2) :
    I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_disconnected (I : OriginalBoundaryInstance G C) (hdisc : ¬ G.Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.minimal_counterexample_has_chordless_native_face_cycle (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.IsChordless ∧
        p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  sorry

theorem OriginalBoundaryInstance.extends_of_separating_short_cycle (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hbound : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates I.embedding p hp)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem OriginalBoundaryInstance.extends_of_short_leaf_edge_cut (I : OriginalBoundaryInstance G C)
    (S T R : Set V) (v w : V) (hvw : G.Adj v w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = R ∪ {v,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (hR : R ⊆ I.short) (hRaway : ∀ x ∈ R, x ≠ v ∧ x ≠ w)
    (hattach : ∀ x ∈ R, ∃ y, (y = v ∨ y = w) ∧ G.Adj x y)
    (N : PlaneMap (G.induce T)) (outer : (G.induce T).Dart)
    (hAface : ∀ x : T, x.1 ∈ I.short → OnOuterFace N outer x)
    (hvface : ∀ hvT : v ∈ T, OnOuterFace N outer ⟨v,hvT⟩)
    (hwface : ∀ hwT : w ∈ T, OnOuterFace N outer ⟨w,hwT⟩)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem interior_path_cut_both_faces (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ q.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ N : PlaneMap (G.induce S), ∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) := by
  sorry

theorem OriginalBoundaryInstance.extends_of_short_leaf_edge_separation (I : OriginalBoundaryInstance G C)
    (S T R : Set V) (v w : V) (hvw : G.Adj v w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = R ∪ {v,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hR : R ⊆ I.short) (hRaway : ∀ x ∈ R, x ≠ v ∧ x ≠ w)
    (hattach : ∀ x ∈ R, ∃ y, (y = v ∨ y = w) ∧ G.Adj x y)
    (NS : PlaneMap (G.induce S)) (oS : (G.induce S).Dart)
    (hSface : ∀ x : S, OnOuterFace I.embedding I.outer x.1 ∨ x.1 ∈ R ∪ {v,w} → OnOuterFace NS oS x)
    (NT : PlaneMap (G.induce T)) (oT : (G.induce T).Dart)
    (hTface : ∀ x : T, OnOuterFace I.embedding I.outer x.1 ∨ x.1 ∈ R ∪ {v,w} → OnOuterFace NT oT x)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_interior_two_path (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haA : a ∈ I.short) (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (z : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_interior_three_path (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haA : a ∈ I.short) (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (hnA : p.getVert n ∈ I.short) (z w : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hw : ¬ OnOuterFace I.embedding I.outer w)
    (hnz : G.Adj (p.getVert n) z) (hzw : G.Adj z w) (hwa : G.Adj w a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem OriginalBoundaryInstance.extends_of_few_neighbours (I : OriginalBoundaryInstance G C)
    (x : V) (hxa : x ≠ I.a) (hxb : x ≠ I.b)
    (hconn : (G.induce ({x} : Set V)ᶜ).Preconnected)
    (hdegree : (Finset.univ.filter (G.Adj x)).card < (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.list_card_le_degree_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (x : V) (hxa : x ≠ I.a) (hxb : x ≠ I.b) :
    (I.lists x).card ≤ (Finset.univ.filter (G.Adj x)).card := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
theorem cycle_index_bounds_of_nonadjacent {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n : ℕ) (hn : n < p.length) (hna : p.getVert n ≠ a)
    (hno : ¬ G.Adj a (p.getVert n)) : 2 ≤ n ∧ n+2 ≤ p.length := by
  sorry

theorem OriginalBoundaryInstance.exists_native_face_cycle_at (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u : V) (hu : OnOuterFace I.embedding I.outer u) :
    ∃ p : G.Walk u u, ∃ hp : p.IsCycle,
      5 ≤ p.length ∧ IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧
      SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp) ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) := by
  sorry

theorem OriginalBoundaryInstance.no_interior_two_path_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u v z : V) (hu : u ∈ I.short) (hv : OnOuterFace I.embedding I.outer v)
    (huv : u ≠ v) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hzu : G.Adj z u) (hzv : G.Adj z v) : False := by
  sorry

theorem OriginalBoundaryInstance.no_interior_three_path_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (u v z w : V) (hu : u ∈ I.short) (hv : v ∈ I.short) (huv : u ≠ v)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hw : ¬ OnOuterFace I.embedding I.outer w)
    (huz : G.Adj u z) (hzw : G.Adj z w) (hwv : G.Adj w v) : False := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem OriginalBoundaryInstance.neighbours_on_short_facial_arc_stay_on_cycle (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6) (A : Set V) (hAC : A ⊆ {x | x ∈ p.support})
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) A)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ p.support := by
  sorry

theorem OriginalBoundaryInstance.short_facial_arc_backward_region_empty (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    ∀ w, ¬ inSubface I.embedding cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) 0) w := by
  sorry

theorem OriginalBoundaryInstance.neighbours_on_short_closed_face_prefix (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (i : ℕ) (hi : 0 < i) (hin : i < n) (y : V) (hadj : G.Adj (p.getVert i) y) :
    y ∈ (spliceFacePath p n q).support := by
  sorry

end

section
variable {V : Type u} {G : SimpleGraph V} [Fintype V] {C : Type v}

theorem OriginalBoundaryInstance.short_facial_arc_backward_face_preserved (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace I.embedding I.outer z ∧ z ∉ p.support)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (i : ZMod p.length) :
    I.embedding.facePerm (toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) i)) =
      toDart cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) (i-1)) := by
  sorry

theorem OriginalBoundaryInstance.short_closed_face_prefix_inner_face_vertices (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (_hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) (z : V) :
    OnOuterFace I.embedding
      (walkArcRoot p hp).symm z ↔
      z ∈ (spliceFacePath p n q).support := by
  sorry

theorem OriginalBoundaryInstance.short_closed_face_prefix_unique (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q q' : G.Walk (p.getVert n) a) (hq : q.IsPath) (hq' : q'.IsPath)
    (hql : 0 < q.length) (hql' : 0 < q'.length)
    (hshort : n+q.length ≤ 6) (hshort' : n+q'.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hInner' : ∀ j, 0 < j → j < q'.length → ¬ OnOuterFace I.embedding I.outer (q'.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    (∀ z, z ∈ (spliceFacePath p n q).support ↔ z ∈ (spliceFacePath p n q').support) ∧
      q.length=q'.length := by
  sorry

end

section
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

theorem OriginalBoundaryInstance.interior_three_path_facial_corners (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    I.embedding.facePerm (walkArcRoot p hp).symm =
      ⟨(a,y),hya.symm⟩ ∧
    I.embedding.facePerm ⟨(a,y),hya.symm⟩ = ⟨(y,x),hxy.symm⟩ := by
  sorry

theorem OriginalBoundaryInstance.interior_three_path_across_two_face_edges_unique (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y x' y' : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hx' : ¬ OnOuterFace I.embedding I.outer x') (hy' : ¬ OnOuterFace I.embedding I.outer y')
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbx' : G.Adj (p.getVert 2) x') (hxy' : G.Adj x' y') (hya' : G.Adj y' a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : x=x' ∧ y=y' := by
  sorry

theorem OriginalBoundaryInstance.middle_vertex_of_interior_three_path_neighbours (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2 := by
  sorry

end

end Thomassen
