/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ChordSeparation
public import Thomassen.FaceMerge

/-! Cutting off a facial arc with a connected path as its separator. -/

@[expose] public section
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
  obtain ⟨i, rfl⟩ := eq_of_sameCycle_cyc
    (cycle_face_forward (restrictMap M cyclicSubgraph_le) hc hk) he
  have hiA : c i ∈ A := by
    have hfst := isNextH_fst M cyclicSubgraph_le hn
    change c i = d.fst at hfst
    exact hfst.symm ▸ hx
  have hprev : (restrictMap M cyclicSubgraph_le).facePerm⁻¹ (cycleForward hc i) =
      cycleForward hc (i - 1) := by
    apply (restrictMap M cyclicSubgraph_le).facePerm.injective
    simpa using (cycle_face_forward (restrictMap M cyclicSubgraph_le) hc hk (i - 1)).symm
  apply eq_of_isNextH_of_preserved_predecessor M cyclicSubgraph_le ?_ hn
  rw [hprev]
  exact hArc i hiA

lemma cycle_no_exterior_neighbour_along (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (A : Set V) (hAC : A ⊆ Set.range c) (hArc : IsFacialCycleAlong M hc A) {x y : V} (hx : x ∈ A)
    (hy : y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) \ Set.range c) :
    ¬ G.Adj x y := by
  intro hxy
  let d : G.Dart := ⟨(x, y), hxy⟩
  have hxH : x ∈ subVerts (cyclicSubgraph G c) := by
    rw [cyclicSubgraph_subVerts hc]
    exact hAC hx
  have hyH : y ∉ subVerts (cyclicSubgraph G c) := by
    rw [cyclicSubgraph_subVerts hc]
    exact hy.2
  obtain ⟨e, he⟩ := exists_isNextH M cyclicSubgraph_le (d := d) hxH
  have hr : inSubface M cyclicSubgraph_le (cycleForward hc 0) y := by
    rcases hy.1 with h | h
    · exact (hyH (subfaceVertices_subset M cyclicSubgraph_le _ h)).elim
    · exact h
  have hcustom : inSubface M cyclicSubgraph_le e y :=
    ⟨hyH, d, e, hxH, hyH, he, SameCycle.refl _ _, .refl _⟩
  have hface := sameCycle_of_inSubface M cyclicSubgraph_le (cyclicSubgraph_connected hc) hr hcustom
  have hd := cycle_gap_empty_along M hc hk A hArc hx hface he
  have hys : d.snd ∈ subVerts (cyclicSubgraph G c) := by
    rw [hd]
    exact ⟨e.fst, e.adj.symm⟩
  exact hyH hys

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
  let hN := restrict_le G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))
  let gd := toDart hN d
  have hx : d.fst ∈ subVerts (cyclicSubgraph G c) :=
    (isNextH_fst M cyclicSubgraph_le hn) ▸ ⟨e.snd, e.adj⟩
  have hxC : d.fst ∈ Set.range c := by rwa [← cyclicSubgraph_subVerts hc]
  by_cases hyC : d.snd ∈ Set.range c
  · have hy : d.snd ∈ subVerts (cyclicSubgraph G c) := by rwa [cyclicSubgraph_subVerts hc]
    by_cases hedge : (cyclicSubgraph G c).Adj d.fst d.snd
    · exact hedge
    · by_cases hxA : d.fst ∈ A
      · have hd := cycle_gap_empty_along M hc hk A hArc hxA he hn
        change gd = toDart cyclicSubgraph_le e at hd
        have h : InH (cyclicSubgraph G c) gd := by rw [hd]; exact e.adj
        exact h
      · by_cases hyA : d.snd ∈ A
        · obtain ⟨f, hf⟩ := exists_isNextH M cyclicSubgraph_le (d := gd.symm) hy
          have hfaces := sameCycle_of_chord M cyclicSubgraph_le (cyclicSubgraph_connected hc)
            (d := gd) hx hy hedge hn hf
          have hd := cycle_gap_empty_along M hc hk A hArc hyA (he.trans hfaces) hf
          have h : InH (cyclicSubgraph G c) gd.symm := by rw [hd]; exact f.adj
          exact h.symm
        · exact hB ⟨hxC, hxA⟩ ⟨hyC, hyA⟩ d.adj.1
  · have hy : d.snd ∉ subVerts (cyclicSubgraph G c) := by rwa [cyclicSubgraph_subVerts hc]
    have hinside : inSubface M cyclicSubgraph_le (cycleBackward hc 0) d.snd := by
      rcases d.adj.2.2 with h | h
      · exact (hy (subfaceVertices_subset M cyclicSubgraph_le _ h)).elim
      · exact h
    have houtside : inSubface M cyclicSubgraph_le (cycleForward hc 0) d.snd :=
      ⟨hy, gd, e, hx, hy, hn, he, .refl _⟩
    exact (cycle_faces_distinct (restrictMap M cyclicSubgraph_le) hc hk
      (sameCycle_of_inSubface M cyclicSubgraph_le (cyclicSubgraph_connected hc) houtside hinside)).elim

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
    cycleSideSkeleton M c o ≤ G := fun _ _ h => h.1

lemma cyclicSubgraph_le_skeleton (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) : cyclicSubgraph G c ≤ cycleSideSkeleton M c o := by
  intro x y hxy
  have h := cyclicSubgraph_le_side M hc hk o hxy
  exact ⟨h.1, h.2.1, h.2.2, Or.inr (Or.inr hxy)⟩

/-- Removing just the extra chords does not disconnect a closed cycle side:
a missing edge is replaced by a walk along the retained cycle. -/
lemma cycleSideSkeleton_connSet (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    ConnSet (cycleSideSkeleton M c o) (subfaceSide M cyclicSubgraph_le o) := by
  let R := subfaceSide M cyclicSubgraph_le o
  let N := cycleSideSkeleton M c o
  have hR := subfaceSide_connSet M cyclicSubgraph_le o
  have hC : ConnSet (cyclicSubgraph G c) (Set.range c) := by
    have h := onOuterFace_connSet (restrictMap M cyclicSubgraph_le) o
    change ConnSet (cyclicSubgraph G c) (subfaceVertices M cyclicSubgraph_le o) at h
    rwa [cycle_subface_vertices M hc hk o] at h
  have hCR : Set.range c ⊆ R := fun x hx =>
    Or.inl (by rwa [cycle_subface_vertices M hc hk o])
  have hmap : ∀ x y, G.Adj x y → x ∈ R → y ∈ R → RIn N R x y := by
    intro x y hxy hx hy
    by_cases hxC : x ∈ Set.range c <;> by_cases hyC : y ∈ Set.range c
    · exact (hC.2 x hxC y hyC).mono (cyclicSubgraph_le_skeleton M hc hk o) hCR
    · exact .single ⟨hxy, hx, hy, Or.inr (Or.inl hyC)⟩ hx hy
    · exact .single ⟨hxy, hx, hy, Or.inl hxC⟩ hx hy
    · exact .single ⟨hxy, hx, hy, Or.inl hxC⟩ hx hy
  refine ⟨hR.1, ?_⟩
  intro x hx y hy
  have h := (hR.2 x hx y hy).map id hmap
  exact h

/-- No skeleton edge can enter a gap of the opposite cycle face. In contrast
to an induced side, it contains no extra chord between cycle vertices. -/
lemma cycleSideSkeleton_opposite_gap_empty (M : PlaneMap G) (hc : IsCycleMap G c)
    (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right)
    (d : (cycleSideSkeleton M c left).Dart) (e : (cyclicSubgraph G c).Dart)
    (hn : IsNextH M cyclicSubgraph_le (toDart (cycleSideSkeleton_le M left) d) e)
    (he : SameCycle (restrictMap M cyclicSubgraph_le).facePerm right e) :
    (cyclicSubgraph G c).Adj d.fst d.snd := by
  have hx : d.fst ∈ subVerts (cyclicSubgraph G c) :=
    (isNextH_fst M cyclicSubgraph_le hn) ▸ ⟨e.snd, e.adj⟩
  by_cases hy : d.snd ∈ subVerts (cyclicSubgraph G c)
  · rcases d.adj.2.2.2 with h | h | h
    · exact (h (by rwa [← cyclicSubgraph_subVerts hc])).elim
    · exact (h (by rwa [← cyclicSubgraph_subVerts hc])).elim
    · exact h
  · have hleft : inSubface M cyclicSubgraph_le left d.snd := by
      rcases d.adj.2.2.1 with h | h
      · exact (hy (subfaceVertices_subset M cyclicSubgraph_le _ h)).elim
      · exact h
    have hright : inSubface M cyclicSubgraph_le right d.snd :=
      ⟨hy, toDart (cycleSideSkeleton_le M left) d, e, hx, hy, hn, he, .refl _⟩
    exact (hne (sameCycle_of_inSubface M cyclicSubgraph_le
      (cyclicSubgraph_connected hc) hleft hright)).elim

/-- The opposite cycle face is an actual face in the skeleton map. -/
lemma cycleSideSkeleton_face_iff (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (left right : (cyclicSubgraph G c).Dart)
    (hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm left right) (x : V) :
    OnOuterFace (restrictMap M (cycleSideSkeleton_le M left))
      (toDart (cyclicSubgraph_le_skeleton M hc hk left) right) x ↔ x ∈ Set.range c := by
  apply cycle_face_after_restriction M hc hk (cycleSideSkeleton_le M left)
    (cyclicSubgraph_le_skeleton M hc hk left) right
  intro e he
  exact facePerm_restrict_of_empty_gaps M (cycleSideSkeleton_le M left)
    (cyclicSubgraph_le_skeleton M hc hk left) right
    (fun d e hn he => cycleSideSkeleton_opposite_gap_empty M hc left right hne d e hn he) he

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
  let inside := cycleBackward hc 0
  let outside := cycleForward hc 0
  let S := subfaceSide M cyclicSubgraph_le inside
  let R := subfaceSide M cyclicSubgraph_le outside
  let B := Set.range c \ A
  let T := R \ A
  have hSC : ∀ x ∈ Set.range c, x ∈ S := fun x hx =>
    Or.inl (by rwa [cycle_subface_vertices M hc hk inside])
  have hRC : ∀ x ∈ Set.range c, x ∈ R := fun x hx =>
    Or.inl (by rwa [cycle_subface_vertices M hc hk outside])
  have hcover : S ∪ R = Set.univ := by
    rw [Set.union_comm]
    exact cycle_sides_cover M hc hk hconn
  have hinter : S ∩ R = Set.range c := by
    rw [Set.inter_comm]
    exact cycle_sides_inter M hc hk
  have hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ R ∧ y ∈ R) :=
    fun {_ _} h => (cycle_sides_no_crossing M hc hk hconn h).symm
  have hnoexit : ∀ x ∈ A, ∀ y ∈ R \ Set.range c, ¬ G.Adj x y :=
    fun _ hx _ hy => cycle_no_exterior_neighbour_along M hc hk A hAC hArc hx hy
  obtain ⟨hnewcover, hnewinter, hnewedges⟩ := trim_separation S R (Set.range c) A
    hcover hinter hedges hAC hnoexit
  have hBW : B ⊆ T := fun x hx => ⟨hRC x hx.1, hx.2⟩
  have hSconn : (G.induce S).Connected :=
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le inside)
  have hTconn : (G.induce T).Connected := by
    apply (connSet_iff_induce_connected _ _).1
    apply connSet_sdiff_of_connected_boundary R A B (subfaceSide_connSet M cyclicSubgraph_le outside)
      (hBconn.mono cyclicSubgraph_le) hBW
    intro x hx y hy hxy
    have hyC : y ∈ Set.range c := by
      by_contra hyC
      exact hnoexit x hx y ⟨hy.1, hyC⟩ hxy
    exact ⟨hyC, hy.2⟩
  let old := toDart cyclicSubgraph_le outside
  have hnext : IsNextH M cyclicSubgraph_le old outside :=
    ⟨0, rfl, fun m hm => (Nat.not_lt_zero m hm).elim⟩
  have hOld : ∀ x, OnOuterFace M old x → x ∈ R :=
    cycle_original_face_subset_side M hc hk old (SameCycle.refl _ _) hnext
  obtain ⟨z, hzOld, hzC⟩ := houtside
  have hzS : z ∉ S := fun hzS =>
    hzC (hinter ▸ (show z ∈ S ∩ R from ⟨hzS, hOld z hzOld⟩))
  have h1T : c 1 ∉ T := fun h => h.2 h1
  have hTW0 : c 0 ∈ T := hBW ⟨⟨0, rfl⟩, h0⟩
  have hTWm : c (-1) ∈ T := hBW ⟨⟨-1, rfl⟩, hback⟩
  have hab : G.Adj (c 0) (c (-1)) := by simpa using (hc.adj (-1)).symm
  let : Nontrivial T := (show (G.induce T).Adj ⟨c 0, hTW0⟩ ⟨c (-1), hTWm⟩ from hab).nontrivial
  refine ⟨S, T, card_induced_vertices_lt S hzS, card_induced_vertices_lt T h1T,
    hnewcover, hnewinter, hnewedges, hSconn, hTconn, hSC,
    fun x hx hxA => ⟨hOld x hx, hxA⟩, ?_, ?_⟩
  · let hN := restrict_le G S
    let hHN := cyclicSubgraph_le_side M hc hk inside
    have hface : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm outside e →
        (restrictMap M hN).facePerm (toDart hHN e) =
          toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e) := by
      intro e he
      exact facePerm_restrict_of_empty_gaps M hN hHN outside
        (fun d e hn he => arc_path_inside_gap_empty M hc hk A hArc hBedge d e hn he) he
    refine ⟨induceDartEquiv G S (toDart hHN outside), ?_⟩
    intro x
    rw [inducedPlaneMap_onOuterFace_iff]
    exact cycle_face_after_restriction M hc hk hN hHN outside hface x.1
  · let N := cycleSideSkeleton M c outside
    let hN : N ≤ G := cycleSideSkeleton_le M outside
    let hHN : cyclicSubgraph G c ≤ N := cyclicSubgraph_le_skeleton M hc hk outside
    let MN := restrictMap M hN
    have hNconn : ConnSet N R := cycleSideSkeleton_connSet M hc hk outside
    have hNT : N.induce T = G.induce T := by
      ext x y
      change (G.Adj x.1 y.1 ∧ x.1 ∈ R ∧ y.1 ∈ R ∧
        (x.1 ∉ Set.range c ∨ y.1 ∉ Set.range c ∨ (cyclicSubgraph G c).Adj x.1 y.1)) ↔ G.Adj x.1 y.1
      constructor
      · exact And.left
      · intro hxy
        refine ⟨hxy, x.2.1, y.2.1, ?_⟩
        by_cases hx : x.1 ∈ Set.range c <;> by_cases hy : y.1 ∈ Set.range c
        · exact Or.inr (Or.inr (hBedge ⟨hx, x.2.2⟩ ⟨hy, y.2.2⟩ hxy))
        · exact Or.inr (Or.inl hy)
        · exact Or.inl hx
        · exact Or.inl hx
    have hNremain : (N.induce T).Preconnected := by rw [hNT]; exact hTconn.preconnected
    have hAN : ConnSet N A := hAconn.mono hHN
    let d : N.Dart := toDart hHN outside
    have hdT : d.fst ∈ T := hTW0
    have hdA : d.snd ∈ A := by simpa only [d, outside, toDart_snd, cycleForward, zero_add] using h1
    obtain ⟨oT, hOuterT, _, hOtherT⟩ := exists_outer_induced_merging_connected_set MN d T A
      hNremain hAN (fun _ hx hT => hT.2 hx) d (SameCycle.refl _ _) hdT hdA
    have hNclosed : restrict N R = N := by
      ext x y
      exact ⟨And.left, fun h => ⟨h, h.2.1, h.2.2.1⟩⟩
    have hNpre : (N.induce R).Preconnected :=
      ((connSet_iff_induce_connected _ _).1 hNconn).preconnected
    have hNR0 : c 0 ∈ R := hRC _ ⟨0, rfl⟩
    have hNR1 : c 1 ∈ R := hRC _ ⟨1, rfl⟩
    let : Nontrivial R := (show (G.induce R).Adj ⟨c 0, hNR0⟩ ⟨c 1, hNR1⟩ from (by
      change G.Adj (c 0) (c 1)
      simpa only [zero_add] using hc.adj 0)).nontrivial
    have hNactive : subVerts N = R := by
      have h := subVerts_restrict_of_preconnected (G := N) R hNpre
      rwa [hNclosed] at h
    have hcN : ∀ a ∈ subVerts N, ∀ b ∈ subVerts N, N.Reachable a b := by
      have h := restrict_reachable_of_induce_preconnected (G := N) R hNpre
      rwa [hNclosed] at h
    have hOldN : ∀ x : T, OnOuterFace M old x.1 → OnOuterFace MN d x.1 := by
      intro x hx
      apply onOuterFace_restrict_of_connected M hN hcN old (SameCycle.refl _ _)
        (show IsNextH M hN old d from ⟨0, rfl, fun m hm => (Nat.not_lt_zero m hm).elim⟩)
        (by rw [hNactive]; exact x.2.1) hx
    let inner : N.Dart := toDart hHN inside
    let t : N.Dart := toDart hHN (cycleBackward hc j)
    have hne : ¬ SameCycle (restrictMap M cyclicSubgraph_le).facePerm outside inside :=
      cycle_faces_distinct _ hc hk
    have hfaceN : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm inside e →
        MN.facePerm (toDart hHN e) = toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e) := by
      intro e he
      exact facePerm_restrict_of_empty_gaps M hN hHN inside
        (fun d e hn he => cycleSideSkeleton_opposite_gap_empty M hc outside inside hne d e hn he) he
    have htface : SameCycle MN.facePerm inner t :=
      sameCycle_of_preserved_subface M hN hHN inside hfaceN
        (cycle_backward_sameCycle (restrictMap M cyclicSubgraph_le) hc hk j)
    have htT : t.fst ∈ T := hBW ⟨⟨j, rfl⟩, hj⟩
    have htA : t.snd ∈ A := by simpa only [t, toDart_snd, cycleBackward] using hjprev
    have hPack : ∃ MT : PlaneMap (N.induce T), ∃ o : (N.induce T).Dart, ∀ x : T,
        OnOuterFace M old x.1 ∨ x.1 ∈ B → OnOuterFace MT o x := by
      refine ⟨inducedPlaneMap MN T, oT, ?_⟩
      intro x hx
      rcases hx with hx | hx
      · exact hOuterT x (hOldN x hx)
      · apply hOtherT inner t htface htT htA x
        exact (cycleSideSkeleton_face_iff M hc hk outside inside hne x.1).2 hx.1
    rwa [hNT] at hPack

end Thomassen
