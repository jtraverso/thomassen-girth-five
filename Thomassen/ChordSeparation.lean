/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleSeparation
public import Thomassen.CycleWalk

/-! Removing the duplicated old boundary arc from a cycle side. -/

@[expose] public section
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
  classical
  obtain ⟨b, hb⟩ := hB.1
  let f : V → V := fun x => if x ∈ A then b else x
  have hmap : ∀ x y, G.Adj x y → x ∈ T → y ∈ T → RIn G (T \ A) (f x) (f y) := by
    intro x y hxy hx hy
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · simp only [f, ite_eq_left hxA, ite_eq_left hyA]
      exact .refl _
    · have hyB := hboundary x hxA y ⟨hy, hyA⟩ hxy
      simpa only [f, ite_eq_left hxA, ite_eq_right hyA] using (hB.2 b hb y hyB).mono_set hBW
    · have hxB := hboundary y hyA x ⟨hx, hxA⟩ hxy.symm
      simpa only [f, ite_eq_right hxA, ite_eq_left hyA] using (hB.2 x hxB b hb).mono_set hBW
    · simpa only [f, ite_eq_right hxA, ite_eq_right hyA] using RIn.single (s := T \ A) hxy ⟨hx, hxA⟩ ⟨hy, hyA⟩
  refine ⟨⟨b, hBW hb⟩, ?_⟩
  intro x hx y hy
  have h := (hT.2 x hx.1 y hy.1).map f hmap
  simpa only [f, ite_eq_right hx.2, ite_eq_right hy.2] using h

/-- Move a duplicated boundary arc to one piece. No edge is lost, and the new
intersection is the old intersection with precisely that arc removed. -/
lemma trim_separation (S T C A : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = C)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hAC : A ⊆ C) (hnoexit : ∀ x ∈ A, ∀ y ∈ T \ C, ¬ G.Adj x y) :
    S ∪ (T \ A) = Set.univ ∧ S ∩ (T \ A) = C \ A ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T \ A ∧ y ∈ T \ A)) := by
  have hCS : C ⊆ S := fun x hx => ((hinter ▸ hx : x ∈ S ∩ T)).1
  have hCT : C ⊆ T := fun x hx => ((hinter ▸ hx : x ∈ S ∩ T)).2
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ x
    rcases hx with hx | hx
    · exact Or.inl hx
    · by_cases hA : x ∈ A
      · exact Or.inl (hCS (hAC hA))
      · exact Or.inr ⟨hx, hA⟩
  · ext x
    constructor
    · rintro ⟨hxS, hxT, hxA⟩
      exact ⟨(hinter ▸ (show x ∈ S ∩ T from ⟨hxS, hxT⟩)), hxA⟩
    · rintro ⟨hxC, hxA⟩
      exact ⟨hCS hxC, hCT hxC, hxA⟩
  · intro x y hxy
    rcases hedges hxy with h | ⟨hxT, hyT⟩
    · exact Or.inl h
    · by_cases hxA : x ∈ A
      · by_cases hyC : y ∈ C
        · exact Or.inl ⟨hCS (hAC hxA), hCS hyC⟩
        · exact (hnoexit x hxA y ⟨hyT, hyC⟩ hxy).elim
      · by_cases hyA : y ∈ A
        · by_cases hxC : x ∈ C
          · exact Or.inl ⟨hCS hxC, hCS (hAC hyA)⟩
          · exact (hnoexit y hyA x ⟨hxT, hxC⟩ hxy.symm).elim
        · exact Or.inr ⟨⟨hxT, hxA⟩, ⟨hyT, hyA⟩⟩

variable [Fintype V]

/-- Only the predecessor step of a particular gap is needed to certify that
the gap is empty; the rest of the smaller face need not be preserved. -/
lemma eq_of_isNextH_of_preserved_predecessor (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    {d : G.Dart} {e : H.Dart}
    (hstep : M.facePerm (toDart hH ((restrictMap M hH).facePerm⁻¹ e)) = toDart hH e)
    (hd : IsNextH M hH d e) : d = toDart hH e := by
  obtain ⟨n, hn, hmin⟩ := hd
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using hn
  · exfalso
    have h2 : (M.rot ^ (n - 1)) d =
        (toDart hH ((restrictMap M hH).facePerm⁻¹ e)).symm := by
      apply M.rot.injective
      rw [← PlaneMap.facePerm_apply, hstep, ← Equiv.Perm.mul_apply, ← pow_succ',
        Nat.sub_add_cancel hpos, hn]
    exact hmin (n - 1) (by omega) (by rw [h2]; exact ((restrictMap M hH).facePerm⁻¹ e).adj.symm)

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
  obtain ⟨i, rfl⟩ := eq_of_sameCycle_cyc
    (cycle_face_forward (restrictMap M cyclicSubgraph_le) hc hk) he
  have hiA : c i ∈ cycleArcInterior c := by
    have hfst := isNextH_fst M cyclicSubgraph_le hn
    change c i = d.fst at hfst
    exact hfst.symm ▸ hx
  have hi0 : c i ≠ c 0 := fun h => hiA.2 (Or.inl h)
  have hi1 : c i ≠ c (-1) := fun h => hiA.2 (Or.inr (Set.mem_singleton_iff.2 h))
  have hprev : (restrictMap M cyclicSubgraph_le).facePerm⁻¹ (cycleForward hc i) =
      cycleForward hc (i - 1) := by
    apply (restrictMap M cyclicSubgraph_le).facePerm.injective
    simpa using (cycle_face_forward (restrictMap M cyclicSubgraph_le) hc hk (i - 1)).symm
  apply eq_of_isNextH_of_preserved_predecessor M cyclicSubgraph_le ?_ hn
  rw [hprev]
  exact hArc i hi0 hi1

/-- An internal old-arc vertex has no neighbour strictly on the exterior side. -/
lemma cycle_arc_no_exterior_neighbour (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) {x y : V} (hx : x ∈ cycleArcInterior c)
    (hy : y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) \ Set.range c) :
    ¬ G.Adj x y := by
  intro hxy
  let d : G.Dart := ⟨(x, y), hxy⟩
  have hxH : x ∈ subVerts (cyclicSubgraph G c) := by
    rw [cyclicSubgraph_subVerts hc]
    exact hx.1
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
  have hd := cycle_arc_gap_empty M hc hk hArc hx hface he
  have hys : d.snd ∈ subVerts (cyclicSubgraph G c) := by
    rw [hd]
    exact ⟨e.fst, e.adj.symm⟩
  exact hyH hys

omit [Fintype V] in
/-- All vertices of the cyclic arc, including both ends, are on its original
face. The last endpoint is reached by the last old arc edge, not by the chord. -/
lemma cycle_arc_vertices_on_outer (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hArc : IsFacialCycleArc M hc) : ∀ x ∈ Set.range c,
    OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x := by
  have hwalk : ∀ n : ℕ, n + 1 < k →
      SameCycle M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0))
        (toDart cyclicSubgraph_le (cycleForward hc (n : ZMod k))) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [Nat.cast_zero] using
        (SameCycle.refl M.facePerm (toDart cyclicSubgraph_le (cycleForward hc 0)))
    | succ n ih =>
      intro hn
      have hi0 : c ((n + 1 : ℕ) : ZMod k) ≠ c 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff (n + 1) k).1 (hc.inj h)
        have := Nat.le_of_dvd (by omega : 0 < n + 1) hd
        omega
      have hi1 : c ((n + 1 : ℕ) : ZMod k) ≠ c (-1) := by
        intro h
        have heq := hc.inj h
        have hz : ((n + 2 : ℕ) : ZMod k) = 0 := by
          push_cast at heq ⊢
          linear_combination heq
        have hd := (ZMod.natCast_eq_zero_iff (n + 2) k).1 hz
        have := Nat.le_of_dvd (by omega : 0 < n + 2) hd
        omega
      have hstep := hArc ((n + 1 : ℕ) : ZMod k) hi0 hi1
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hstep
      exact (ih (by omega)).trans ⟨1, by simpa only [zpow_one, Nat.cast_add, Nat.cast_one] using hstep⟩
  rintro x ⟨i, rfl⟩
  have hi := ZMod.val_lt i
  by_cases hlt : i.val + 1 < k
  · exact ⟨toDart cyclicSubgraph_le (cycleForward hc i),
      by simpa only [ZMod.natCast_zmod_val] using hwalk i.val hlt, rfl⟩
  · have heq : i.val = k - 1 := by omega
    let d := toDart cyclicSubgraph_le (cycleForward hc ((k - 2 : ℕ) : ZMod k))
    have hd := hwalk (k - 2) (by omega)
    have hidx : ((k - 2 : ℕ) : ZMod k) + 1 = i := by
      rw [← Nat.cast_one, ← Nat.cast_add, show k - 2 + 1 = i.val by omega, ZMod.natCast_zmod_val]
    refine ⟨M.facePerm d, hd.trans ⟨1, by simp [d]⟩, ?_⟩
    have hfst : (M.facePerm d).fst = d.snd := M.isRotationSystem.fst_apply _
    change (M.facePerm d).fst = c i
    rw [hfst]
    change c (((k - 2 : ℕ) : ZMod k) + 1) = c i
    rw [hidx]

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
  let hN := restrict_le G (subfaceSide M cyclicSubgraph_le (cycleBackward hc 0))
  let gd := toDart hN d
  have hx : d.fst ∈ subVerts (cyclicSubgraph G c) :=
    (isNextH_fst M cyclicSubgraph_le hn) ▸ ⟨e.snd, e.adj⟩
  have hxC : d.fst ∈ Set.range c := by rwa [← cyclicSubgraph_subVerts hc]
  by_cases hyC : d.snd ∈ Set.range c
  · have hy : d.snd ∈ subVerts (cyclicSubgraph G c) := by rwa [cyclicSubgraph_subVerts hc]
    by_cases hedge : (cyclicSubgraph G c).Adj d.fst d.snd
    · exact hedge
    · by_cases hxA : d.fst ∈ cycleArcInterior c
      · have hd := cycle_arc_gap_empty M hc hk hArc hxA he hn
        change gd = toDart cyclicSubgraph_le e at hd
        have h : InH (cyclicSubgraph G c) gd := by rw [hd]; exact e.adj
        exact h
      · by_cases hyA : d.snd ∈ cycleArcInterior c
        · obtain ⟨f, hf⟩ := exists_isNextH M cyclicSubgraph_le (d := gd.symm) hy
          have hfaces := sameCycle_of_chord M cyclicSubgraph_le (cyclicSubgraph_connected hc)
            (d := gd) hx hy hedge hn hf
          have hd := cycle_arc_gap_empty M hc hk hArc hyA (he.trans hfaces) hf
          have h : InH (cyclicSubgraph G c) gd.symm := by rw [hd]; exact f.adj
          exact h.symm
        · have hxB : d.fst ∈ ({c 0, c (-1)} : Set V) := by
            by_contra h
            exact hxA ⟨hxC, h⟩
          have hyB : d.snd ∈ ({c 0, c (-1)} : Set V) := by
            by_contra h
            exact hyA ⟨hyC, h⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxB hyB
          have hback : (cyclicSubgraph G c).Adj (c 0) (c (-1)) := by
            simpa only [cycleBackward, zero_sub] using (cycleBackward hc 0).adj
          rcases hxB with hxB | hxB <;> rcases hyB with hyB | hyB
          · exact (d.adj.1.ne (hxB.trans hyB.symm)).elim
          · exact hxB.symm ▸ hyB.symm ▸ hback
          · exact hxB.symm ▸ hyB.symm ▸ hback.symm
          · exact (d.adj.1.ne (hxB.trans hyB.symm)).elim
  · have hy : d.snd ∉ subVerts (cyclicSubgraph G c) := by rwa [cyclicSubgraph_subVerts hc]
    have hinside : inSubface M cyclicSubgraph_le (cycleBackward hc 0) d.snd := by
      rcases d.adj.2.2 with h | h
      · exact (hy (subfaceVertices_subset M cyclicSubgraph_le _ h)).elim
      · exact h
    have houtside : inSubface M cyclicSubgraph_le (cycleForward hc 0) d.snd :=
      ⟨hy, gd, e, hx, hy, hn, he, .refl _⟩
    have hne := cycle_faces_distinct (restrictMap M cyclicSubgraph_le) hc hk
    exact (hne (sameCycle_of_inSubface M cyclicSubgraph_le (cyclicSubgraph_connected hc)
      houtside hinside)).elim

/-- Exact face transport once the actual cycle face steps are preserved in a
retained graph. The preservation proof is supplied geometrically below. -/
lemma cycle_face_after_restriction (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    {N : SimpleGraph V} (hN : N ≤ G) (hHN : cyclicSubgraph G c ≤ N)
    (o : (cyclicSubgraph G c).Dart)
    (hface : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm o e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e)) (x : V) :
    OnOuterFace (restrictMap M hN) (toDart hHN o) x ↔ x ∈ Set.range c := by
  constructor
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨e, he, hed⟩ := exists_dart_of_preserved_subface M hN hHN o hface hd
    apply (cycle_outer_iff (restrictMap M cyclicSubgraph_le) hc hk o x).1
    refine ⟨e, he, ?_⟩
    rw [← toDart_fst hHN e, hed]
    exact hdx
  · intro hx
    obtain ⟨e, he, hfst⟩ := (cycle_outer_iff (restrictMap M cyclicSubgraph_le) hc hk o x).2 hx
    exact ⟨toDart hHN e, sameCycle_of_preserved_subface M hN hHN o hface he, hfst⟩

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
  classical
  let inside := cycleBackward hc 0
  let outside := cycleForward hc 0
  let S := subfaceSide M cyclicSubgraph_le inside
  let R := subfaceSide M cyclicSubgraph_le outside
  let A := cycleArcInterior c
  let B : Set V := {c 0, c (-1)}
  let T := R \ A
  have hBC : B ⊆ Set.range c := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, rfl⟩
    · exact ⟨-1, (Set.mem_singleton_iff.1 hx).symm⟩
  have hAC : A ⊆ Set.range c := fun _ hx => hx.1
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
    fun _ hx _ hy => cycle_arc_no_exterior_neighbour M hc hk hArc hx hy
  obtain ⟨hnewcover, hnewinter, hnewedges⟩ := trim_separation S R (Set.range c) A
    hcover hinter hedges hAC hnoexit
  have hCB : Set.range c \ A = B := by
    ext x
    constructor
    · rintro ⟨hxC, hxA⟩
      by_contra hxB
      exact hxA ⟨hxC, hxB⟩
    · intro hxB
      exact ⟨hBC hxB, fun h => h.2 hxB⟩
  have hBW : B ⊆ T := fun x hx => ⟨hRC x (hBC hx), fun h => h.2 hx⟩
  have hab : G.Adj (c 0) (c (-1)) := by simpa using (hc.adj (-1)).symm
  have hBconn : ConnSet G B :=
    (connSet_singleton G (c (-1))).insert_adj (Set.mem_singleton _) hab
  have hSconn : (G.induce S).Connected :=
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le inside)
  have hTconn : (G.induce T).Connected := by
    apply (connSet_iff_induce_connected _ _).1
    apply connSet_sdiff_of_connected_boundary R A B
      (subfaceSide_connSet M cyclicSubgraph_le outside) hBconn hBW
    intro x hx y hy hxy
    have hyC : y ∈ Set.range c := by
      by_contra hyC
      exact hnoexit x hx y ⟨hy.1, hyC⟩ hxy
    by_contra hyB
    exact hy.2 ⟨hyC, hyB⟩
  let outer := toDart cyclicSubgraph_le outside
  have hnext : IsNextH M cyclicSubgraph_le outer outside :=
    ⟨0, rfl, fun m hm => (Nat.not_lt_zero m hm).elim⟩
  have hOld : ∀ x, OnOuterFace M outer x → x ∈ R :=
    cycle_original_face_subset_side M hc hk outer (SameCycle.refl _ _) hnext
  obtain ⟨z, hzOld, hzC⟩ := houtside
  have hzS : z ∉ S := fun hzS =>
    hzC (hinter ▸ (show z ∈ S ∩ R from ⟨hzS, hOld z hzOld⟩))
  have h1A : c 1 ∈ A := by
    have h10 : c 1 ≠ c 0 := by simpa using (hc.adj 0).ne.symm
    have h1m : c 1 ≠ c (-1) := by
      intro h
      have heq := hc.inj h
      apply zmod_two_ne_zero_of_three_le hk
      linear_combination heq
    exact ⟨⟨1, rfl⟩, fun h => h.elim h10 (fun h => h1m (Set.mem_singleton_iff.1 h))⟩
  have h1T : c 1 ∉ T := fun h => h.2 h1A
  have hne := cycle_faces_distinct (restrictMap M cyclicSubgraph_le) hc hk
  have hTW0 : c 0 ∈ T := hBW (Or.inl rfl)
  have hTW1 : c (-1) ∈ T := hBW (Or.inr (Set.mem_singleton _))
  have hAdjT : (G.induce T).Adj ⟨c 0, hTW0⟩ ⟨c (-1), hTW1⟩ := hab
  let : Nontrivial T := hAdjT.nontrivial
  obtain ⟨oT, hTface⟩ := exists_outer_induced_of_preconnected M outer T hTconn.preconnected
  refine ⟨S, T, card_induced_vertices_lt S hzS, card_induced_vertices_lt T h1T,
    hnewcover, hnewinter.trans hCB, hnewedges, hSconn, hTconn, hSC,
    fun x hx hxA => ⟨hOld x hx, hxA⟩, ?_, ⟨oT, hTface⟩⟩
  let hN := restrict_le G S
  let hHN := cyclicSubgraph_le_side M hc hk inside
  have hface : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm outside e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e) := by
    intro e he
    exact facePerm_restrict_of_empty_gaps M hN hHN outside
      (fun d e hn he => facial_arc_inside_gap_empty M hc hk hArc d e hn he) he
  refine ⟨induceDartEquiv G S (toDart hHN outside), ?_⟩
  intro x
  rw [inducedPlaneMap_onOuterFace_iff]
  exact cycle_face_after_restriction M hc hk hN hHN outside hface x.1

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
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have h0 : walkCycleVertices p 0 = a := by
    simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hvneg : (-1 : ZMod p.length).val = p.length - 1 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.length ≠ 0)
    rw [hn, ZMod.val_neg_one, Nat.succ_sub_one]
  have hlast : walkCycleVertices p (-1) = p.penultimate := by
    simp only [walkCycleVertices, hvneg, Walk.penultimate]
  have hOld : ∀ x, OnOuterFace M outer x ↔ OnOuterFace M (walkArcRoot p hp) x := by
    intro x
    constructor
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hroot.symm.trans hd, hdx⟩
    · rintro ⟨d, hd, hdx⟩
      exact ⟨d, hroot.trans hd, hdx⟩
  have hw : ∃ x, OnOuterFace M (walkArcRoot p hp) x ∧
      x ∉ Set.range (walkCycleVertices p) := by
    obtain ⟨x, hx, hxC⟩ := houtside
    refine ⟨x, (hOld x).1 hx, ?_⟩
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using hxC
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSconn, hTconn,
    hSC, hkeep, ⟨oS, hSface⟩, ⟨oT, hTface⟩⟩ :=
    facial_arc_chord_separation M (walk_isCycleMap p hp) hk hArc hconn hw
  refine ⟨S, T, hSsmall, hTsmall, hcover, ?_, hedges, hSconn, hTconn, ?_, ?_,
    ⟨oS, ?_⟩, ⟨oT, ?_⟩⟩
  · simpa only [h0, hlast] using hinter
  · intro x hx
    apply hSC x
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using hx
  · intro x hx hxA
    apply hkeep x ((hOld x).1 hx)
    simpa only [cycleArcInterior, walkCycleVertices_range p hp, h0, hlast] using hxA
  · intro x
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using hSface x
  · intro x hx
    exact hTface x ((hOld x.1).1 hx)

end Thomassen
