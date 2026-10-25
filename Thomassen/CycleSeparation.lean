/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RegionSeparation
public import Thomassen.FaceRestriction
public import Grotzsch.FacialCycle

/-! Actual face orbits and sides of a simple cycle. -/

@[expose] public section
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

lemma cyclicSubgraph_le : cyclicSubgraph G c ≤ G := fun _ _ h => h.1

def cycleForward (hc : IsCycleMap G c) (i : ZMod k) : (cyclicSubgraph G c).Dart :=
  ⟨(c i, c (i + 1)), hc.adj i, i, Or.inl ⟨rfl, rfl⟩⟩

def cycleBackward (hc : IsCycleMap G c) (i : ZMod k) : (cyclicSubgraph G c).Dart :=
  ⟨(c i, c (i - 1)), by simpa using (hc.adj (i - 1)).symm,
    i - 1, Or.inr ⟨by simp, rfl⟩⟩

lemma cyclicSubgraph_subVerts (hc : IsCycleMap G c) :
    subVerts (cyclicSubgraph G c) = Set.range c := by
  ext x
  constructor
  · rintro ⟨y, _, i, ⟨hx, _⟩ | ⟨hx, _⟩⟩
    · exact ⟨i, hx.symm⟩
    · exact ⟨i + 1, hx.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨c (i + 1), (cycleForward hc i).adj⟩

lemma cyclicSubgraph_of_chordless (hch : IsChordless G c) {x y : V}
    (hx : x ∈ Set.range c) (hy : y ∈ Set.range c) (hxy : G.Adj x y) :
    (cyclicSubgraph G c).Adj x y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  refine ⟨hxy, ?_⟩
  rcases hch i j hxy with hj | hi
  · exact ⟨i, Or.inl ⟨rfl, congrArg c hj⟩⟩
  · exact ⟨j, Or.inr ⟨congrArg c hi, rfl⟩⟩

lemma cycleForward_symm (hc : IsCycleMap G c) (i : ZMod k) :
    (cycleForward hc i).symm = cycleBackward hc (i + 1) := by
  apply (Dart.ext_iff _ _).2
  simp [cycleForward, cycleBackward]

lemma cycleBackward_symm (hc : IsCycleMap G c) (i : ZMod k) :
    (cycleBackward hc i).symm = cycleForward hc (i - 1) := by
  apply (Dart.ext_iff _ _).2
  simp [cycleForward, cycleBackward]

lemma cyclic_dart_cases (hc : IsCycleMap G c) (d : (cyclicSubgraph G c).Dart) :
    (∃ i, d = cycleForward hc i) ∨ (∃ i, d = cycleBackward hc i) := by
  obtain ⟨i, hi | hi⟩ := d.adj.2
  · exact Or.inl ⟨i, (Dart.ext_iff _ _).2 (Prod.ext hi.1 hi.2)⟩
  · refine Or.inr ⟨i + 1, (Dart.ext_iff _ _).2 (Prod.ext hi.1 ?_)⟩
    simpa only [cycleBackward, add_sub_cancel_right] using hi.2

lemma cycleForward_ne_backward (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    cycleForward hc i ≠ cycleBackward hc i := by
  intro h
  have heq := hc.inj (congrArg (fun d : (cyclicSubgraph G c).Dart => d.snd) h)
  have hz : (2 : ZMod k) = 0 := by linear_combination heq
  have hdiv : k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 k).1 hz
  have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

/-- At every cycle vertex the restricted rotation exchanges its two darts. -/
lemma cycle_rot_forward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.rot (cycleForward hc i) = cycleBackward hc i := by
  have hfst := M.isRotationSystem.fst_apply (cycleForward hc i)
  rcases cyclic_dart_cases hc (M.rot (cycleForward hc i)) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hij : j = i := hc.inj (by simpa only [cycleForward, cycleBackward] using
      (congrArg (fun d : (cyclicSubgraph G c).Dart => d.fst) hj).symm.trans hfst)
    subst j
    have hsame := M.isRotationSystem.sameCycle (cycleForward hc i) (cycleBackward hc i) rfl
    exact False.elim (cycleForward_ne_backward hc hk i (hsame.eq_of_left hj))
  · have hij : j = i := hc.inj (by simpa only [cycleForward, cycleBackward] using
      (congrArg (fun d : (cyclicSubgraph G c).Dart => d.fst) hj).symm.trans hfst)
    exact hij ▸ hj

lemma cycle_rot_backward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.rot (cycleBackward hc i) = cycleForward hc i := by
  have hfst := M.isRotationSystem.fst_apply (cycleBackward hc i)
  rcases cyclic_dart_cases hc (M.rot (cycleBackward hc i)) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hij : j = i := hc.inj (by simpa only [cycleForward, cycleBackward] using
      (congrArg (fun d : (cyclicSubgraph G c).Dart => d.fst) hj).symm.trans hfst)
    exact hij ▸ hj
  · have hij : j = i := hc.inj (by simpa only [cycleForward, cycleBackward] using
      (congrArg (fun d : (cyclicSubgraph G c).Dart => d.fst) hj).symm.trans hfst)
    subst j
    have hsame := M.isRotationSystem.sameCycle (cycleBackward hc i) (cycleForward hc i) rfl
    exact False.elim ((cycleForward_ne_backward hc hk i).symm (hsame.eq_of_left hj))

lemma cycle_face_forward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.facePerm (cycleForward hc i) = cycleForward hc (i + 1) := by
  rw [PlaneMap.facePerm_apply, cycleForward_symm, cycle_rot_backward M hc hk]

lemma cycle_face_backward (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    M.facePerm (cycleBackward hc i) = cycleBackward hc (i - 1) := by
  rw [PlaneMap.facePerm_apply, cycleBackward_symm, cycle_rot_forward M hc hk]

variable [NeZero k]

lemma cyclicSubgraph_reachable (hc : IsCycleMap G c) (i j : ZMod k) :
    (cyclicSubgraph G c).Reachable (c i) (c j) := by
  have hwalk : ∀ n : ℕ, (cyclicSubgraph G c).Reachable (c i) (c (i + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [cycleForward, Nat.cast_add, Nat.cast_one, add_assoc] using
        ih.trans (cycleForward hc (i + n)).adj.reachable
  have h := hwalk (j - i).val
  simpa only [ZMod.natCast_zmod_val, add_sub_cancel] using h

lemma cyclicSubgraph_connected (hc : IsCycleMap G c) :
    ∀ a ∈ subVerts (cyclicSubgraph G c), ∀ b ∈ subVerts (cyclicSubgraph G c),
      (cyclicSubgraph G c).Reachable a b := by
  intro a ha b hb
  rw [cyclicSubgraph_subVerts hc] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact cyclicSubgraph_reachable hc i j

lemma cycle_forward_sameCycle (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    SameCycle M.facePerm (cycleForward hc 0) (cycleForward hc i) := by
  have hpow : ∀ n : ℕ, (M.facePerm ^ n) (cycleForward hc 0) = cycleForward hc (n : ZMod k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, cycle_face_forward M hc hk]
      simp only [Nat.cast_add, Nat.cast_one]
  exact ⟨(i.val : ℤ), by rw [zpow_natCast, hpow]; simp⟩

lemma cycle_backward_sameCycle (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (i : ZMod k) :
    SameCycle M.facePerm (cycleBackward hc 0) (cycleBackward hc i) := by
  have hpow : ∀ n : ℕ, (M.facePerm ^ n) (cycleBackward hc 0) = cycleBackward hc (-(n : ZMod k)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, cycle_face_backward M hc hk]
      congr 1
      push_cast
      ring
  exact ⟨((-i).val : ℤ), by rw [zpow_natCast, hpow]; simp⟩

lemma cycle_faces_distinct [Fintype V] (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    ¬ SameCycle M.facePerm (cycleForward hc 0) (cycleBackward hc 0) := by
  intro h
  obtain ⟨i, hi⟩ := eq_of_sameCycle_cyc (cycle_face_forward M hc hk) h
  have hi0 : i = 0 := hc.inj (congrArg (fun d : (cyclicSubgraph G c).Dart => d.fst) hi).symm
  subst i
  exact cycleForward_ne_backward hc hk 0 hi.symm

lemma cycle_two_faces (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (d : (cyclicSubgraph G c).Dart) :
    SameCycle M.facePerm (cycleForward hc 0) d ∨
      SameCycle M.facePerm (cycleBackward hc 0) d := by
  rcases cyclic_dart_cases hc d with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inl (cycle_forward_sameCycle M hc hk i)
  · exact Or.inr (cycle_backward_sameCycle M hc hk i)

lemma cycle_outer_forward_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (x : V) :
    OnOuterFace M (cycleForward hc 0) x ↔ x ∈ Set.range c := by
  constructor
  · rintro ⟨e, _, rfl⟩
    rw [← cyclicSubgraph_subVerts hc]
    exact ⟨e.snd, e.adj⟩
  · rintro ⟨i, rfl⟩
    exact ⟨cycleForward hc i, cycle_forward_sameCycle M hc hk i, rfl⟩

lemma cycle_outer_backward_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (x : V) :
    OnOuterFace M (cycleBackward hc 0) x ↔ x ∈ Set.range c := by
  constructor
  · rintro ⟨e, _, rfl⟩
    rw [← cyclicSubgraph_subVerts hc]
    exact ⟨e.snd, e.adj⟩
  · rintro ⟨i, rfl⟩
    exact ⟨cycleBackward hc i, cycle_backward_sameCycle M hc hk i, rfl⟩

lemma cycle_outer_iff (M : PlaneMap (cyclicSubgraph G c))
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (o : (cyclicSubgraph G c).Dart) (x : V) :
    OnOuterFace M o x ↔ x ∈ Set.range c := by
  constructor
  · rintro ⟨e, _, rfl⟩
    rw [← cyclicSubgraph_subVerts hc]
    exact ⟨e.snd, e.adj⟩
  · rintro ⟨i, rfl⟩
    rcases cyclic_dart_cases hc o with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨cycleForward hc i, (cycle_forward_sameCycle M hc hk j).symm.trans
        (cycle_forward_sameCycle M hc hk i), rfl⟩
    · exact ⟨cycleBackward hc i, (cycle_backward_sameCycle M hc hk j).symm.trans
        (cycle_backward_sameCycle M hc hk i), rfl⟩

variable [Fintype V]

lemma cycle_subface_forward (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceVertices M cyclicSubgraph_le (cycleForward hc 0) = Set.range c := by
  ext x
  exact cycle_outer_forward_iff _ hc hk x

lemma cycle_subface_backward (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceVertices M cyclicSubgraph_le (cycleBackward hc 0) = Set.range c := by
  ext x
  exact cycle_outer_backward_iff _ hc hk x

omit [NeZero k] [Fintype V] in
lemma rIn_univ_of_reachable {x y : V} (h : G.Reachable x y) : RIn G Set.univ x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | cons h p ih => exact (RIn.single h (Set.mem_univ _) (Set.mem_univ _)).trans ih

/-- The two actual cycle faces account for all components outside the cycle. -/
lemma cycle_sides_cover (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) :
    subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∪
      subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ subVerts (cyclicSubgraph G c)
  · apply Or.inl
    apply Or.inl
    rwa [cycle_subface_forward M hc hk, ← cyclicSubgraph_subVerts hc]
  · obtain ⟨o, ho⟩ := exists_inSubface M cyclicSubgraph_le hx
      ⟨c 1, by simpa only [cycleForward, zero_add] using (cycleForward hc 0).adj⟩ (rIn_univ_of_reachable (hconn x (c 0)))
    rcases cycle_two_faces (restrictMap M cyclicSubgraph_le) hc hk o with hf | hf
    · exact Or.inl (Or.inr ((inSubface_congr hf x).2 ho))
    · exact Or.inr (Or.inr ((inSubface_congr hf x).2 ho))

lemma cycle_sides_inter (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k) :
    subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∩
      subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) = Set.range c := by
  rw [two_face_sides_inter M cyclicSubgraph_le (cyclicSubgraph_connected hc)
    _ _ (cycle_faces_distinct _ hc hk), cycle_subface_forward M hc hk,
    cycle_subface_backward M hc hk, Set.inter_self]

lemma cycle_sides_no_crossing (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) {x y : V} (hxy : G.Adj x y) :
    (x ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∧
      y ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0)) ∨
    (x ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) ∧
      y ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0)) := by
  have side : ∀ z, z ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∨
      z ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) := by
    intro z
    have h := Set.mem_univ z
    rwa [← cycle_sides_cover M hc hk hconn] at h
  have active : ∀ z ∈ subVerts (cyclicSubgraph G c),
      z ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∧
      z ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) := by
    intro z hz
    rw [cyclicSubgraph_subVerts hc] at hz
    exact ⟨Or.inl (by rwa [cycle_subface_forward M hc hk]),
      Or.inl (by rwa [cycle_subface_backward M hc hk])⟩
  have outside {o : (cyclicSubgraph G c).Dart} {z : V}
      (hz : z ∉ subVerts (cyclicSubgraph G c))
      (hs : z ∈ subfaceSide M cyclicSubgraph_le o) : inSubface M cyclicSubgraph_le o z := by
    rcases hs with hs | hs
    · exact (hz (subfaceVertices_subset M cyclicSubgraph_le o hs)).elim
    · exact hs
  by_cases hx : x ∈ subVerts (cyclicSubgraph G c)
  · rcases side y with hy | hy
    · exact Or.inl ⟨(active x hx).1, hy⟩
    · exact Or.inr ⟨(active x hx).2, hy⟩
  · by_cases hy : y ∈ subVerts (cyclicSubgraph G c)
    · rcases side x with hs | hs
      · exact Or.inl ⟨hs, (active y hy).1⟩
      · exact Or.inr ⟨hs, (active y hy).2⟩
    · rcases side x with hs | hs
      · exact Or.inl ⟨hs, Or.inr (inSubface_of_rIn (outside hx hs)
          (RIn.single hxy hx hy))⟩
      · exact Or.inr ⟨hs, Or.inr (inSubface_of_rIn (outside hx hs)
          (RIn.single hxy hx hy))⟩

omit [NeZero k] in
/-- A face walk connects its boundary vertices within that boundary. -/
lemma onOuterFace_connSet (M : PlaneMap G) (o : G.Dart) :
    ConnSet G {x | OnOuterFace M o x} := by
  have hpow : ∀ n : ℕ, RIn G {x | OnOuterFace M o x} o.fst ((M.facePerm ^ n) o).fst := by
    intro n
    induction n with
    | zero => exact .refl _
    | succ n ih =>
      let d := (M.facePerm ^ n) o
      have hd : SameCycle M.facePerm o d := ⟨(n : ℤ), by simp [d]⟩
      have he : SameCycle M.facePerm o (M.facePerm d) := hd.trans ⟨1, by simp⟩
      have hfst : (M.facePerm d).fst = d.snd := M.isRotationSystem.fst_apply _
      have hedge : RIn G {x | OnOuterFace M o x} d.fst (M.facePerm d).fst := by
        rw [hfst]
        exact .single d.adj ⟨d, hd, rfl⟩ ⟨M.facePerm d, he, hfst⟩
      simpa only [pow_succ', Equiv.Perm.mul_apply] using ih.trans hedge
  have hroot : ∀ x, OnOuterFace M o x → RIn G {x | OnOuterFace M o x} o.fst x := by
    rintro x ⟨e, he, rfl⟩
    obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
    simpa only [hn] using hpow n
  exact ⟨⟨o.fst, onOuterFace_self M o⟩, fun a ha b hb => (hroot a ha).symm.trans (hroot b hb)⟩

omit [NeZero k] in
/-- A closed face side is connected: its attached components meet its connected
face boundary. No assertion about extension of colours is used. -/
lemma subfaceSide_connSet (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    (o : H.Dart) : ConnSet G (subfaceSide M hH o) := by
  have hboundary : ConnSet H (subfaceVertices M hH o) :=
    onOuterFace_connSet (restrictMap M hH) o
  have hsub : subfaceVertices M hH o ⊆ subfaceSide M hH o := fun _ hx => Or.inl hx
  have ho : o.fst ∈ subfaceVertices M hH o := ⟨o, SameCycle.refl _ _, rfl⟩
  have hroot : ∀ w ∈ subfaceSide M hH o, RIn G (subfaceSide M hH o) o.fst w := by
    intro w hw
    rcases hw with hw | ⟨hw, d, e, hd, hdout, hn, he, hp⟩
    · exact (hboundary.2 _ ho _ hw).mono hH hsub
    · have hdb : d.fst ∈ subfaceVertices M hH o := ⟨e, he, isNextH_fst M hH hn⟩
      have hcomponent := connSet_reach G (subVerts H)ᶜ hdout
      have hcomponentSub : {z | z ∈ (subVerts H)ᶜ ∧ RIn G (subVerts H)ᶜ d.snd z} ⊆
          subfaceSide M hH o := by
        intro z hz
        exact Or.inr ⟨hz.1, d, e, hd, hdout, hn, he, hz.2⟩
      have hstart : d.snd ∈ subfaceSide M hH o := hcomponentSub ⟨hdout, .refl _⟩
      have hpath := (hcomponent.2 d.snd ⟨hdout, .refl _⟩ w ⟨hw, hp⟩).mono_set hcomponentSub
      exact ((hboundary.2 _ ho _ hdb).mono hH hsub).trans
        ((RIn.single d.adj (hsub hdb) hstart).trans hpath)
  exact ⟨⟨o.fst, hsub ho⟩, fun a ha b hb => (hroot a ha).symm.trans (hroot b hb)⟩

lemma cycle_subface_vertices (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    subfaceVertices M cyclicSubgraph_le o = Set.range c := by
  ext x
  exact cycle_outer_iff _ hc hk o x

lemma cyclicSubgraph_le_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (o : (cyclicSubgraph G c).Dart) :
    cyclicSubgraph G c ≤ restrict G (subfaceSide M cyclicSubgraph_le o) := by
  intro x y hxy
  have hx : x ∈ subfaceVertices M cyclicSubgraph_le o := by
    rw [cycle_subface_vertices M hc hk, ← cyclicSubgraph_subVerts hc]
    exact ⟨y, hxy⟩
  have hy : y ∈ subfaceVertices M cyclicSubgraph_le o := by
    rw [cycle_subface_vertices M hc hk, ← cyclicSubgraph_subVerts hc]
    exact ⟨x, hxy.symm⟩
  exact ⟨hxy.1, Or.inl hx, Or.inl hy⟩

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
  have hx : d.fst ∈ subVerts (cyclicSubgraph G c) :=
    (isNextH_fst M cyclicSubgraph_le hn) ▸ ⟨e.snd, e.adj⟩
  by_cases hy : d.snd ∈ subVerts (cyclicSubgraph G c)
  · apply cyclicSubgraph_of_chordless hch
    · rwa [← cyclicSubgraph_subVerts hc]
    · rwa [← cyclicSubgraph_subVerts hc]
    · exact d.adj.1
  · have hleft : inSubface M cyclicSubgraph_le left d.snd := by
      rcases d.adj.2.2 with h | h
      · exact (hy (subfaceVertices_subset M cyclicSubgraph_le left h)).elim
      · exact h
    have hright : inSubface M cyclicSubgraph_le right d.snd :=
      ⟨hy, toDart (restrict_le G (subfaceSide M cyclicSubgraph_le left)) d,
        e, hx, hy, hn, he, .refl _⟩
    exact (hne (sameCycle_of_inSubface M cyclicSubgraph_le
      (cyclicSubgraph_connected hc) hleft hright)).elim

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
  let f := (restrictMap M (hHN.trans hN)).facePerm
  let f' := (restrictMap M hN).facePerm
  have hpow : ∀ n : ℕ, (f' ^ n) (toDart hHN o) = toDart hHN ((f ^ n) o) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change (restrictMap M hN).facePerm (toDart hHN ((f ^ n) o)) = _
      rw [hface ((f ^ n) o) ⟨(n : ℤ), by simp [f]⟩]
      rw [pow_succ', Equiv.Perm.mul_apply]
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  exact ⟨(f ^ n) o, ⟨(n : ℤ), by simp [f]⟩, (hpow n).symm.trans hn⟩

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
  let S := subfaceSide M cyclicSubgraph_le left
  let hN := restrict_le G S
  let hHN := cyclicSubgraph_le_side M hc hk left
  have hface : ∀ e, SameCycle (restrictMap M cyclicSubgraph_le).facePerm right e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M cyclicSubgraph_le).facePerm e) := by
    intro e he
    exact facePerm_restrict_of_empty_gaps M hN hHN right
      (fun d e hn he => cycle_opposite_gap_empty M hc hch left right hne d e hn he) he
  rw [inducedPlaneMap_onOuterFace_iff]
  constructor
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨e, he, hed⟩ := exists_dart_of_preserved_subface M hN hHN right hface hd
    apply (cycle_outer_iff (restrictMap M cyclicSubgraph_le) hc hk right x.1).1
    refine ⟨e, he, ?_⟩
    rw [← toDart_fst hHN e, hed]
    exact hdx
  · intro hx
    obtain ⟨e, he, hfst⟩ :=
      (cycle_outer_iff (restrictMap M cyclicSubgraph_le) hc hk right x.1).2 hx
    exact ⟨toDart hHN e, sameCycle_of_preserved_subface M hN hHN right hface he, hfst⟩

omit [NeZero k] in
lemma mem_subfaceSide_congr (M : PlaneMap G) {H : SimpleGraph V} (hH : H ≤ G)
    {left right : H.Dart} (h : SameCycle (restrictMap M hH).facePerm left right) (x : V) :
    x ∈ subfaceSide M hH left ↔ x ∈ subfaceSide M hH right := by
  change (_ ∨ _) ↔ (_ ∨ _)
  apply or_congr ?_ (inSubface_congr h x)
  constructor
  · rintro ⟨e, he, hfst⟩
    exact ⟨e, h.symm.trans he, hfst⟩
  · rintro ⟨e, he, hfst⟩
    exact ⟨e, h.trans he, hfst⟩

/-- If an old face meets the cycle, all its vertices project to the same cycle
side. Excursions off the cycle are followed until their last cycle incidence. -/
lemma cycle_original_face_subset_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (outer : G.Dart) {d : G.Dart} {e : (cyclicSubgraph G c).Dart}
    (hdface : SameCycle M.facePerm outer d) (hnext : IsNextH M cyclicSubgraph_le d e) :
    ∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le e := by
  let H := cyclicSubgraph G c
  have hdH : d.fst ∈ subVerts H := (isNextH_fst M cyclicSubgraph_le hnext) ▸ ⟨e.snd, e.adj⟩
  have hpow : ∀ n : ℕ, ((M.facePerm ^ n) d).fst ∈ subVerts H ∨
      ∃ z : G.Dart, SameCycle M.facePerm d z ∧ z.fst ∈ subVerts H ∧
        z.snd ∉ subVerts H ∧ RIn G (subVerts H)ᶜ z.snd ((M.facePerm ^ n) d).fst := by
    intro n
    induction n with
    | zero => exact Or.inl hdH
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      let t := (M.facePerm ^ n) d
      have hfst : (M.facePerm t).fst = t.snd := M.isRotationSystem.fst_apply _
      dsimp only [t] at hfst
      simp only [hfst]
      by_cases ht : t.snd ∈ subVerts H
      · exact Or.inl ht
      · rcases ih with htH | ⟨z, hz, hzH, hzout, hp⟩
        · exact Or.inr ⟨t, ⟨(n : ℤ), by simp [t]⟩, htH, ht, .refl _⟩
        · exact Or.inr ⟨z, hz, hzH, hzout, hp.trans (RIn.single t.adj (hp.mem hzout) ht)⟩
  rintro x ⟨t, ht, htx⟩
  obtain ⟨n, hn⟩ := (hdface.symm.trans ht).exists_nat_pow_eq
  have hx := hpow n
  rw [hn, htx] at hx
  rcases hx with hx | ⟨z, hz, hzH, hzout, hp⟩
  · apply Or.inl
    rwa [cycle_subface_vertices M hc hk, ← cyclicSubgraph_subVerts hc]
  · obtain ⟨f, hf⟩ := exists_isNextH M cyclicSubgraph_le (d := z) hzH
    exact Or.inr ⟨hp.mem hzout, z, f, hzH, hzout, hf,
      sameCycle_restrict_of_same_original_face M cyclicSubgraph_le
        (cyclicSubgraph_connected hc) hz hnext hf, hp⟩

/-- An original face lies on one of the two closed cycle sides. -/
lemma cycle_original_face_one_side (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hconn : G.Preconnected) (outer : G.Dart) :
    (∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0)) ∨
    (∀ x, OnOuterFace M outer x → x ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0)) := by
  classical
  by_cases hmeet : ∃ x, x ∈ Set.range c ∧ OnOuterFace M outer x
  · obtain ⟨x, hx, d, hd, hdx⟩ := hmeet
    have hdH : d.fst ∈ subVerts (cyclicSubgraph G c) := by
      rw [cyclicSubgraph_subVerts hc, hdx]
      exact hx
    obtain ⟨e, he⟩ := exists_isNextH M cyclicSubgraph_le (d := d) hdH
    have hsubset := cycle_original_face_subset_side M hc hk outer hd he
    rcases cycle_two_faces (restrictMap M cyclicSubgraph_le) hc hk e with hf | hf
    · exact Or.inl (fun x hx => (mem_subfaceSide_congr M cyclicSubgraph_le hf x).2 (hsubset x hx))
    · exact Or.inr (fun x hx => (mem_subfaceSide_congr M cyclicSubgraph_le hf x).2 (hsubset x hx))
  · have hout : ∀ x, OnOuterFace M outer x → x ∉ subVerts (cyclicSubgraph G c) := by
      intro x hx hC
      exact hmeet ⟨x, by rwa [← cyclicSubgraph_subVerts hc], hx⟩
    have hboundary := onOuterFace_connSet M outer
    have hroot := onOuterFace_self M outer
    have hp : ∀ x, OnOuterFace M outer x →
        RIn G (subVerts (cyclicSubgraph G c))ᶜ outer.fst x :=
      fun x hx => (hboundary.2 _ hroot _ hx).mono_set (fun z hz => hout z hz)
    have hcover : outer.fst ∈ subfaceSide M cyclicSubgraph_le (cycleForward hc 0) ∨
        outer.fst ∈ subfaceSide M cyclicSubgraph_le (cycleBackward hc 0) := by
      have h := Set.mem_univ outer.fst
      rwa [← cycle_sides_cover M hc hk hconn] at h
    have to_region {o : (cyclicSubgraph G c).Dart}
        (hs : outer.fst ∈ subfaceSide M cyclicSubgraph_le o) :
        inSubface M cyclicSubgraph_le o outer.fst := by
      rcases hs with hs | hs
      · exact (hout _ hroot (subfaceVertices_subset M cyclicSubgraph_le o hs)).elim
      · exact hs
    rcases hcover with hs | hs
    · exact Or.inl (fun x hx => Or.inr (inSubface_of_rIn (to_region hs) (hp x hx)))
    · exact Or.inr (fun x hx => Or.inr (inSubface_of_rIn (to_region hs) (hp x hx)))

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
  let left := cycleForward hc 0
  let right := cycleBackward hc 0
  let S := subfaceSide M cyclicSubgraph_le left
  let T := subfaceSide M cyclicSubgraph_le right
  have hne := cycle_faces_distinct (restrictMap M cyclicSubgraph_le) hc hk
  refine ⟨S, T, cycle_sides_cover M hc hk hconn, cycle_sides_inter M hc hk,
    fun {_ _} h => cycle_sides_no_crossing M hc hk hconn h,
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le left),
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le right),
    ⟨induceDartEquiv G S (toDart (cyclicSubgraph_le_side M hc hk left) right), ?_⟩,
    ⟨induceDartEquiv G T (toDart (cyclicSubgraph_le_side M hc hk right) left), ?_⟩⟩
  · exact cycle_side_outer_iff M hc hk hch left right hne
  · exact cycle_side_outer_iff M hc hk hch right left (fun h => hne h.symm)

end Thomassen
