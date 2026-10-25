/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Grotzsch.Regions

/-!
# Separating a plane map using the faces of a connected subgraph

The region and chord theorems of the registered Grötzsch development assign
components and chords to faces. This module constructs vertex sides, proves
coverage and absence of crossing edges, and identifies their intersection.
The hypotheses concern actual face orbits and rotations, never colourability.
-/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

/-- Vertices visited by a specified face of the induced map on `H`. -/
def subfaceVertices (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) : Set V :=
  {w | ∃ e : H.Dart, SameCycle (restrictMap M hH).facePerm o e ∧ e.fst = w}

/-- A component off `H` is in the face through `o` if it attaches in one of its gaps. -/
def inSubface (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) (w : V) : Prop :=
  w ∉ subVerts H ∧ ∃ (d : G.Dart) (e : H.Dart),
    d.fst ∈ subVerts H ∧ d.snd ∉ subVerts H ∧ IsNextH M hH d e ∧
    SameCycle (restrictMap M hH).facePerm o e ∧ RIn G (subVerts H)ᶜ d.snd w

/-- The closed side consisting of one face boundary and all its attached components. -/
def subfaceSide (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) : Set V :=
  subfaceVertices M hH o ∪ {w | inSubface M hH o w}

lemma subfaceVertices_subset (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) :
    subfaceVertices M hH o ⊆ subVerts H := by
  rintro w ⟨e, _, rfl⟩
  exact ⟨e.snd, e.adj⟩

lemma inSubface_of_rIn {M : PlaneMap G} {hH : H ≤ G} {o : H.Dart} {w z : V}
    (hw : inSubface M hH o w) (hr : RIn G (subVerts H)ᶜ w z) :
    inSubface M hH o z := by
  obtain ⟨hw, d, e, hd, hd', hn, he, hpath⟩ := hw
  exact ⟨hr.mem hw, d, e, hd, hd', hn, he, hpath.trans hr⟩

lemma inSubface_congr {M : PlaneMap G} {hH : H ≤ G} {o p : H.Dart}
    (hop : SameCycle (restrictMap M hH).facePerm o p) (w : V) :
    inSubface M hH o w ↔ inSubface M hH p w := by
  constructor
  · rintro ⟨hw, d, e, hd, hd', hn, he, hp⟩
    exact ⟨hw, d, e, hd, hd', hn, hop.symm.trans he, hp⟩
  · rintro ⟨hw, d, e, hd, hd', hn, he, hp⟩
    exact ⟨hw, d, e, hd, hd', hn, hop.trans he, hp⟩

lemma sameCycle_of_inSubface (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {o p : H.Dart} {w : V} (ho : inSubface M hH o w) (hp : inSubface M hH p w) :
    SameCycle (restrictMap M hH).facePerm o p := by
  obtain ⟨_, d, e, hd, hd', hn, he, hpath⟩ := ho
  obtain ⟨_, d', e', hd1, hd1', hn1, he1, hpath1⟩ := hp
  have hfaces := sameCycle_of_rIn M hH hconn hd hd1 hd' hd1'
    (hpath.trans hpath1.symm) hn hn1
  exact (he.trans hfaces).trans he1.symm

lemma exists_inSubface (M : PlaneMap G) (hH : H ≤ G) {w s : V}
    (hw : w ∉ subVerts H) (hs : s ∈ subVerts H) (hws : RIn G Set.univ w s) :
    ∃ o : H.Dart, inSubface M hH o w := by
  obtain ⟨p, q, hwp, _, hp, _, hq, hpq⟩ :=
    hws.exit (P := (subVerts H)ᶜ) hw (fun h => h hs)
  have hqH : q ∈ subVerts H := by simpa using hq
  let d : G.Dart := ⟨(q, p), hpq.symm⟩
  obtain ⟨e, he⟩ := exists_isNextH M hH (d := d) hqH
  exact ⟨e, hw, d, e, hqH, hp, he, SameCycle.refl _ _,
    (hwp.mono_set (fun _ hx => hx.2)).symm⟩

/-- A face preserved from the whole map has no attached outside component. -/
lemma not_inSubface_of_preserved (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart)
    (hface : ∀ e, SameCycle (restrictMap M hH).facePerm o e →
      M.facePerm (toDart hH e) = toDart hH ((restrictMap M hH).facePerm e))
    (w : V) : ¬ inSubface M hH o w := by
  rintro ⟨_, d, e, _, hd', hn, he, _⟩
  have hde := eq_of_isNextH_of_face M hH hface he hn
  apply hd'
  rw [hde]
  exact ⟨e.fst, e.adj.symm⟩

/-- Every edge touching an attached component meets its face boundary. -/
lemma subfaceVertices_of_adj_inSubface (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {o : H.Dart} {x w : V} (hx : x ∈ subVerts H) (hw : inSubface M hH o w)
    (hxw : G.Adj x w) : x ∈ subfaceVertices M hH o := by
  obtain ⟨hw, d, e, hd, hd', hn, he, hpath⟩ := hw
  let d' : G.Dart := ⟨(x, w), hxw⟩
  obtain ⟨e', he'⟩ := exists_isNextH M hH (d := d') hx
  have hfaces := sameCycle_of_rIn M hH hconn hd hx hd' hw hpath hn he'
  exact ⟨e', he.trans hfaces, isNextH_fst M hH he'⟩

/-- Both ends of a dart on a face belong to that face's vertex set. -/
lemma endpoints_in_subfaceVertices (M : PlaneMap G) (hH : H ≤ G) {o e : H.Dart}
    (he : SameCycle (restrictMap M hH).facePerm o e) :
    e.fst ∈ subfaceVertices M hH o ∧ e.snd ∈ subfaceVertices M hH o := by
  refine ⟨⟨e, he, rfl⟩, ⟨(restrictMap M hH).facePerm e, ?_, ?_⟩⟩
  · exact he.trans ⟨1, by simp⟩
  · change ((subRot M hH) e.symm).fst = e.snd
    exact (isRotationSystem_subRot M hH).fst_apply _

lemma subfaceSide_of_H_edge (M : PlaneMap G) (hH : H ≤ G) (left right : H.Dart)
    (hedges : ∀ e : H.Dart,
      (SameCycle (restrictMap M hH).facePerm left e ∨
       SameCycle (restrictMap M hH).facePerm left e.symm) ∨
      (SameCycle (restrictMap M hH).facePerm right e ∨
       SameCycle (restrictMap M hH).facePerm right e.symm))
    {x y : V} (hxy : H.Adj x y) :
    (x ∈ subfaceSide M hH left ∧ y ∈ subfaceSide M hH left) ∨
    (x ∈ subfaceSide M hH right ∧ y ∈ subfaceSide M hH right) := by
  rcases hedges ⟨(x, y), hxy⟩ with (he | he) | (he | he)
  · have h := endpoints_in_subfaceVertices M hH he
    exact Or.inl ⟨Or.inl h.1, Or.inl h.2⟩
  · have h := endpoints_in_subfaceVertices M hH he
    exact Or.inl ⟨Or.inl h.2, Or.inl h.1⟩
  · have h := endpoints_in_subfaceVertices M hH he
    exact Or.inr ⟨Or.inl h.1, Or.inl h.2⟩
  · have h := endpoints_in_subfaceVertices M hH he
    exact Or.inr ⟨Or.inl h.2, Or.inl h.1⟩

/-- A chord of `H` lies on one of the two permitted sides. The third face is
preserved from `G`, so the chord cannot occupy any of its gaps. -/
lemma subfaceSide_of_chord (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer left right : H.Dart)
    (hfaces : ∀ e : H.Dart,
      SameCycle (restrictMap M hH).facePerm outer e ∨
      SameCycle (restrictMap M hH).facePerm left e ∨
      SameCycle (restrictMap M hH).facePerm right e)
    (houter : ∀ e, SameCycle (restrictMap M hH).facePerm outer e →
      M.facePerm (toDart hH e) = toDart hH ((restrictMap M hH).facePerm e))
    {x y : V} (hx : x ∈ subVerts H) (hy : y ∈ subVerts H)
    (hxy : G.Adj x y) (hnot : ¬ H.Adj x y) :
    (x ∈ subfaceSide M hH left ∧ y ∈ subfaceSide M hH left) ∨
    (x ∈ subfaceSide M hH right ∧ y ∈ subfaceSide M hH right) := by
  let d : G.Dart := ⟨(x, y), hxy⟩
  obtain ⟨e, he⟩ := exists_isNextH M hH (d := d) hx
  obtain ⟨e', he'⟩ := exists_isNextH M hH (d := d.symm) hy
  have hs := sameCycle_of_chord M hH hconn (d := d) hx hy hnot he he'
  rcases hfaces e with ho | hl | hr
  · have hd := eq_of_isNextH_of_face M hH houter ho he
    exact False.elim (hnot (by change InH H d; rw [hd]; exact e.adj))
  · exact Or.inl ⟨Or.inl ⟨e, hl, isNextH_fst M hH he⟩,
      Or.inl ⟨e', hl.trans hs, isNextH_fst M hH he'⟩⟩
  · exact Or.inr ⟨Or.inl ⟨e, hr, isNextH_fst M hH he⟩,
      Or.inl ⟨e', hr.trans hs, isNextH_fst M hH he'⟩⟩

lemma two_face_sides_cover (M : PlaneMap G) (hH : H ≤ G) (outer left right : H.Dart)
    (hconnG : ∀ a b, RIn G Set.univ a b)
    (hfaces : ∀ e : H.Dart,
      SameCycle (restrictMap M hH).facePerm outer e ∨
      SameCycle (restrictMap M hH).facePerm left e ∨
      SameCycle (restrictMap M hH).facePerm right e)
    (houter : ∀ e, SameCycle (restrictMap M hH).facePerm outer e →
      M.facePerm (toDart hH e) = toDart hH ((restrictMap M hH).facePerm e))
    (hedges : ∀ e : H.Dart,
      (SameCycle (restrictMap M hH).facePerm left e ∨
       SameCycle (restrictMap M hH).facePerm left e.symm) ∨
      (SameCycle (restrictMap M hH).facePerm right e ∨
       SameCycle (restrictMap M hH).facePerm right e.symm)) :
    subfaceSide M hH left ∪ subfaceSide M hH right = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  by_cases hw : w ∈ subVerts H
  · obtain ⟨z, hwz⟩ := hw
    rcases subfaceSide_of_H_edge M hH left right hedges hwz with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · obtain ⟨o, ho⟩ := exists_inSubface M hH hw ⟨left.snd, left.adj⟩
      (hconnG w left.fst)
    rcases hfaces o with hf | hf | hf
    · exact False.elim (not_inSubface_of_preserved M hH outer houter w
        ((inSubface_congr hf w).2 ho))
    · exact Or.inl (Or.inr ((inSubface_congr hf w).2 ho))
    · exact Or.inr (Or.inr ((inSubface_congr hf w).2 ho))

/-- The sides meet precisely in their common boundary vertices, not in their interiors. -/
lemma two_face_sides_inter (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (left right : H.Dart) (hne : ¬ SameCycle (restrictMap M hH).facePerm left right) :
    subfaceSide M hH left ∩ subfaceSide M hH right =
      subfaceVertices M hH left ∩ subfaceVertices M hH right := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hl | hl, hr | hr⟩
    · exact ⟨hl, hr⟩
    · exact False.elim (hr.1 (subfaceVertices_subset M hH left hl))
    · exact False.elim (hl.1 (subfaceVertices_subset M hH right hr))
    · exact False.elim (hne (sameCycle_of_inSubface M hH hconn hl hr))
  · rintro ⟨hl, hr⟩
    exact ⟨Or.inl hl, Or.inl hr⟩

lemma two_face_sides_no_crossing (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer left right : H.Dart)
    (hfaces : ∀ e : H.Dart,
      SameCycle (restrictMap M hH).facePerm outer e ∨
      SameCycle (restrictMap M hH).facePerm left e ∨
      SameCycle (restrictMap M hH).facePerm right e)
    (houter : ∀ e, SameCycle (restrictMap M hH).facePerm outer e →
      M.facePerm (toDart hH e) = toDart hH ((restrictMap M hH).facePerm e))
    (hedges : ∀ e : H.Dart,
      (SameCycle (restrictMap M hH).facePerm left e ∨
       SameCycle (restrictMap M hH).facePerm left e.symm) ∨
      (SameCycle (restrictMap M hH).facePerm right e ∨
       SameCycle (restrictMap M hH).facePerm right e.symm))
    (hcover : subfaceSide M hH left ∪ subfaceSide M hH right = Set.univ)
    {x y : V} (hxy : G.Adj x y) :
    (x ∈ subfaceSide M hH left ∧ y ∈ subfaceSide M hH left) ∨
    (x ∈ subfaceSide M hH right ∧ y ∈ subfaceSide M hH right) := by
  have side (w : V) : w ∈ subfaceSide M hH left ∨ w ∈ subfaceSide M hH right := by
    have hw : w ∈ Set.univ := Set.mem_univ w
    rw [← hcover] at hw
    exact hw
  have outside {o : H.Dart} {w : V} (hw : w ∉ subVerts H)
      (hs : w ∈ subfaceSide M hH o) : inSubface M hH o w := by
    rcases hs with h | h
    · exact False.elim (hw (subfaceVertices_subset M hH o h))
    · exact h
  by_cases hx : x ∈ subVerts H
  · by_cases hy : y ∈ subVerts H
    · by_cases he : H.Adj x y
      · exact subfaceSide_of_H_edge M hH left right hedges he
      · exact subfaceSide_of_chord M hH hconn outer left right hfaces houter hx hy hxy he
    · rcases side y with hs | hs
      · exact Or.inl ⟨Or.inl (subfaceVertices_of_adj_inSubface M hH hconn hx
          (outside hy hs) hxy), hs⟩
      · exact Or.inr ⟨Or.inl (subfaceVertices_of_adj_inSubface M hH hconn hx
          (outside hy hs) hxy), hs⟩
  · by_cases hy : y ∈ subVerts H
    · rcases side x with hs | hs
      · exact Or.inl ⟨hs, Or.inl (subfaceVertices_of_adj_inSubface M hH hconn hy
          (outside hx hs) hxy.symm)⟩
      · exact Or.inr ⟨hs, Or.inl (subfaceVertices_of_adj_inSubface M hH hconn hy
          (outside hx hs) hxy.symm)⟩
    · rcases side x with hs | hs
      · exact Or.inl ⟨hs, Or.inr (inSubface_of_rIn (outside hx hs)
          (RIn.single hxy hx hy))⟩
      · exact Or.inr ⟨hs, Or.inr (inSubface_of_rIn (outside hx hs)
          (RIn.single hxy hx hy))⟩

/-- If a kept subgraph has no additional dart in the gaps of a face, deleting
the other edges makes that face an actual face of the kept map. -/
lemma facePerm_restrict_of_empty_gaps (M : PlaneMap G) {N : SimpleGraph V}
    (hN : N ≤ G) (hHN : H ≤ N) (o : H.Dart)
    (hgap : ∀ (d : N.Dart) (e : H.Dart),
      IsNextH M (hHN.trans hN) (toDart hN d) e →
      SameCycle (restrictMap M (hHN.trans hN)).facePerm o e →
      H.Adj d.fst d.snd)
    {e : H.Dart} (he : SameCycle (restrictMap M (hHN.trans hN)).facePerm o e) :
    (restrictMap M hN).facePerm (toDart hHN e) =
      toDart hHN ((restrictMap M (hHN.trans hN)).facePerm e) := by
  let n := (restrictMap M hN).facePerm (toDart hHN e)
  have hn : IsNextH M hN (M.rot (toDart (hHN.trans hN) e.symm)) n :=
    isNextH_rot_subRot M hN (toDart hHN e.symm)
  have hh := isNextH_rot_subRot M (hHN.trans hN) e.symm
  have hnext := isNextH_of_first M (hHN.trans hN) hN hHN hn hh
  have he' : SameCycle (restrictMap M (hHN.trans hN)).facePerm o
      ((restrictMap M (hHN.trans hN)).facePerm e) := he.trans ⟨1, by simp⟩
  let e' : H.Dart := ⟨n.toProd, hgap n _ hnext he'⟩
  have hself : IsNextH M (hHN.trans hN) (toDart hN n) e' :=
    isNextH_self M (hHN.trans hN) (d := toDart hN n) e'.adj
  have heq := isNextH_unique M (hHN.trans hN) hself hnext
  change n = toDart hHN ((subRot M (hHN.trans hN)) e.symm)
  rw [← heq]
  rfl

/-- Face-orbit transport along a subgraph inclusion when the face permutation is preserved. -/
lemma sameCycle_of_preserved_subface (M : PlaneMap G) {N : SimpleGraph V}
    (hN : N ≤ G) (hHN : H ≤ N) (o : H.Dart)
    (hface : ∀ e, SameCycle (restrictMap M (hHN.trans hN)).facePerm o e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M (hHN.trans hN)).facePerm e))
    {e : H.Dart} (he : SameCycle (restrictMap M (hHN.trans hN)).facePerm o e) :
    SameCycle (restrictMap M hN).facePerm (toDart hHN o) (toDart hHN e) := by
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
  obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, hpow, hn]⟩

end Thomassen
