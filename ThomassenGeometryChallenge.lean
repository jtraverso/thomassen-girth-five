/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Grotzsch.Regions

/-!
Independent contracts for geometric separation, over the shared, registered
plane-map infrastructure. This file imports no new Thomassen proof module.
It specifies no list-colouring extension theorem.
-/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

def subfaceVertices (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) : Set V :=
  {w | ∃ e : H.Dart, SameCycle (restrictMap M hH).facePerm o e ∧ e.fst = w}

def inSubface (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) (w : V) : Prop :=
  w ∉ subVerts H ∧ ∃ (d : G.Dart) (e : H.Dart),
    d.fst ∈ subVerts H ∧ d.snd ∉ subVerts H ∧ IsNextH M hH d e ∧
    SameCycle (restrictMap M hH).facePerm o e ∧ RIn G (subVerts H)ᶜ d.snd w

def subfaceSide (M : PlaneMap G) (hH : H ≤ G) (o : H.Dart) : Set V :=
  subfaceVertices M hH o ∪ {w | inSubface M hH o w}

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
  sorry

lemma two_face_sides_inter (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (left right : H.Dart) (hne : ¬ SameCycle (restrictMap M hH).facePerm left right) :
    subfaceSide M hH left ∩ subfaceSide M hH right =
      subfaceVertices M hH left ∩ subfaceVertices M hH right := by
  sorry

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
  sorry

lemma facePerm_restrict_of_empty_gaps (M : PlaneMap G) {N : SimpleGraph V}
    (hN : N ≤ G) (hHN : H ≤ N) (o : H.Dart)
    (hgap : ∀ (d : N.Dart) (e : H.Dart),
      IsNextH M (hHN.trans hN) (toDart hN d) e →
      SameCycle (restrictMap M (hHN.trans hN)).facePerm o e →
      H.Adj d.fst d.snd)
    {e : H.Dart} (he : SameCycle (restrictMap M (hHN.trans hN)).facePerm o e) :
    (restrictMap M hN).facePerm (toDart hHN e) =
      toDart hHN ((restrictMap M (hHN.trans hN)).facePerm e) := by
  sorry

lemma sameCycle_of_preserved_subface (M : PlaneMap G) {N : SimpleGraph V}
    (hN : N ≤ G) (hHN : H ≤ N) (o : H.Dart)
    (hface : ∀ e, SameCycle (restrictMap M (hHN.trans hN)).facePerm o e →
      (restrictMap M hN).facePerm (toDart hHN e) =
        toDart hHN ((restrictMap M (hHN.trans hN)).facePerm e))
    {e : H.Dart} (he : SameCycle (restrictMap M (hHN.trans hN)).facePerm o e) :
    SameCycle (restrictMap M hN).facePerm (toDart hHN o) (toDart hHN e) := by
  sorry

end Thomassen

namespace Thomassen
variable {V : Type u} [Finite V] {G : SimpleGraph V}

lemma eq_of_same_face_of_fst (M : PlaneMap G) {d e : G.Dart}
    (hface : SameCycle M.facePerm d e) (hfst : d.fst = e.fst)
    (hconn : ∀ a b, a ≠ d.fst → b ≠ d.fst → RIn G ({d.fst} : Set V)ᶜ a b) :
    d = e := by
  sorry

lemma face_fst_injective_of_delete_preconnected (M : PlaneMap G)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) (outer : G.Dart) :
    Function.Injective (fun e : FaceApex.F M outer => e.1.fst) := by
  sorry

end Thomassen
