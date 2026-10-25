/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Grotzsch.Regions
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import LeanPool.K5MinorFreeChoosability.Planar.Colouring

/-! Independent contracts for induced embeddings and the induction measure.
Only the shared registered geometry is imported; no new Thomassen proof module. -/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

def OnOuterFace (M : PlaneMap G) (outer : G.Dart) (x : V) : Prop :=
  ∃ e : G.Dart, Equiv.Perm.SameCycle M.facePerm outer e ∧ e.fst = x

def induceDartEquiv (G : SimpleGraph V) (S : Set V) :
    (restrict G S).Dart ≃ (G.induce S).Dart where
  toFun d := ⟨(⟨d.fst, d.adj.2.1⟩, ⟨d.snd, d.adj.2.2⟩), d.adj.1⟩
  invFun d := ⟨(d.fst.1, d.snd.1), d.adj, d.fst.2, d.snd.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

@[simp] lemma induceDartEquiv_symm (S : Set V) (d : (restrict G S).Dart) :
    induceDartEquiv G S d.symm = (induceDartEquiv G S d).symm := rfl

lemma induceDartEquiv_dartSymm (G : SimpleGraph V) (S : Set V) :
    (induceDartEquiv G S).permCongr (dartSymm (restrict G S)) = dartSymm (G.induce S) := by
  apply Equiv.ext
  intro d
  change induceDartEquiv G S (((induceDartEquiv G S).symm d).symm) = d.symm
  rw [induceDartEquiv_symm, Equiv.apply_symm_apply]

noncomputable def subtypePlaneMap (S : Set V) (M : PlaneMap (restrict G S)) :
    PlaneMap (G.induce S) where
  rot := (induceDartEquiv G S).permCongr M.rot
  isRotationSystem := {
    fst_apply := by
      intro d
      apply Subtype.ext
      change (M.rot ((induceDartEquiv G S).symm d)).fst = d.fst.1
      rw [M.isRotationSystem.fst_apply]
      rfl
    sameCycle := by
      intro d e hde
      have hf : ((induceDartEquiv G S).symm d).fst =
          ((induceDartEquiv G S).symm e).fst := congrArg Subtype.val hde
      have h := (sameCycle_permCongr_iff (induceDartEquiv G S) M.rot _ _).1
        (M.isRotationSystem.sameCycle _ _ hf)
      simpa using h }
  eulerDefect_eq_zero := by
    rw [← induceDartEquiv_dartSymm G S, eulerDefect_permCongr]
    exact M.eulerDefect_eq_zero

lemma subtypePlaneMap_facePerm (S : Set V) (M : PlaneMap (restrict G S)) :
    (subtypePlaneMap S M).facePerm = (induceDartEquiv G S).permCongr M.facePerm := by
  sorry

lemma subtypePlaneMap_sameCycle_iff (S : Set V) (M : PlaneMap (restrict G S))
    (d e : (restrict G S).Dart) :
    SameCycle (subtypePlaneMap S M).facePerm (induceDartEquiv G S d)
      (induceDartEquiv G S e) ↔ SameCycle M.facePerm d e := by
  sorry

lemma subtypePlaneMap_onOuterFace_iff (S : Set V) (M : PlaneMap (restrict G S))
    (outer : (restrict G S).Dart) (x : S) :
    OnOuterFace (subtypePlaneMap S M) (induceDartEquiv G S outer) x ↔
      OnOuterFace M outer x.1 := by
  sorry

variable [Fintype V]

omit [Fintype V] in
lemma five_le_egirth_induce (S : Set V) (hg : 5 ≤ G.egirth) :
    5 ≤ (G.induce S).egirth := by
  sorry

noncomputable def inducedPlaneMap (M : PlaneMap G) (S : Set V) : PlaneMap (G.induce S) :=
  subtypePlaneMap S (restrictMap M (restrict_le G S))

lemma card_induced_vertices_lt (S : Set V) {x : V} (hx : x ∉ S) :
    Nat.card S < Nat.card V := by
  sorry

lemma restrictMap_facePerm_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (d : (restrict G S).Dart) :
    toDart (restrict_le G S) ((restrictMap M (restrict_le G S)).facePerm d) =
      M.facePerm (toDart (restrict_le G S) d) := by
  sorry

lemma restrictMap_sameCycle_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (d e : (restrict G S).Dart) :
    SameCycle (restrictMap M (restrict_le G S)).facePerm d e ↔
      SameCycle M.facePerm (toDart (restrict_le G S) d) (toDart (restrict_le G S) e) := by
  sorry

lemma inducedPlaneMap_onOuterFace_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (outer : (restrict G S).Dart)
    (x : S) :
    OnOuterFace (inducedPlaneMap M S) (induceDartEquiv G S outer) x ↔
      OnOuterFace M (toDart (restrict_le G S) outer) x.1 := by
  sorry

omit [Fintype V] in
lemma col_restrict_iff_listColourable_induce {C : Type v} (S : Finset V)
    (L : V → Finset C) (fallback : V → C) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ↔
      ListColourable (G.induce (↑S : Set V)) (fun x => L x.1) := by
  sorry

end Thomassen
