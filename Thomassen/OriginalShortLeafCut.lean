/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalMinimal

/-! The colour-transfer operation in original reductions (4) and (5). -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Colour a strict cut whose separator consists of a central edge and
released vertices adjacent to that edge. The actual new short set on the
second side may include formerly three-list separator vertices. Give each released short vertex its old
colour and its parent's colour as a temporary two-list. The central prescribed
edge forces every released vertex back to its original colour. All temporary
lists and all restoration constraints are checked here. This includes the
original two-path and three-path cuts; it is not an assumed extension lemma. -/
theorem extends_of_released_leaf_edge_cut (I : OriginalBoundaryInstance G C)
    (S T R : Set V) (v w : V) (hvw : G.Adj v w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = R ∪ {v,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (hRaway : ∀ x ∈ R, x ≠ v ∧ x ≠ w)
    (hattach : ∀ x ∈ R, ∃ y, (y = v ∨ y = w) ∧ G.Adj x y)
    (N : PlaneMap (G.induce T)) (outer : (G.induce T).Dart)
    (A : Set T) (hAshape : OriginalShortSet (G.induce T) A)
    (hAold : ∀ x : T, x.1 ∈ I.short → x ∈ A)
    (hAR : ∀ x : T, x.1 ∈ R → x ∈ A)
    (hAface : ∀ x ∈ A, OnOuterFace N outer x)
    (hvface : ∀ hvT : v ∈ T, OnOuterFace N outer ⟨v,hvT⟩)
    (hwface : ∀ hwT : w ∈ T, OnOuterFace N outer ⟨w,hwT⟩)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  have hSep : ∀ x ∈ R ∪ ({v,w} : Set V), x ∈ S ∧ x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h
  have hvST := hSep v (Or.inr (Or.inl rfl))
  have hwST := hSep w (Or.inr (Or.inr rfl))
  have hvR : v ∉ R := fun h => (hRaway v h).1 rfl
  have hwR : w ∉ R := fun h => (hRaway w h).2 rfl
  have hAdjS : (G.induce S).Adj ⟨I.a,haS⟩ ⟨I.b,hbS⟩ := I.edge
  let : Nontrivial S := hAdjS.nontrivial
  let JS := I.induceWithEdge S hSc I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) JS hSsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := hcS
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x,hx⟩ else I.ta
  have hfS : ∀ x : S, f x.1 = cS x := fun x => dite_eq_left x.2
  let parent : V → V := fun x => if hx : x ∈ R then (hattach x hx).choose else v
  have hp : ∀ x ∈ R, (parent x = v ∨ parent x = w) ∧ G.Adj x (parent x) := by
    intro x hx
    simpa only [parent,dite_eq_left hx] using (hattach x hx).choose_spec
  have hpST : ∀ x ∈ R, parent x ∈ S ∧ parent x ∈ T := by
    intro x hx
    exact (hp x hx).1.elim (fun h => h ▸ hvST) (fun h => h ▸ hwST)
  have hfp : ∀ x ∈ R, f x ≠ f (parent x) := by
    intro x hx
    rw [hfS ⟨x,(hSep x (Or.inl hx)).1⟩,hfS ⟨parent x,(hpST x hx).1⟩]
    exact cS.valid (show (G.induce S).Adj ⟨x,(hSep x (Or.inl hx)).1⟩
      ⟨parent x,(hpST x hx).1⟩ from (hp x hx).2)
  let L' : T → Finset C := fun x => if x.1 ∈ R then {f x.1,f (parent x.1)} else I.lists x.1
  let JT : OriginalBoundaryInstance (G.induce T) C := {
    embedding := N
    outer := outer
    girth := five_le_egirth_induce T I.girth
    short := A
    on_outer := hAface
    short_shape := hAshape
    lists := L'
    list_two := by
      intro x
      by_cases hx : x.1 ∈ R
      · simp only [L',ite_eq_left hx,Finset.card_pair (hfp x.1 hx)]
        exact le_rfl
      · simpa only [L',ite_eq_right hx] using I.list_two x.1
    list_three := by
      intro x hx
      have hxR : x.1 ∉ R := fun h => hx (hAR x h)
      simpa only [L',ite_eq_right hxR] using I.list_three x.1 (fun h => hx (hAold x h))
    a := ⟨v,hvST.2⟩
    b := ⟨w,hwST.2⟩
    edge := hvw
    a_outer := hvface _
    b_outer := hwface _
    ta := f v
    tb := f w
    ta_mem := by
      simp only [L',ite_eq_right hvR]
      rw [hfS ⟨v,hvST.1⟩]; exact hS _
    tb_mem := by
      simp only [L',ite_eq_right hwR]
      rw [hfS ⟨w,hwST.1⟩]; exact hS _
    colours_ne := by
      rw [hfS ⟨v,hvST.1⟩,hfS ⟨w,hwST.1⟩]
      exact cS.valid (show (G.induce S).Adj ⟨v,hvST.1⟩ ⟨w,hwST.1⟩ from hvw) }
  obtain ⟨cT,hcT,hcv,hcw⟩ := hsmall T (G.induce T) JT hTsmall
  change ∀ x : T, cT x ∈ L' x at hcT
  have hTp : ∀ (x : V) (hx : x ∈ R), cT ⟨parent x,(hpST x hx).2⟩ = f (parent x) := by
    intro x hx
    rcases (hp x hx).1 with he | he
    · simpa only [he] using hcv
    · simpa only [he] using hcw
  have hTR : ∀ x : T, x.1 ∈ R → cT x = f x.1 := by
    intro x hx
    have hc := hcT x
    change cT x ∈ L' x at hc
    simp only [L',ite_eq_left hx,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · exact hc
    · exact (cT.valid (show (G.induce T).Adj x ⟨parent x.1,(hpST x.1 hx).2⟩ from (hp x.1 hx).2)
        (hc.trans (hTp x.1 hx).symm)).elim
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    intro x
    by_cases hx : x.1 ∈ R
    · rw [hTR x hx,hfS ⟨x.1,(hSep x.1 (Or.inl hx)).1⟩]
      exact hS _
    · simpa only [L',ite_eq_right hx] using hcT x
  apply I.extends_of_glued_colourings S T hcover hedges haS hbS cS cT hS hT ?_ hca hcb
  intro x hx hy
  rw [← hfS ⟨x,hx⟩]
  have hxSep : x ∈ R ∪ ({v,w} : Set V) := hinter ▸ (show x ∈ S ∩ T from ⟨hx,hy⟩)
  rcases hxSep with hxR | rfl | hxw
  · exact (hTR ⟨x,hy⟩ hxR).symm
  · exact hcv.symm
  · have he : x = w := Set.mem_singleton_iff.1 hxw
    subst x
    exact hcw.symm

/-- Colour a strict cut whose separator consists of a central edge and old
short vertices adjacent to that edge. Give each released short vertex its old
colour and its parent's colour as a temporary two-list. The central prescribed
edge forces every released vertex back to its original colour. All temporary
lists and all restoration constraints are checked here. This includes the
original two-path and three-path cuts; it is not an assumed extension lemma. -/
theorem extends_of_short_leaf_edge_cut (I : OriginalBoundaryInstance G C)
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
  exact I.extends_of_released_leaf_edge_cut S T R v w hvw hcover hinter hedges hSc haS hbS
    hRaway hattach N outer {x : T | x.1 ∈ I.short} (I.short_shape.induce I.short T)
    (fun _ hx => hx) (fun _ hx => hR hx) hAface hvface hwface hSsmall hTsmall hsmall

end Thomassen.OriginalBoundaryInstance
