/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalExceptionalComponents
public import Thomassen.ShortRingGluing

/-! The original 1995 extension invariant, retaining its exceptional edge.
Unlike BoundaryInstance, this state permits one unprescribed short-list edge.
No colourability or extension premise is a field of this structure. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The original independent-set or distinguished-single-edge condition. -/
def OriginalShortSet (G : SimpleGraph V) (A : Set V) : Prop :=
  (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) ∨
    ∃ x y, x ∈ A ∧ y ∈ A ∧ G.Adj x y ∧
      (∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
        (r = x ∧ s = y) ∨ (r = y ∧ s = x)) ∧
      (∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)

/-- The short-set condition survives every actual induced restriction.
If either exceptional endpoint is omitted, the surviving set is independent. -/
theorem OriginalShortSet.induce (A : Set V) (hA : OriginalShortSet G A) (S : Set V) :
    OriginalShortSet (G.induce S) {x : S | x.1 ∈ A} := by
  rcases hA with hA | ⟨x,y,hx,hy,hxy,hedge,hNo⟩
  · exact Or.inl (fun r hr s hs hrs => hA r.1 hr s.1 hs hrs)
  · by_cases hxyS : x ∈ S ∧ y ∈ S
    · refine Or.inr ⟨⟨x,hxyS.1⟩,⟨y,hxyS.2⟩,hx,hy,hxy,?_,?_⟩
      · intro r hr s hs hrs
        rcases hedge r.1 hr s.1 hs hrs with h | h
        · exact Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩
        · exact Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩
      · intro z hz p hp hlen
        exact hNo z.1 hz (p.map (Embedding.induce S).toHom)
          (hp.map Subtype.val_injective) ((Walk.length_map _ p).trans hlen)
    · left
      intro r hr s hs hrs
      rcases hedge r.1 hr s.1 hs hrs with h | h
      · exact hxyS ⟨h.1 ▸ r.2,h.2 ▸ s.2⟩
      · exact hxyS ⟨h.2 ▸ s.2,h.1 ▸ r.2⟩

/-- Exact selected-face form of the original Theorem 2.1 input. The shape
condition is combinatorial, and none of the fields assumes an extension. -/
structure OriginalBoundaryInstance (G : SimpleGraph V) (C : Type v) where
  embedding : PlaneMap G
  outer : G.Dart
  girth : 5 ≤ G.egirth
  short : Set V
  on_outer : ∀ x ∈ short, OnOuterFace embedding outer x
  short_shape : OriginalShortSet G short
  lists : V → Finset C
  list_two : ∀ x, 2 ≤ (lists x).card
  list_three : ∀ x, x ∉ short → 3 ≤ (lists x).card
  a : V
  b : V
  edge : G.Adj a b
  a_outer : OnOuterFace embedding outer a
  b_outer : OnOuterFace embedding outer b
  ta : C
  tb : C
  ta_mem : ta ∈ lists a
  tb_mem : tb ∈ lists b
  colours_ne : ta ≠ tb

namespace OriginalBoundaryInstance

/-- The requested output, separated from the input invariant. -/
def Extends (I : OriginalBoundaryInstance G C) : Prop :=
  ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ c I.a = I.ta ∧ c I.b = I.tb

variable [Finite V]

/-- The complete independent-set branch is an available proved dependency. -/
theorem extends_of_independent (I : OriginalBoundaryInstance G C)
    (hA : ∀ x ∈ I.short, ∀ y ∈ I.short, ¬ G.Adj x y) : I.Extends :=
  original_theorem_2_1_independent I.embedding I.outer I.girth I.short I.on_outer hA
    I.lists I.list_two I.list_three I.a I.b I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne

/-- Lists in every free original instance are unconditionally colourable.
This does not assert that the original fixed colours extend. -/
theorem colourable (I : OriginalBoundaryInstance G C) : ListColourable G I.lists := by
  let : Fintype V := Fintype.ofFinite V
  rcases I.short_shape with hA | ⟨x,y,_,_,_,hedge,_⟩
  · obtain ⟨c,hc,_,_⟩ := I.extends_of_independent hA
    exact ⟨c,hc⟩
  · exact listColourable_of_one_short_edge_on_face I.embedding I.outer I.girth I.short
      I.on_outer x y hedge I.lists I.list_two I.list_three

/-- Induce an original instance on a connected set, retaining any chosen
outer edge and its actual allowed colours. In particular this supports the
new separator edge after the other side has been coloured. -/
noncomputable def induceWithEdge (I : OriginalBoundaryInstance G C)
    (S : Set V) [Nontrivial S] (hS : (G.induce S).Preconnected)
    (a b : V) (haS : a ∈ S) (hbS : b ∈ S) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b) (htab : ta ≠ tb) :
    OriginalBoundaryInstance (G.induce S) C := by
  let : Fintype V := Fintype.ofFinite V
  let o := (exists_outer_induced_of_preconnected I.embedding I.outer S hS).choose
  have ho := (exists_outer_induced_of_preconnected I.embedding I.outer S hS).choose_spec
  exact {
    embedding := inducedPlaneMap I.embedding S
    outer := o
    girth := five_le_egirth_induce S I.girth
    short := {x : S | x.1 ∈ I.short}
    on_outer := fun x hx => ho x (I.on_outer x.1 hx)
    short_shape := I.short_shape.induce I.short S
    lists := fun x => I.lists x.1
    list_two := fun x => I.list_two x.1
    list_three := fun x hx => I.list_three x.1 hx
    a := ⟨a,haS⟩
    b := ⟨b,hbS⟩
    edge := hab
    a_outer := ho _ ha
    b_outer := ho _ hb
    ta := ta
    tb := tb
    ta_mem := hta
    tb_mem := htb
    colours_ne := htab }

end OriginalBoundaryInstance
end Thomassen
