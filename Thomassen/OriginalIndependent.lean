/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryExtension

/-! The independent-set alternative in Theorem 2.1 of the 1995 paper. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]
namespace BoundaryInstance

/-- The proved edge-star induction now has no residual induction hypothesis. -/
theorem extend_edge_of_preconnected (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ c a = ta ∧ c b = tb := by
  obtain ⟨f,hfa,hfb,hf,hproper⟩ := I.exists_edgeStar_colours hP a b hab ta tb hta htb htab
  obtain ⟨c,hc,hfixed⟩ := I.edgeStar_extension_of_smaller (Nat.card V + 1)
    (fun W _ H J _ => boundary_extension C W H J) hP hG a b hab ha hb f hf hproper (by omega)
  exact ⟨c,hc,(hfixed a (Or.inl (Or.inl rfl))).trans hfa,
    (hfixed b (Or.inr (Or.inl rfl))).trans hfb⟩

/-- An adjacent pair on the selected face can be fixed even when the ambient
graph is disconnected. Other components have full three-lists. -/
theorem extend_edge (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ c a = ta ∧ c b = tb := by
  let : Fintype V := Fintype.ofFinite V
  let S : Set V := {x | G.Reachable I.outer.fst x}
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S :=
    fun _ hx _ hxy => hx.trans hxy.reachable
  have hroot : I.outer.fst ∈ S := Reachable.refl _
  have haS : a ∈ S := reachable_of_onOuterFace I.embedding I.outer ha
  have hbS : b ∈ S := reachable_of_onOuterFace I.embedding I.outer hb
  have hPsub : ∀ x ∈ I.precolor.vertices, x ∈ S := by simp [hP]
  let J := I.induceClosed S hclosed hroot hPsub
  have hempty (P : BoundaryPrecolor G) (h : P = .empty)
      (hs : ∀ x ∈ P.vertices, x ∈ S) : P.induce S hs = .empty := by
    subst P
    rfl
  have hJP : J.precolor = .empty := hempty I.precolor hP hPsub
  have hconn : (G.induce S).Preconnected := by
    intro x y
    obtain ⟨p⟩ := x.2.symm.trans y.2
    exact ⟨p.induce S (fun z hz => x.2.trans (p.takeUntil z hz).reachable)⟩
  have hface : ∀ x : S, OnOuterFace J.embedding J.outer x ↔
      OnOuterFace I.embedding I.outer x.1 := by
    intro x
    exact inducedPlaneMap_onOuterFace_of_closed I.embedding S hclosed _ x
  obtain ⟨cS,hcS,hca,hcb⟩ := J.extend_edge_of_preconnected hJP hconn
    ⟨a,haS⟩ ⟨b,hbS⟩ hab ((hface _).2 ha) ((hface _).2 hb) ta tb hta htb htab
  have hTlists : ∀ x : (Sᶜ : Set V), 3 ≤ (I.lists x.1).card :=
    fun x => I.list_ge_three_of_not_reachable x.2
  have hT : ListColourable (G.induce Sᶜ) (fun x => I.lists x.1) := by
    apply choosable_of_boundary_extension (boundary_extension C) (G.induce Sᶜ)
      ⟨inducedPlaneMap I.embedding Sᶜ⟩ (five_le_egirth_induce Sᶜ I.girth)
    exact hTlists
  obtain ⟨cT,hcT⟩ := hT
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x,hx⟩ else cT ⟨x,hx⟩
  refine ⟨Coloring.mk f ?_,?_,?_,?_⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · have hy := hclosed x hx y hxy
      simpa only [f,dite_eq_left hx,dite_eq_left hy] using
        (show cS ⟨x,hx⟩ ≠ cS ⟨y,hy⟩ from cS.valid hxy)
    · have hy : y ∉ S := fun hy => hx (hclosed y hy x hxy.symm)
      simpa only [f,dite_eq_right hx,dite_eq_right hy] using
        (show cT ⟨x,hx⟩ ≠ cT ⟨y,hy⟩ from cT.valid hxy)
  · intro x
    change f x ∈ I.lists x
    by_cases hx : x ∈ S
    · simpa only [f,dite_eq_left hx,J,induceClosed] using hcS ⟨x,hx⟩
    · simpa only [f,dite_eq_right hx] using hcT ⟨x,hx⟩
  · change f a = ta
    simpa only [f,dite_eq_left haS] using hca
  · change f b = tb
    simpa only [f,dite_eq_left hbS] using hcb

end BoundaryInstance

/-- Theorem 2.1(i): two allowed distinct colours at an arbitrary outer edge
extend when the vertices allowed two-lists form an independent set. No
cardinality bound or induction premise remains in the conclusion. -/
theorem original_theorem_2_1_independent (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (A : Set V)
    (hAface : ∀ x ∈ A, OnOuterFace M outer x)
    (hAind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  let I : BoundaryInstance G C := {
    girth := hg
    embedding := M
    outer := outer
    precolor := .empty
    lists := L
    prescribed := fun _ => ta
    on_outer := by simp
    singleton := by simp
    proper_precolor := by simp
    boundary_lists := fun x _ _ => hLtwo x
    interior_lists := fun x hx => hLthree x (fun h => hx (hAface x h))
    short_edges := by
      intro x y hxy hx hy
      have hxA : x ∈ A := by by_contra hn; have := hLthree x hn; omega
      have hyA : y ∈ A := by by_contra hn; have := hLthree y hn; omega
      exact (hAind x hxA y hyA hxy).elim }
  exact I.extend_edge rfl a b hab ha hb ta tb hta htb htab

end Thomassen
