/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalIndependent
public import Thomassen.OuterBoundary

/-! The independent-set alternative of the original paper, including all exterior components. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The full finite, possibly disconnected version of Theorem 2.1(i).
The componentwise face certificate includes two-list vertices in every
component of the unbounded-face boundary, rather than just one dart orbit. -/
theorem original_theorem_2_1_independent_global
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (hAind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  have hcomponent : ∀ K : G.ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, (∀ x : K, c x ∈ L x.1) ∧
      (∀ x : K, x.1 = a → c x = ta) ∧ (∀ x : K, x.1 = b → c x = tb) := by
    intro K
    by_cases haK : a ∈ K.supp
    · have hbK : b ∈ K.supp := (ConnectedComponent.sound hab.reachable).symm.trans haK
      let a' : K := ⟨a,haK⟩
      let b' : K := ⟨b,hbK⟩
      obtain ⟨outer,houter⟩ := hB K ⟨⟨(a',b'),hab⟩⟩
      obtain ⟨c,hc,hca,hcb⟩ := original_theorem_2_1_independent
        (inducedPlaneMap M K.supp) outer (five_le_egirth_induce K.supp hg)
        {x : K | x.1 ∈ A} (fun x hx => houter x (hAB hx))
        (fun x hx y hy hxy => hAind x.1 hx y.1 hy hxy)
        (fun x : K => L x.1) (fun x => hLtwo x.1) (fun x hx => hLthree x.1 hx)
        a' b' hab (houter a' ha) (houter b' hb) ta tb hta htb htab
      refine ⟨c,hc,?_,?_⟩
      · intro x hx
        have he : x = a' := Subtype.ext hx
        exact (congrArg (fun z : K => c z) he).trans hca
      · intro x hx
        have he : x = b' := Subtype.ext hx
        exact (congrArg (fun z : K => c z) he).trans hcb
    · have hbK : b ∉ K.supp := fun h => haK ((ConnectedComponent.sound hab.reachable).trans h)
      have hfree : ListColourable K.toSimpleGraph (fun x : K => L x.1) := by
        by_cases hedge : Nonempty K.toSimpleGraph.Dart
        · obtain ⟨outer,houter⟩ := hB K hedge
          let I : BoundaryInstance K.toSimpleGraph C := {
            girth := five_le_egirth_induce K.supp hg
            embedding := inducedPlaneMap M K.supp
            outer := outer
            precolor := .empty
            lists := fun x => L x.1
            prescribed := fun _ => ta
            on_outer := by simp
            singleton := by simp
            proper_precolor := by simp
            boundary_lists := fun x _ _ => hLtwo x.1
            interior_lists := fun x hx => hLthree x.1 (fun h => hx (houter x (hAB h)))
            short_edges := by
              intro x y hxy hx hy
              have hxA : x.1 ∈ A := by by_contra hn; have := hLthree x.1 hn; omega
              have hyA : y.1 ∈ A := by by_contra hn; have := hLthree y.1 hn; omega
              exact (hAind x.1 hxA y.1 hyA hxy).elim }
          exact boundary_extension C K K.toSimpleGraph I
        · let f : K → C := fun x => ((Finset.card_pos (s := L x.1)).1 (by have := hLtwo x.1; omega)).choose
          exact ⟨Coloring.mk f (fun {x y} hxy => (hedge ⟨⟨(x,y),hxy⟩⟩).elim),
            fun x => ((Finset.card_pos (s := L x.1)).1 (by have := hLtwo x.1; omega)).choose_spec⟩
      obtain ⟨c,hc⟩ := hfree
      exact ⟨c,hc,fun x hx => (haK (hx ▸ x.2)).elim,fun x hx => (hbK (hx ▸ x.2)).elim⟩
  let c := G.homOfConnectedComponents (fun K => (hcomponent K).choose)
  refine ⟨c,?_,?_,?_⟩
  · intro x
    exact (hcomponent (G.connectedComponentMk x)).choose_spec.1
      ⟨x,ConnectedComponent.connectedComponentMk_mem⟩
  · exact (hcomponent (G.connectedComponentMk a)).choose_spec.2.1
      ⟨a,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  · exact (hcomponent (G.connectedComponentMk b)).choose_spec.2.2
      ⟨b,ConnectedComponent.connectedComponentMk_mem⟩ rfl

end Thomassen
