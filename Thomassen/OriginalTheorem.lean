/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalClosure

/-! The entire original 1995 Theorem 2.1, with componentwise outer boundary. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Thomassen (1995), Theorem 2.1, both alternatives and all exterior components.
The exceptional endpoint is distinguished: it has no simple length-two path
to any vertex of A. Lists and the two fixed colours are arbitrary. -/
theorem original_theorem_2_1
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (hA : (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) ∨
      ∃ x y, x ∈ A ∧ y ∈ A ∧ G.Adj x y ∧
        (∀ r ∈ A, ∀ s ∈ A, G.Adj r s → (r = x ∧ s = y) ∨ (r = y ∧ s = x)) ∧
        (∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False))
    (L : V → Finset C) (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLthree : ∀ x, x ∉ A → 3 ≤ (L x).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ c a = ta ∧ c b = tb := by
  rcases hA with hAind | ⟨x,y,hx,hy,hxy,hedge,hNo⟩
  · exact original_theorem_2_1_independent_global M B hB hg A hAB hAind
      L hLtwo hLthree a b hab ha hb ta tb hta htb htab
  · let K := G.connectedComponentMk a
    have haK : a∈K.supp := ConnectedComponent.connectedComponentMk_mem
    have hbK : b∈K.supp := (ConnectedComponent.sound hab.reachable).symm.trans haK
    let aK : K := ⟨a,haK⟩
    let bK : K := ⟨b,hbK⟩
    obtain ⟨outer,houter⟩ := hB K ⟨⟨(aK,bK),hab⟩⟩
    have hshape : OriginalShortSet G A := Or.inr ⟨x,y,hx,hy,hxy,hedge,hNo⟩
    let I : OriginalBoundaryInstance K.toSimpleGraph C := {
      embedding := inducedPlaneMap M K.supp
      outer := outer
      girth := five_le_egirth_induce K.supp hg
      short := {z : K | z.1∈A}
      on_outer := fun z hz => houter z (hAB hz)
      short_shape := hshape.induce A K.supp
      lists := fun z => L z.1
      list_two := fun z => hLtwo z.1
      list_three := fun z hz => hLthree z.1 hz
      a := aK
      b := bK
      edge := hab
      a_outer := houter aK ha
      b_outer := houter bK hb
      ta := ta
      tb := tb
      ta_mem := hta
      tb_mem := htb
      colours_ne := htab }
    obtain ⟨cK,hcK,hca,hcb⟩ := original_boundary_extension C K K.toSimpleGraph I
    apply assemble_fixed_component_with_one_short_edge M B hB hg A hAB x y hedge L hLtwo hLthree
      a b hab ta tb K haK cK hcK
    · intro z hz
      exact (congrArg (fun z : K => cK z) (Subtype.ext hz : z=aK)).trans hca
    · intro z hz
      exact (congrArg (fun z : K => cK z) (Subtype.ext hz : z=bK)).trans hcb

end Thomassen
