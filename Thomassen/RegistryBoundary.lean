/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalTheorem
public import Thomassen.PublicBoundaryGlobal

/-! A small equivalent public boundary certificate for protected compilation.
The original ComponentOuterBoundary and all its theorems are retained unchanged.
Componentwise ambient face orbits avoid constructing induced plane maps inside
the registry contract. Their equivalence to the original certificate is proved.
-/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A single actual ambient face orbit contains the marked vertices of each
component with an edge. Isolated vertices impose no dart condition. -/
def AmbientComponentOuterBoundary (M : PlaneMap G) (B : Set V) : Prop :=
  ∀ K : G.ConnectedComponent, Nonempty K.toSimpleGraph.Dart →
    ∃ outer : G.Dart, outer.fst ∈ K.supp ∧
      ∀ x : K, x.1 ∈ B → OnOuterFace M outer x.1

/-- The small public boundary certificate is exactly equivalent to the old
certificate on the actual induced plane map of each connected component. -/
theorem ambientComponentOuterBoundary_iff (M : PlaneMap G) (B : Set V) :
    AmbientComponentOuterBoundary M B ↔ ComponentOuterBoundary M B := by
  have hclosed (K : G.ConnectedComponent) :
      ∀ a ∈ K.supp, ∀ b, G.Adj a b → b ∈ K.supp := by
    intro a ha b hab
    exact (ConnectedComponent.sound hab.reachable).symm.trans ha
  constructor
  · intro h K hD
    obtain ⟨outer,hfst,hface⟩ := h K hD
    have hsnd : outer.snd ∈ K.supp := hclosed K outer.fst hfst outer.snd outer.adj
    let o : (restrict G K.supp).Dart := ⟨outer.toProd,outer.adj,hfst,hsnd⟩
    refine ⟨induceDartEquiv G K.supp o,?_⟩
    intro x hx
    exact (inducedPlaneMap_onOuterFace_of_closed M K.supp (hclosed K) o x).2 (hface x hx)
  · intro h K hD
    obtain ⟨outer,hface⟩ := h K hD
    let o := (induceDartEquiv G K.supp).symm outer
    refine ⟨toDart (restrict_le G K.supp) o,o.adj.2.1,?_⟩
    intro x hx
    apply (inducedPlaneMap_onOuterFace_of_closed M K.supp (hclosed K) o x).1
    have he : induceDartEquiv G K.supp o = outer :=
      (induceDartEquiv G K.supp).apply_symm_apply outer
    rw [he]
    exact hface x hx

/-- Thomassen (1995), Theorem 2.1, both alternatives and all exterior components.
The exceptional endpoint is distinguished: it has no simple length-two path
to any vertex of A. Lists and the two fixed colours are arbitrary. -/
theorem original_theorem_2_1_on_component_faces
    (M : PlaneMap G) (B : Set V) (hB : AmbientComponentOuterBoundary M B)
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
  exact original_theorem_2_1 M B ((ambientComponentOuterBoundary_iff M B).1 hB) hg A hAB hA
    L hLtwo hLthree a b hab ha hb ta tb hta htb htab

/-- Dvořák–Kawarabayashi (2011), Theorem 1, including possibly disconnected
plane graphs. A marked face can have several boundary dart orbits, recorded
by ComponentOuterBoundary. Proper chords of the precoloured path are allowed. -/
theorem dvorak_kawarabayashi_theorem_1_on_component_faces
    (M : PlaneMap G) (B : Set V) (hB : AmbientComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ 5)
    (hPB : ∀ x ∈ p.support, x ∈ B)
    (L : V → Finset C) (f : V → C)
    (hsingle : ∀ x ∈ p.support, L x = {f x})
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x ∈ B, x ∉ p.support → 2 ≤ (L x).card)
    (hinterior : ∀ x, x ∉ B → 3 ≤ (L x).card)
    (hshort : ∀ x, (L x).card = 2 → ∀ y, (L y).card ≤ 2 → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  exact dvorak_kawarabayashi_theorem_1_global M B ((ambientComponentOuterBoundary_iff M B).1 hB)
    hg p hp hlen hPB L f hsingle hproper hboundary hinterior hshort

end Thomassen
