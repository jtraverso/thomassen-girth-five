/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalIndependentGlobal
public import Thomassen.ExceptionalBoundaryBridge

/-! Component assembly for the original exceptional-edge alternative.
No unresolved connected extension is assumed in the free components. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Without an old prescribed edge, one exceptional short-list edge is
colourable: prescribe that edge itself and use the already proved incident
case. This needs no two-path exclusion. If A is independent, the empty
prescription theorem applies instead. -/
theorem listColourable_of_one_short_edge_on_face
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card) : ListColourable G L := by
  by_cases hAind : ∀ r ∈ A, ∀ s ∈ A, ¬ G.Adj r s
  · obtain ⟨ta,hta⟩ := Finset.card_pos.1 (show 0 < (L outer.fst).card by have := hLtwo outer.fst; omega)
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
      boundary_lists := fun z _ _ => hLtwo z
      interior_lists := fun z hz => hLthree z (fun h => hz (hAface z h))
      short_edges := by
        intro r s hrs hr hs
        have hrA : r ∈ A := by by_contra hn; have := hLthree r hn; omega
        have hsA : s ∈ A := by by_contra hn; have := hLthree s hn; omega
        exact (hAind r hrA s hsA hrs).elim }
    exact boundary_extension C V G I
  · push Not at hAind
    obtain ⟨r,hr,s,hs,hrs⟩ := hAind
    obtain ⟨tr,htr⟩ := Finset.card_pos.1 (show 0 < (L r).card by have := hLtwo r; omega)
    obtain ⟨ts,hts,htsr⟩ := Finset.exists_mem_ne (s := L s) (by have := hLtwo s; omega) tr
    have hinc : x = r ∨ y = r ∨ x = s ∨ y = s := by
      rcases hedge r hr s hs hrs with h | h
      · exact Or.inl h.1.symm
      · exact Or.inr (Or.inl h.1.symm)
    obtain ⟨c,hc,_,_⟩ := original_theorem_2_1_exceptional_incident M outer hg A hAface
      x y hedge L hLtwo hLthree r s hrs (hAface r hr) (hAface s hs)
      tr ts htr hts htsr.symm hinc
    exact ⟨c,hc⟩

/-- Once the component containing the fixed edge has actually been coloured,
all other components can be filled unconditionally, even if the unique short
edge belongs to one of them. The input is a colouring, not an extension
hypothesis for the unresolved case of the theorem. -/
theorem assemble_fixed_component_with_one_short_edge
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ta tb : C)
    (K : G.ConnectedComponent) (haK : a ∈ K.supp)
    (cK : K.toSimpleGraph.Coloring C) (hcK : ∀ z : K, cK z ∈ L z.1)
    (hca : ∀ z : K, z.1 = a → cK z = ta)
    (hcb : ∀ z : K, z.1 = b → cK z = tb) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  have hcomponent : ∀ T : G.ConnectedComponent,
      ∃ c : T.toSimpleGraph.Coloring C, (∀ z : T, c z ∈ L z.1) ∧
      (∀ z : T, z.1 = a → c z = ta) ∧ (∀ z : T, z.1 = b → c z = tb) := by
    intro T
    by_cases hTK : T = K
    · subst T
      exact ⟨cK,hcK,hca,hcb⟩
    · have haT : a ∉ T.supp := fun h => hTK (((T.mem_supp_iff a).1 h).symm.trans ((K.mem_supp_iff a).1 haK))
      have hbT : b ∉ T.supp := fun h => haT ((ConnectedComponent.sound hab.reachable).trans h)
      have hfree : ListColourable T.toSimpleGraph (fun z : T => L z.1) := by
        by_cases hD : Nonempty T.toSimpleGraph.Dart
        · obtain ⟨outer,houter⟩ := hB T hD
          by_cases hxyT : x ∈ T.supp ∧ y ∈ T.supp
          · exact listColourable_of_one_short_edge_on_face (inducedPlaneMap M T.supp) outer
              (five_le_egirth_induce T.supp hg) {z : T | z.1 ∈ A}
              (fun z hz => houter z (hAB hz)) ⟨x,hxyT.1⟩ ⟨y,hxyT.2⟩
              (by
                intro r hr s hs hrs
                rcases hedge r.1 hr s.1 hs hrs with h | h
                · exact Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩
                · exact Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
              (fun z => L z.1) (fun z => hLtwo z.1) (fun z hz => hLthree z.1 hz)
          · have hAind : ∀ r : T, r.1 ∈ A → ∀ s : T, s.1 ∈ A → ¬ T.toSimpleGraph.Adj r s := by
              intro r hr s hs hrs
              rcases hedge r.1 hr s.1 hs hrs with h | h
              · exact hxyT ⟨h.1 ▸ r.2,h.2 ▸ s.2⟩
              · exact hxyT ⟨h.2 ▸ s.2,h.1 ▸ r.2⟩
            exact listColourable_of_one_short_edge_on_face (inducedPlaneMap M T.supp) outer
              (five_le_egirth_induce T.supp hg) {z : T | z.1 ∈ A}
              (fun z hz => houter z (hAB hz)) outer.fst outer.snd
              (fun r hr s hs hrs => (hAind r hr s hs hrs).elim)
              (fun z => L z.1) (fun z => hLtwo z.1) (fun z hz => hLthree z.1 hz)
        · let f : T → C := fun z => ((Finset.card_pos (s := L z.1)).1 (by have := hLtwo z.1; omega)).choose
          exact ⟨Coloring.mk f (fun {r s} hrs => (hD ⟨⟨(r,s),hrs⟩⟩).elim),
            fun z => ((Finset.card_pos (s := L z.1)).1 (by have := hLtwo z.1; omega)).choose_spec⟩
      obtain ⟨c,hc⟩ := hfree
      exact ⟨c,hc,fun z hz => (haT (hz ▸ z.2)).elim,fun z hz => (hbT (hz ▸ z.2)).elim⟩
  let c : G.Coloring C := G.homOfConnectedComponents (fun T => (hcomponent T).choose)
  refine ⟨c,?_,?_,?_⟩
  · intro z
    exact (hcomponent (G.connectedComponentMk z)).choose_spec.1
      ⟨z,ConnectedComponent.connectedComponentMk_mem⟩
  · exact (hcomponent (G.connectedComponentMk a)).choose_spec.2.1
      ⟨a,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  · exact (hcomponent (G.connectedComponentMk b)).choose_spec.2.2
      ⟨b,ConnectedComponent.connectedComponentMk_mem⟩ rfl

/-- Every counterexample to the global exceptional alternative is already
a counterexample in the connected component containing the prescribed edge.
Both exceptional endpoints belong to that component. In particular, free
components leave no additional mathematical extension obligation. -/
theorem exceptional_counterexample_fixed_component
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb)
    (K : G.ConnectedComponent) (haK : a ∈ K.supp) :
    ∃ (_hxK : x ∈ K.supp) (_hyK : y ∈ K.supp) (hbK : b ∈ K.supp),
      ∃ outer : K.toSimpleGraph.Dart,
        (∀ z : K, z.1 ∈ B → OnOuterFace (inducedPlaneMap M K.supp) outer z) ∧
        ¬ ∃ c : K.toSimpleGraph.Coloring C, (∀ z : K, c z ∈ L z.1) ∧
          c ⟨a,haK⟩ = ta ∧ c ⟨b,hbK⟩ = tb := by
  have hbK : b ∈ K.supp := (ConnectedComponent.sound hab.reachable).symm.trans haK
  let a' : K := ⟨a,haK⟩
  let b' : K := ⟨b,hbK⟩
  obtain ⟨outer,houter⟩ := hB K ⟨⟨(a',b'),hab⟩⟩
  have hbadK : ¬ ∃ c : K.toSimpleGraph.Coloring C, (∀ z : K, c z ∈ L z.1) ∧
      c a' = ta ∧ c b' = tb := by
    rintro ⟨c,hc,hca,hcb⟩
    apply hbad
    apply assemble_fixed_component_with_one_short_edge M B hB hg A hAB x y hedge
      L hLtwo hLthree a b hab ta tb K haK c hc
    · intro z hz
      exact (congrArg (fun w : K => c w) (Subtype.ext hz)).trans hca
    · intro z hz
      exact (congrArg (fun w : K => c w) (Subtype.ext hz)).trans hcb
  have hxK : x ∈ K.supp := by
    by_contra hn
    apply hbadK
    exact original_theorem_2_1_independent (inducedPlaneMap M K.supp) outer
      (five_le_egirth_induce K.supp hg) {z : K | z.1 ∈ A}
      (fun z hz => houter z (hAB hz))
      (by
        intro r hr s hs hrs
        rcases hedge r.1 hr s.1 hs hrs with h | h
        · exact hn (h.1 ▸ r.2)
        · exact hn (h.2 ▸ s.2))
      (fun z => L z.1) (fun z => hLtwo z.1) (fun z hz => hLthree z.1 hz)
      a' b' hab (houter a' ha) (houter b' hb) ta tb hta htb htab
  have hyK : y ∈ K.supp := (ConnectedComponent.sound hxy.reachable).symm.trans hxK
  exact ⟨hxK,hyK,hbK,outer,houter,hbadK⟩

/-- The identical-two-list obstruction is also necessary for a global,
possibly disconnected counterexample. Component reduction and path transport
are proved here; the two-path assumption is not strengthened on restriction.
This theorem does not rule out the resulting normalized configuration. -/
theorem exceptional_global_counterexample_normal_form
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAB : A ⊆ B)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b) (ha : a ∈ B) (hb : b ∈ B)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb) :
    G.Reachable a x ∧ G.Reachable a y ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      ¬ G.Adj a x ∧ ¬ G.Adj b x ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y ∧
      (L x).card = 2 ∧ (L y).card = 2 ∧ L x = L y := by
  let K : G.ConnectedComponent := G.connectedComponentMk a
  have haK : a ∈ K.supp := ConnectedComponent.connectedComponentMk_mem
  obtain ⟨hxK,hyK,hbK,outer,houter,hbadK⟩ := exceptional_counterexample_fixed_component
    M B hB hg A hAB x y hxy hedge L hLtwo hLthree a b hab ha hb ta tb hta htb htab hbad K haK
  let x' : K := ⟨x,hxK⟩
  let y' : K := ⟨y,hyK⟩
  let a' : K := ⟨a,haK⟩
  let b' : K := ⟨b,hbK⟩
  have hedgeK : ∀ r : K, r.1 ∈ A → ∀ s : K, s.1 ∈ A → K.toSimpleGraph.Adj r s →
      (r = x' ∧ s = y') ∨ (r = y' ∧ s = x') := by
    intro r hr s hs hrs
    rcases hedge r.1 hr s.1 hs hrs with h | h
    · exact Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩
    · exact Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩
  have hNoK : ∀ z : K, z.1 ∈ A → ∀ p : K.toSimpleGraph.Walk x' z,
      p.IsPath → p.length = 2 → False := by
    intro z hz p hp hlen
    exact hNo z.1 hz (p.map (Embedding.induce K.supp).toHom)
      (hp.map Subtype.val_injective) ((Walk.length_map (Embedding.induce K.supp).toHom p).trans hlen)
  obtain ⟨hxa,hxb,hya,hyb,hax,hbx,hay,hby,hx2,hy2,heq,_⟩ :=
    exceptional_counterexample_no_short_outer_bridge (inducedPlaneMap M K.supp) outer
      K.connected_toSimpleGraph.preconnected (five_le_egirth_induce K.supp hg)
      {z : K | z.1 ∈ A} (fun z hz => houter z (hAB hz)) x' y' hxA hyA hxy hedgeK hNoK
      (fun z => L z.1) (fun z => hLtwo z.1) (fun z hz => hLthree z.1 hz)
      a' b' hab (houter a' ha) (houter b' hb) ta tb hta htb htab hbadK
  refine ⟨ConnectedComponent.exact hxK.symm,ConnectedComponent.exact hyK.symm,
    ?_,?_,?_,?_,hax,hbx,hay,hby,hx2,hy2,heq⟩
  · exact fun h => hxa (Subtype.ext h)
  · exact fun h => hxb (Subtype.ext h)
  · exact fun h => hya (Subtype.ext h)
  · exact fun h => hyb (Subtype.ext h)

end Thomassen
