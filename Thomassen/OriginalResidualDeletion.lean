/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalShortSetTransport

/-! Residual-list induction after a boundary deletion that may disconnect G. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Apply original strict induction to every residual component and restore
the deleted coloured set. The residual short-set condition is checked in the
remaining graph, so paths through deleted vertices are not excluded by fiat.
Actual face certificates are required component by component. -/
theorem extends_of_residual_components (I : OriginalBoundaryInstance G C)
    (D : Finset V) (hD : D.Nonempty) (f : V → C)
    (hf : ∀ x ∈ D, f x ∈ I.lists x)
    (hproper : ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → f x ≠ f y)
    (haD : I.a ∉ D) (hbD : I.b ∉ D) (A : Set V)
    (hshape : OriginalShortSet (G.induce (↑D : Set V)ᶜ) {x | x.1 ∈ A})
    (htwo : ∀ x, x ∉ D → 2 ≤ (residual G I.lists D f x).card)
    (hthree : ∀ x, x ∉ D → x ∉ A → 3 ≤ (residual G I.lists D f x).card)
    (hta : I.ta ∈ residual G I.lists D f I.a) (htb : I.tb ∈ residual G I.lists D f I.b)
    (hfaces : ∀ K : (G.induce (↑D : Set V)ᶜ).ConnectedComponent,
      ∀ [Nontrivial (componentVertexSet (↑D : Set V)ᶜ K)],
      ∃ o : (G.induce (componentVertexSet (↑D : Set V)ᶜ K)).Dart,
        (∀ x : componentVertexSet (↑D : Set V)ᶜ K, x.1 ∈ A →
          OnOuterFace (inducedPlaneMap I.embedding (componentVertexSet (↑D : Set V)ᶜ K)) o x) ∧
        (∀ x : componentVertexSet (↑D : Set V)ᶜ K, OnOuterFace I.embedding I.outer x.1 →
          OnOuterFace (inducedPlaneMap I.embedding (componentVertexSet (↑D : Set V)ᶜ K)) o x))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  let Q : Set V := (↑D : Set V)ᶜ
  let R : V → Finset C := residual G I.lists D f
  have hRtwo : ∀ x ∈ Q, 2 ≤ (R x).card := htwo
  have haQ : I.a ∈ Q := haD
  have hbQ : I.b ∈ Q := hbD
  have hcomponent : ∀ K : (G.induce Q).ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, (∀ z : K, c z ∈ R z.1.1) ∧
        (∀ z : K, z.1.1 = I.a → c z = I.ta) ∧ (∀ z : K, z.1.1 = I.b → c z = I.tb) := by
    intro K
    let T := componentVertexSet Q K
    let φ := componentInduceIso Q K
    have hTsub : T ⊆ Q := componentVertexSet_subset Q K
    have hpair : I.a ∈ T ↔ I.b ∈ T := ⟨
      fun h => componentVertexSet_adj_closed Q K h hbQ I.edge,
      fun h => componentVertexSet_adj_closed Q K h haQ I.edge.symm⟩
    have hpiece : ∃ c : (G.induce T).Coloring C, (∀ z : T, c z ∈ R z.1) ∧
        (∀ z : T, z.1 = I.a → c z = I.ta) ∧ (∀ z : T, z.1 = I.b → c z = I.tb) := by
      by_cases hnt : Nontrivial T
      · let : Nontrivial T := hnt
        obtain ⟨o,hAface,hold⟩ := hfaces K
        let e : G.induce T ↪g G.induce Q := {
          toFun := fun z => ⟨z.1,hTsub z.2⟩
          inj' := by intro x y h; exact Subtype.ext (congrArg (fun z : Q => z.1) h)
          map_rel_iff' := Iff.rfl }
        have hTshape : OriginalShortSet (G.induce T) {z : T | z.1 ∈ A} :=
          OriginalShortSet.comap {z : Q | z.1 ∈ A} hshape e
        have hExt : ∀ (a b : T), (G.induce T).Adj a b →
            OnOuterFace (inducedPlaneMap I.embedding T) o a →
            OnOuterFace (inducedPlaneMap I.embedding T) o b →
            ∀ ta tb, ta ∈ R a.1 → tb ∈ R b.1 → ta ≠ tb →
              ∃ c : (G.induce T).Coloring C, (∀ z : T, c z ∈ R z.1) ∧ c a = ta ∧ c b = tb := by
          intro a b hab haf hbf ta tb hta htb htab
          let J : OriginalBoundaryInstance (G.induce T) C := {
            embedding := inducedPlaneMap I.embedding T
            outer := o
            girth := five_le_egirth_induce T I.girth
            short := {z : T | z.1 ∈ A}
            on_outer := hAface
            short_shape := hTshape
            lists := fun z => R z.1
            list_two := fun z => htwo z.1 (hTsub z.2)
            list_three := fun z hz => hthree z.1 (hTsub z.2) hz
            a := a
            b := b
            edge := hab
            a_outer := haf
            b_outer := hbf
            ta := ta
            tb := tb
            ta_mem := hta
            tb_mem := htb
            colours_ne := htab }
          obtain ⟨d,hd⟩ := hD
          have hdT : d ∉ T := fun h => hTsub h hd
          exact hsmall T (G.induce T) J (card_induced_vertices_lt T hdT)
        by_cases haT : I.a ∈ T
        · have hbT := hpair.1 haT
          obtain ⟨c,hc,hca,hcb⟩ := hExt ⟨I.a,haT⟩ ⟨I.b,hbT⟩ I.edge
            (hold _ I.a_outer) (hold _ I.b_outer) I.ta I.tb hta htb I.colours_ne
          refine ⟨c,hc,?_,?_⟩
          · intro z hz
            exact (congrArg (fun w : T => c w) (Subtype.ext hz)).trans hca
          · intro z hz
            exact (congrArg (fun w : T => c w) (Subtype.ext hz)).trans hcb
        · have hbT : I.b ∉ T := fun h => haT (hpair.2 h)
          obtain ⟨ta,hta'⟩ := Finset.card_pos.1
            (show 0 < (R o.fst.1).card by have := hRtwo o.fst.1 (hTsub o.fst.2); omega)
          obtain ⟨tb,htb',htba⟩ := Finset.exists_mem_ne (s := R o.snd.1)
            (by have := hRtwo o.snd.1 (hTsub o.snd.2); omega) ta
          have hbf : OnOuterFace (inducedPlaneMap I.embedding T) o o.snd :=
            ⟨(inducedPlaneMap I.embedding T).facePerm o,(Equiv.Perm.SameCycle.refl _ _).apply_right,
              (inducedPlaneMap I.embedding T).isRotationSystem.fst_apply o.symm⟩
          obtain ⟨c,hc,_,_⟩ := hExt o.fst o.snd o.adj (onOuterFace_self _ _) hbf ta tb hta' htb' htba.symm
          exact ⟨c,hc,fun z hz => (haT (hz ▸ z.2)).elim,fun z hz => (hbT (hz ▸ z.2)).elim⟩
      · have haT : I.a ∉ T := by
          intro h
          exact hnt (show Nontrivial T from
            (show (G.induce T).Adj ⟨I.a,h⟩ ⟨I.b,hpair.1 h⟩ from I.edge).nontrivial)
        have hbT : I.b ∉ T := fun h => haT (hpair.2 h)
        let g : T → C := fun z => ((Finset.card_pos (s := R z.1)).1
          (by have := hRtwo z.1 (hTsub z.2); omega)).choose
        exact ⟨Coloring.mk g (fun {z w} hzw => (hnt hzw.nontrivial).elim),
          fun z => ((Finset.card_pos (s := R z.1)).1 (by have := hRtwo z.1 (hTsub z.2); omega)).choose_spec,
          fun z hz => (haT (hz ▸ z.2)).elim,fun z hz => (hbT (hz ▸ z.2)).elim⟩
    obtain ⟨c,hc,hca,hcb⟩ := hpiece
    exact ⟨c.comp φ.toHom,fun z => hc (φ z),fun z hz => hca (φ z) hz,fun z hz => hcb (φ z) hz⟩
  let cQ : (G.induce Q).Coloring C := (G.induce Q).homOfConnectedComponents (fun K => (hcomponent K).choose)
  have hcQ : ∀ z : Q, cQ z ∈ R z.1 := fun z =>
    (hcomponent ((G.induce Q).connectedComponentMk z)).choose_spec.1
      ⟨z,ConnectedComponent.connectedComponentMk_mem⟩
  have hcaQ : cQ ⟨I.a,haQ⟩ = I.ta :=
    (hcomponent ((G.induce Q).connectedComponentMk ⟨I.a,haQ⟩)).choose_spec.2.1
      ⟨⟨I.a,haQ⟩,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  have hcbQ : cQ ⟨I.b,hbQ⟩ = I.tb :=
    (hcomponent ((G.induce Q).connectedComponentMk ⟨I.b,hbQ⟩)).choose_spec.2.2
      ⟨⟨I.b,hbQ⟩,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  let g : V → C := fun z => if hz : z ∈ D then f z else cQ ⟨z,hz⟩
  refine ⟨Coloring.mk g ?_,?_,?_,?_⟩
  · intro z w hzw
    by_cases hz : z ∈ D <;> by_cases hw : w ∈ D
    · simpa only [g,dite_eq_left hz,dite_eq_left hw] using hproper z hz w hw hzw
    · simpa only [g,dite_eq_left hz,dite_eq_right hw] using
        (((mem_residual_iff I.lists D f w _).1 (hcQ ⟨w,hw⟩)).2 z hz hzw.symm).symm
    · simpa only [g,dite_eq_right hz,dite_eq_left hw] using
        ((mem_residual_iff I.lists D f z _).1 (hcQ ⟨z,hz⟩)).2 w hw hzw
    · simpa only [g,dite_eq_right hz,dite_eq_right hw] using
        (show cQ ⟨z,hz⟩ ≠ cQ ⟨w,hw⟩ from cQ.valid hzw)
  · intro z
    change g z ∈ I.lists z
    by_cases hz : z ∈ D
    · simpa only [g,dite_eq_left hz] using hf z hz
    · simpa only [g,dite_eq_right hz] using ((mem_residual_iff I.lists D f z _).1 (hcQ ⟨z,hz⟩)).1
  · change g I.a = I.ta
    simpa only [g,dite_eq_right haD] using hcaQ
  · change g I.b = I.tb
    simpa only [g,dite_eq_right hbD] using hcbQ

/-- A connected coloured deletion meeting the actual old face supplies all
component face certificates automatically. Residual short vertices may be old
short vertices or newly exposed neighbours of the deleted set. -/
theorem extends_of_connected_boundary_deletion (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (D : Finset V) (ha : a ∈ D) (hD : ConnSet G (↑D : Set V)) (f : V → C)
    (hf : ∀ x ∈ D, f x ∈ I.lists x)
    (hproper : ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → f x ≠ f y)
    (haD : I.a ∉ D) (hbD : I.b ∉ D) (A : Set V)
    (hshape : OriginalShortSet (G.induce (↑D : Set V)ᶜ) {x | x.1 ∈ A})
    (hA : ∀ x ∈ A, x ∈ I.short ∨ ∃ y ∈ D, G.Adj x y)
    (htwo : ∀ x, x ∉ D → 2 ≤ (residual G I.lists D f x).card)
    (hthree : ∀ x, x ∉ D → x ∉ A → 3 ≤ (residual G I.lists D f x).card)
    (hta : I.ta ∈ residual G I.lists D f I.a) (htb : I.tb ∈ residual G I.lists D f I.b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  apply I.extends_of_residual_components D ⟨a,ha⟩ f hf hproper haD hbD A hshape htwo hthree hta htb ?_ hsmall
  intro K instNT
  obtain ⟨o,hold,hnew⟩ := exists_outer_component_after_connected_boundary_deletion
    I.embedding I.outer hG p hp hface hroot
    (fun x hx => (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot x).2 hx)
    (↑D : Set V) ha hD K
  refine ⟨o,?_,hold⟩
  intro x hx
  rcases hA x.1 hx with hxold | hxnew
  · exact hold x (I.on_outer x.1 hxold)
  · exact hnew x hxnew

end Thomassen.OriginalBoundaryInstance
