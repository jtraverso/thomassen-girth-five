/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SingleBoundaryDeletion
public import Thomassen.ExceptionalDeletionLists
public import Thomassen.OriginalIndependent

/-! Eliminate an exceptional edge when its distinguished endpoint has an
available colour not in the other endpoint's list. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The exceptional-edge deletion needs no induction hypothesis. All remaining
components have independent short lists, so the already proved alternative (i)
colours them; the component containing the prescribed edge keeps its colours.
The colour at the deleted endpoint is unavailable at the other short endpoint. -/
theorem original_theorem_2_1_exceptional_colour_outside_other_list
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    (hg : 5 ≤ G.egirth) (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (t : C) (htx : t ∈ L x) (hty : t ∉ L y)
    (haavoid : G.Adj a x → ta ≠ t) (hbavoid : G.Adj b x → tb ≠ t) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  let S : Set V := ({x} : Set V)ᶜ
  let R : V → Finset C := residual G L {x} (fun _ => t)
  have haS : a ∈ S := by simpa only [S,Set.mem_compl_iff,Set.mem_singleton_iff] using hxa.symm
  have hbS : b ∈ S := by simpa only [S,Set.mem_compl_iff,Set.mem_singleton_iff] using hxb.symm
  have hRmem : ∀ z c, c ∈ R z ↔ c ∈ L z ∧ (G.Adj z x → c ≠ t) := by
    intro z c
    simp only [R,mem_residual_iff,Finset.mem_singleton,forall_eq]
  have hRtwo : ∀ z ∈ S, 2 ≤ (R z).card := by
    intro z hz
    by_cases hzA : z ∈ A
    · have hzx : z ≠ x := hz
      have heq := exceptional_delete_old_list_unchanged A x y hxA hedge L t hty hzA hzx
      simpa only [R,heq] using hLtwo z
    · apply residual_three_to_two L {x} (fun _ => t) z (hLthree z hzA)
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hRind : ∀ z ∈ S, ∀ w ∈ S, (R z).card ≤ 2 → (R w).card ≤ 2 → ¬ G.Adj z w := by
    intro z hz w hw hzs hws
    exact exceptional_delete_short_lists_independent hg A x y hedge hNo L hLthree t hz hw hzs hws
  have hRface : ∀ z, (R z).card ≤ 2 → z ∈ A ∨ G.Adj z x := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl hzA
    · right
      by_contra hn
      have heq : R z = L z := by
        apply residual_unchanged
        intro w hw
        have he : w = x := Finset.mem_singleton.1 hw
        subst w
        exact hn
      have h3 := hLthree z hzA
      rw [heq] at hz
      omega
  have htaR : ta ∈ R a := (hRmem a ta).2 ⟨hta,haavoid⟩
  have htbR : tb ∈ R b := (hRmem b tb).2 ⟨htb,hbavoid⟩
  have hcomponent : ∀ K : (G.induce S).ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, (∀ z : K, c z ∈ R z.1.1) ∧
      (∀ z : K, z.1.1 = a → c z = ta) ∧ (∀ z : K, z.1.1 = b → c z = tb) := by
    intro K
    let T := componentVertexSet S K
    let φ := componentInduceIso S K
    have hTsub : T ⊆ S := componentVertexSet_subset S K
    have hpair : a ∈ T ↔ b ∈ T := ⟨
      fun haT => componentVertexSet_adj_closed S K haT hbS hab,
      fun hbT => componentVertexSet_adj_closed S K hbT haS hab.symm⟩
    have hpiece : ∃ c : (G.induce T).Coloring C, (∀ z : T, c z ∈ R z.1) ∧
        (∀ z : T, z.1 = a → c z = ta) ∧ (∀ z : T, z.1 = b → c z = tb) := by
      by_cases hnt : Nontrivial T
      · let : Nontrivial T := hnt
        obtain ⟨o,hold,hnew⟩ := exists_outer_component_after_boundary_vertex_deletion M outer hG x (hAface x hxA) K
        have hshortface : ∀ z : T, (R z.1).card ≤ 2 →
            OnOuterFace (inducedPlaneMap M T) o z := by
          intro z hz
          rcases hRface z.1 hz with hzA | hzx
          · exact hold z (hAface z.1 hzA)
          · exact hnew z hzx
        have hthree : ∀ z : T, ¬ (R z.1).card ≤ 2 → 3 ≤ (R z.1).card := by
          intro z hz; omega
        by_cases haT : a ∈ T
        · have hbT := hpair.1 haT
          obtain ⟨c,hc,hca,hcb⟩ := original_theorem_2_1_independent
            (inducedPlaneMap M T) o (five_le_egirth_induce T hg)
            {z : T | (R z.1).card ≤ 2} hshortface
            (fun z hz w hw hzw => hRind z.1 (hTsub z.2) w.1 (hTsub w.2) hz hw hzw)
            (fun z : T => R z.1) (fun z => hRtwo z.1 (hTsub z.2)) hthree
            ⟨a,haT⟩ ⟨b,hbT⟩ hab (hold _ ha) (hold _ hb) ta tb htaR htbR htab
          refine ⟨c,hc,?_,?_⟩
          · intro z hz
            exact (congrArg (fun w : T => c w) (Subtype.ext hz)).trans hca
          · intro z hz
            exact (congrArg (fun w : T => c w) (Subtype.ext hz)).trans hcb
        · have hbT : b ∉ T := fun h => haT (hpair.2 h)
          let I : BoundaryInstance (G.induce T) C := {
            girth := five_le_egirth_induce T hg
            embedding := inducedPlaneMap M T
            outer := o
            precolor := .empty
            lists := fun z => R z.1
            prescribed := fun _ => t
            on_outer := by simp
            singleton := by simp
            proper_precolor := by simp
            boundary_lists := fun z _ _ => hRtwo z.1 (hTsub z.2)
            interior_lists := fun z hz => hthree z (fun h => hz (hshortface z h))
            short_edges := fun {z w} hzw hz hw =>
              (hRind z.1 (hTsub z.2) w.1 (hTsub w.2) hz hw hzw).elim }
          obtain ⟨c,hc⟩ := boundary_extension C T (G.induce T) I
          exact ⟨c,hc,fun z hz => (haT (hz ▸ z.2)).elim,fun z hz => (hbT (hz ▸ z.2)).elim⟩
      · have haT : a ∉ T := by
          intro h
          exact hnt (show Nontrivial T from
            (show (G.induce T).Adj ⟨a,h⟩ ⟨b,hpair.1 h⟩ from hab).nontrivial)
        have hbT : b ∉ T := fun h => haT (hpair.2 h)
        let f : T → C := fun z => ((Finset.card_pos (s := R z.1)).1
          (by have := hRtwo z.1 (hTsub z.2); omega)).choose
        refine ⟨Coloring.mk f (fun {z w} hzw => (hnt hzw.nontrivial).elim),
          fun z => ?_,fun z hz => (haT (hz ▸ z.2)).elim,fun z hz => (hbT (hz ▸ z.2)).elim⟩
        exact ((Finset.card_pos (s := R z.1)).1 (by have := hRtwo z.1 (hTsub z.2); omega)).choose_spec
    obtain ⟨c,hc,hca,hcb⟩ := hpiece
    exact ⟨c.comp φ.toHom,fun z => hc (φ z),fun z hz => hca (φ z) hz,fun z hz => hcb (φ z) hz⟩
  let cR : (G.induce S).Coloring C := (G.induce S).homOfConnectedComponents (fun K => (hcomponent K).choose)
  have hcR : ∀ z : S, cR z ∈ R z.1 := fun z =>
    (hcomponent ((G.induce S).connectedComponentMk z)).choose_spec.1
      ⟨z,ConnectedComponent.connectedComponentMk_mem⟩
  have hcaR : cR ⟨a,haS⟩ = ta :=
    (hcomponent ((G.induce S).connectedComponentMk ⟨a,haS⟩)).choose_spec.2.1
      ⟨⟨a,haS⟩,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  have hcbR : cR ⟨b,hbS⟩ = tb :=
    (hcomponent ((G.induce S).connectedComponentMk ⟨b,hbS⟩)).choose_spec.2.2
      ⟨⟨b,hbS⟩,ConnectedComponent.connectedComponentMk_mem⟩ rfl
  let f : V → C := fun z => if hz : z = x then t else cR ⟨z,by simpa only [S,Set.mem_compl_iff,Set.mem_singleton_iff] using hz⟩
  refine ⟨Coloring.mk f ?_,?_,?_,?_⟩
  · intro z w hzw
    by_cases hz : z = x
    · subst z
      have hw : w ≠ x := hzw.ne.symm
      have h := ((hRmem w _).1 (hcR ⟨w,hw⟩)).2 hzw.symm
      simpa only [f,dite_eq_left rfl,dite_eq_right hw] using h.symm
    · by_cases hw : w = x
      · subst w
        have h := ((hRmem z _).1 (hcR ⟨z,hz⟩)).2 hzw
        simpa only [f,dite_eq_left rfl,dite_eq_right hz] using h
      · simpa only [f,dite_eq_right hz,dite_eq_right hw] using
          (show cR ⟨z,hz⟩ ≠ cR ⟨w,hw⟩ from cR.valid hzw)
  · intro z
    change f z ∈ L z
    by_cases hz : z = x
    · subst z; simpa only [f,dite_eq_left rfl] using htx
    · simpa only [f,dite_eq_right hz] using ((hRmem z _).1 (hcR ⟨z,hz⟩)).1
  · change f a = ta
    simpa only [f,dite_eq_right hxa.symm] using hcaR
  · change f b = tb
    simpa only [f,dite_eq_right hxb.symm] using hcbR

end Thomassen
