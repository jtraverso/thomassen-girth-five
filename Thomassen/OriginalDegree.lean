/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalPathCuts

/-! Restoration of a low-degree vertex in the original exceptional induction. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- An unprescribed vertex with fewer neighbours than available colours is
restored after a strict original-instance deletion. The remainder is required
to be connected; this is already proved for every vertex of a minimal original
counterexample by the cutvertex reduction. -/
theorem extends_of_few_neighbours (I : OriginalBoundaryInstance G C)
    (x : V) (hxa : x ≠ I.a) (hxb : x ≠ I.b)
    (hconn : (G.induce ({x} : Set V)ᶜ).Preconnected)
    (hdegree : (Finset.univ.filter (G.Adj x)).card < (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  let S : Set V := ({x} : Set V)ᶜ
  have haS : I.a ∈ S := by simpa only [S,Set.mem_compl_iff,Set.mem_singleton_iff] using hxa.symm
  have hbS : I.b ∈ S := by simpa only [S,Set.mem_compl_iff,Set.mem_singleton_iff] using hxb.symm
  have hAdjS : (G.induce S).Adj ⟨I.a,haS⟩ ⟨I.b,hbS⟩ := I.edge
  let : Nontrivial S := hAdjS.nontrivial
  let J := I.induceWithEdge S hconn I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) J
    (card_induced_vertices_lt S (by simp [S] : x ∉ S))
  let f : V → C := fun z => if hz : z ∈ S then cS ⟨z,hz⟩ else I.ta
  have hfS : ∀ z : S, f z.1 = cS z := fun z => dite_eq_left z.2
  obtain ⟨tx,htx,htN⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt (Finset.card_image_le (f := f) (s := Finset.univ.filter (G.Adj x))) hdegree)
  have htne : ∀ y, G.Adj x y → tx ≠ f y := by
    intro y hxy he
    exact htN (he ▸ Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨Finset.mem_univ _,hxy⟩))
  let g : V → C := fun y => if y=x then tx else f y
  have hgx : g x = tx := ite_eq_left rfl
  have hgS : ∀ y : S, g y.1 = cS y := by
    intro y
    have hyx : y.1 ≠ x := y.2
    exact (ite_eq_right hyx).trans (hfS y)
  have hp : ∀ {r s}, G.Adj r s → g r ≠ g s := by
    intro r s hrs
    by_cases hr : r=x
    · subst r
      have hsS : s ∈ S := hrs.ne.symm
      rw [hgx,hgS ⟨s,hsS⟩,← hfS ⟨s,hsS⟩]
      exact htne s hrs
    · by_cases hs : s=x
      · subst s
        have hrS : r ∈ S := hr
        rw [hgS ⟨r,hrS⟩,hgx,← hfS ⟨r,hrS⟩]
        exact (htne r hrs.symm).symm
      · have hrS : r ∈ S := hr
        have hsS : s ∈ S := hs
        rw [hgS ⟨r,hrS⟩,hgS ⟨s,hsS⟩]
        exact cS.valid hrs
  refine ⟨Coloring.mk g hp,?_,(hgS ⟨I.a,haS⟩).trans hca,(hgS ⟨I.b,hbS⟩).trans hcb⟩
  intro y
  change g y ∈ I.lists y
  by_cases hy : y=x
  · subst y
    rw [hgx]; exact htx
  · rw [hgS ⟨y,hy⟩]
    exact hcS ⟨y,hy⟩

/-- In a minimal original counterexample, a nonfixed vertex has at least as
many neighbours as original list colours. In particular every nonfixed
three-list vertex has degree at least three. -/
theorem list_card_le_degree_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (x : V) (hxa : x ≠ I.a) (hxb : x ≠ I.b) :
    (I.lists x).card ≤ (Finset.univ.filter (G.Adj x)).card := by
  obtain ⟨_,_,hdel,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  by_contra hn
  exact hbad (I.extends_of_few_neighbours x hxa hxb (hdel x) (by omega) hsmall)

end Thomassen.OriginalBoundaryInstance
