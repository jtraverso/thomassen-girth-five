/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundedPrescriptionCuts

/-! Extension of connected branching prescriptions below the main bound. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace ConnectedPrescription

/-- On a simple facial boundary, split each prescribed chord using the actual
strict face cut. Once no such chord remains, the prescribed graph has maximum
degree two, and the bounded-path lemma gives a valid native main instance. -/
theorem colourable_of_facial_boundary (I : ConnectedPrescription G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  by_cases hex : ∃ i j : ZMod k, c i ∈ I.vertices ∧ c j ∈ I.vertices ∧
      G.Adj (c i) (c j) ∧ j ≠ i+1 ∧ i ≠ j+1
  · obtain ⟨i,j,hiP,hjP,hij,hf,hb⟩ := hex
    obtain ⟨S,T,hScard,hTcard,hcover,hinter,hedges,hS,hT⟩ :=
      full_face_chord_separation_at I.embedding hc hk hface hG i j hij hf hb
    have hi : c i ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
    have hj : c j ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
    let : Nontrivial S := (show (G.induce S).Adj ⟨c i,hi.1⟩ ⟨c j,hj.1⟩ from hij).nontrivial
    let : Nontrivial T := (show (G.induce T).Adj ⟨c i,hi.2⟩ ⟨c j,hj.2⟩ from hij).nontrivial
    apply I.colourable_of_clique_cut S T hcover hedges ?_ ?_ ⟨c i,hi⟩
      hS.preconnected hT.preconnected hScard hTcard hrec
    · intro x hx y hy hxy
      rw [hinter] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact hij
      · exact hij.symm
      · exact (hxy rfl).elim
    · intro x hx
      rw [hinter] at hx
      rcases hx with rfl | rfl
      · exact hiP
      · exact hjP
  · have hcycle : ∀ {x y}, x ∈ I.vertices → y ∈ I.vertices → G.Adj x y →
        (cyclicSubgraph G c).Adj x y := by
      intro x y hx hy hxy
      obtain ⟨i,hi⟩ := hrange x (I.on_outer x hx)
      obtain ⟨j,hj⟩ := hrange y (I.on_outer y hy)
      subst x; subst y
      have hcon : j = i+1 ∨ i = j+1 := by
        by_contra h
        push Not at h
        exact hex ⟨i,j,hx,hy,hxy,h.1,h.2⟩
      apply (cyclicSubgraph_adj_at_iff hc i _).2
      rcases hcon with h | h
      · exact Or.inl (congrArg c h)
      · exact Or.inr (congrArg c (by linear_combination -h))
    obtain ⟨Q,hQv,hQe⟩ := exists_native_precolor_of_connected_degree_two I.vertices I.connected
      I.paths_short (by
        intro x hx r hr s hs t ht hxr hxs hxt hrs
        obtain ⟨i,hi⟩ := hrange x (I.on_outer x hx)
        exact cyclicSubgraph_third_neighbour hc i (by rw [hi]; exact hcycle hx hr hxr)
          (by rw [hi]; exact hcycle hx hs hxs) (by rw [hi]; exact hcycle hx ht hxt) hrs)
    exact hsmall V G (I.toBoundaryInstance Q hQv hQe) hN

end ConnectedPrescription

/-- A connected branching prescription whose every simple path has at most six
vertices extends below the strict main induction bound. The complete auxiliary
strong induction handles all cutvertices and prescribed chords; its base invokes
the main induction only on graphs of cardinality strictly less than `N`. -/
theorem connectedPrescription_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : ConnectedPrescription G C)
    (hG : G.Preconnected) (hN : Nat.card V < N) : ListColourable G I.lists := by
  have haux : ∀ n, ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W = n → n < N → ListColourable H J.lists := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H J hH hn hnN
      let : Fintype W := Fintype.ofFinite W
      have hrec : ∀ (W' : Type u) [Finite W'] (H' : SimpleGraph W') (K : ConnectedPrescription H' C),
          H'.Preconnected → Nat.card W' < Nat.card W → ListColourable H' K.lists := by
        intro W' _ H' K hH' hcard
        exact ih (Nat.card W') (by omega) W' H' K hH' rfl (by omega)
      by_cases hcard : 3 ≤ Nat.card W
      · by_cases hdelete : ∀ z, (H.induce ({z} : Set W)ᶜ).Preconnected
        · have hdeg := two_le_card_neighbours_of_delete_preconnected hH hcard hdelete
          let c := faceOrbitVertex J.embedding J.outer
          let k := faceOrbitLength J.embedding J.outer
          have hk : 3 ≤ k := faceOrbitLength_three_le J.embedding hdeg J.outer
          let : NeZero k := ⟨by omega⟩
          have hc : IsCycleMap H c := faceOrbitVertex_isCycleMap J.embedding J.outer (by omega) hdelete
          exact J.colourable_of_facial_boundary hH hc hk
            (faceOrbitVertex_isFacial J.embedding J.outer (by omega) hdelete)
            (fun x hx => by rw [faceOrbitVertex_range]; exact hx)
            N (by omega) hsmall hrec
        · push Not at hdelete
          obtain ⟨z,hz⟩ := hdelete
          exact J.colourable_of_cutvertex hH z hz N (by omega) hsmall hrec
      · obtain ⟨Q,hQv,hQe⟩ := exists_native_precolor_of_connected_degree_two J.vertices J.connected
          J.paths_short (by
            intro x hx r hr s hs t ht hxr hxs hxt hrs
            have hpair : ({r,s} : Finset W) = Finset.univ := by
              apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
              rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Finset.card_pair hrs]
              omega
            have ht : t ∈ ({r,s} : Finset W) := by rw [hpair]; exact Finset.mem_univ _
            simpa only [Finset.mem_insert, Finset.mem_singleton] using ht)
        exact hsmall W H (J.toBoundaryInstance Q hQv hQe) (by omega)
  exact haux (Nat.card V) V G I hG rfl hN

end Thomassen
