/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeCutPrecolor
public import Thomassen.PrescribedChordReduction

/-! Strict induction across prescribed edges without a one-sided prescription. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Edge coverage and the exact two-endpoint intersection give side constancy
for every edge avoiding both separator vertices. -/
lemma edge_cut_side_constancy (S T : Set V) (a b : V)
    (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S) := by
  intro x y hxy hxa hxb hya hyb
  rcases hedges hxy with hS | hT
  · exact iff_of_true hS.1 hS.2
  · have hx : x ∉ S := by
      intro hx
      have h : x ∈ ({a, b} : Set V) := hinter ▸ (show x ∈ S ∩ T from ⟨hx, hT.1⟩)
      exact h.elim hxa (fun h => hxb (Set.mem_singleton_iff.1 h))
    have hy : y ∉ S := by
      intro hy
      have h : y ∈ ({a, b} : Set V) := hinter ▸ (show y ∈ S ∩ T from ⟨hy, hT.2⟩)
      exact h.elim hya (fun h => hyb (Set.mem_singleton_iff.1 h))
    exact iff_of_false hx hy

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Complete two-piece induction when both ends of the separator edge are
prescribed. The exact native prescription is constructed independently on each
piece; no assumption places all remaining prescribed vertices in one side. -/
theorem colourable_of_prescribed_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (hab : G.Adj a b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∈ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Connected) (hTconn : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hB : ({a, b} : Set V) ⊆ S ∩ T := fun _ hx => hinter.symm ▸ hx
  have haS := (hB (Or.inl rfl)).1
  have hbS := (hB (Or.inr (Set.mem_singleton _))).1
  have haT := (hB (Or.inl rfl)).2
  have hbT := (hB (Or.inr (Set.mem_singleton _))).2
  let : Nontrivial S := (show (G.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ from hab).nontrivial
  let : Nontrivial T := (show (G.induce T).Adj ⟨a, haT⟩ ⟨b, hbT⟩ from hab).nontrivial
  have he : s(a, b) ∈ I.precolor.edges :=
    I.short_edges hab (by simp [I.singleton a haP]) (by simp [I.singleton b hbP])
  obtain ⟨QS, hQSv, hQSe⟩ := I.precolor.exists_induce_edge_cut haS hbS he
    (edge_cut_side_constancy S T a b hinter hedges)
  have hinterT : T ∩ S = {a, b} := by rw [Set.inter_comm]; exact hinter
  obtain ⟨QT, hQTv, hQTe⟩ := I.precolor.exists_induce_edge_cut haT hbT he
    (edge_cut_side_constancy T S a b hinterT (fun {_ _} h => (hedges h).symm))
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S)
    (I.inducePrecolor S hSconn.preconnected QS hQSv hQSe) hSsmall
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T)
    (I.inducePrecolor T hTconn.preconnected QT hQTv hQTe) hTsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcS
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcT
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have h : x ∈ ({a, b} : Set V) := hinter ▸ (show x ∈ S ∩ T from ⟨hx, hy⟩)
    have hxP : x ∈ I.precolor.vertices := h.elim (fun h => h ▸ haP)
      (fun h => (Set.mem_singleton_iff.1 h) ▸ hbP)
    have hSc : cS ⟨x, hx⟩ = I.prescribed x :=
      Finset.mem_singleton.1 (by simpa only [I.singleton x hxP] using hS ⟨x, hx⟩)
    have hTc : cT ⟨x, hy⟩ = I.prescribed x :=
      Finset.mem_singleton.1 (by simpa only [I.singleton x hxP] using hT ⟨x, hy⟩)
    exact hSc.trans hTc.symm

/-- The facial-chord reduction for arbitrary placement of the remaining
prescription, when both chord endpoints are prescribed. -/
theorem colourable_of_prescribed_facial_chord_general (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hArc : IsFacialWalkArc I.embedding p hp)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (haP : a ∈ I.precolor.vertices) (hbP : p.penultimate ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSconn, hTconn,
    _, _, _, _⟩ := facial_walk_chord_separation I.embedding I.outer hconn p hp hArc hroot houtside
  exact I.colourable_of_prescribed_edge_cut S T (p.adj_penultimate hp.not_nil).symm
    haP hbP hcover hinter hedges hSconn hTconn hSsmall hTsmall hsmall

end BoundaryInstance
end Thomassen
