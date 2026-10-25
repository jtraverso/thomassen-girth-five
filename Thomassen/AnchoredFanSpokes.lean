/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanCuts

/-! All spoke and prescribed-edge cuts in the anchored fan induction. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- Keep the old prescription in the root piece and solve the other spoke
piece by the complete two-endpoint fan theorem. -/
theorem anchoredFan_extension_of_one_sided_spoke (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hPS : ∀ y ∈ I.precolor.vertices, y ∈ S)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  have hbST : b ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hxST : x ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
  let : Nontrivial S := (show (G.induce S).Adj ⟨b, hbST.1⟩ ⟨x, hxST.1⟩ from hbx).nontrivial
  let : Nontrivial T := (show (G.induce T).Adj ⟨b, hbST.2⟩ ⟨x, hxST.2⟩ from hbx).nontrivial
  obtain ⟨a, haP, hba⟩ := ha
  obtain ⟨cS, hcS, hgS⟩ := I.anchoredFan_on_induced hcard b hbP hbface f hf hp S hSc.preconnected hbST.1
    ⟨a, hPS a haP, haP, hba⟩ (I.precolor.induce S hPS)
    (BoundaryPrecolor.mem_vertices_induce _ S hPS) (BoundaryPrecolor.mem_edges_induce _ S hPS) hSsmall hfan
  have hb3 : 3 ≤ (I.lists b).card := by
    by_contra h
    have he := I.short_edges hba (by omega) (by simp [I.singleton a haP])
    exact hbP (I.precolor.endpoints_of_mem_edges he).1
  have hxface : OnOuterFace I.embedding I.outer x := by
    by_contra h
    have h3 := I.interior_lists x h
    omega
  obtain ⟨cT, hcT, hgT⟩ := I.rootStar_on_released_spoke_piece b x hbx hxs hbface hxface hb3 f hf hp T hTc.preconnected
    hbST.2 hxST.2 (by
      intro y hy hyP
      have h : y ∈ S ∩ T := ⟨hPS y hyP, hy⟩
      rw [hinter] at h
      exact h.elim Or.inl (fun h => Or.inr (Set.mem_singleton_iff.1 h))) N (hTsmall.trans hN) hsmall
  apply I.rootStar_extension_of_induced_colourings b f hf S T
    (fun y => by have h := Set.mem_univ y; rwa [← hcover] at h) hedges cS cT hcS hcT hgS hgT
  intro y hyS hyT
  have hy : y ∈ S ∩ T := ⟨hyS, hyT⟩
  rw [hinter] at hy
  have hystar : y ∈ rootStar I b := by
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · have hyx := Set.mem_singleton_iff.1 hy
      subst y
      exact Or.inr ⟨hbx, hxs⟩
  exact (hgS ⟨y, hyS⟩ hystar).trans (hgT ⟨y, hyT⟩ hystar).symm

/-- Every short-neighbour spoke is cut, whether or not it meets or divides
the old prescription. Both original path branches keep their singleton colours. -/
theorem anchoredFan_extension_of_spoke_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  by_cases hxP : x ∈ I.precolor.vertices
  · exact I.anchoredFan_extension_of_prescribed_spoke_cut hcard b x hbP hxP hbx hbface f hf hp
      S T hcover hinter hedges hSc hTc hSsmall hTsmall hfan
  · rcases I.precolor.edge_cut_dichotomy_avoiding b x hbP hxP S
      (edge_cut_side_constancy S T b x hinter hedges) with hPS | hPS
    · exact I.anchoredFan_extension_of_one_sided_spoke hcard b x hbP ha hbx hxs hbface f hf hp
        S T hcover hinter hedges hSc hTc hPS hSsmall hTsmall N hN hsmall hfan
    · apply I.anchoredFan_extension_of_one_sided_spoke hcard b x hbP ha hbx hxs hbface f hf hp
        T S (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm)
        hTc hSc ?_ hTsmall hSsmall N hN hsmall hfan
      intro y hyP
      have hy : y ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ y
      exact hy.resolve_left (hPS y hyP)

/-- A cut along an original prescribed edge is also a strict anchored-fan
reduction. The root piece retains an actual prescribed neighbour of the root. -/
theorem anchoredFan_extension_of_prescribed_edge_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (r s : V) (hrs : G.Adj r s) (hrP : r ∈ I.precolor.vertices) (hsP : s ∈ I.precolor.vertices)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {r, s})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  have heP := I.short_edges hrs (by simp [I.singleton r hrP]) (by simp [I.singleton s hsP])
  have hdo : ∀ (U Z : Set V), U ∪ Z = Set.univ → U ∩ Z = {r, s} →
      (∀ {y z}, G.Adj y z → (y ∈ U ∧ z ∈ U) ∨ (y ∈ Z ∧ z ∈ Z)) →
      (G.induce U).Connected → (G.induce Z).Connected →
      Nat.card U < Nat.card V → Nat.card Z < Nat.card V → b ∈ U → RootStarExtension I b f := by
    intro U Z hcov hint he hcU hcZ hUs hZs hbU
    have hrUZ : r ∈ U ∩ Z := by rw [hint]; exact Or.inl rfl
    have hsUZ : s ∈ U ∩ Z := by rw [hint]; exact Or.inr rfl
    let : Nontrivial U := (show (G.induce U).Adj ⟨r, hrUZ.1⟩ ⟨s, hsUZ.1⟩ from hrs).nontrivial
    let : Nontrivial Z := (show (G.induce Z).Adj ⟨r, hrUZ.2⟩ ⟨s, hsUZ.2⟩ from hrs).nontrivial
    have hbZ : b ∉ Z := by
      intro h
      have h' : b ∈ U ∩ Z := ⟨hbU, h⟩
      rw [hint] at h'
      exact hbP (h'.elim (fun h => h ▸ hrP) (fun h => Set.mem_singleton_iff.1 h ▸ hsP))
    obtain ⟨a, haP, hba⟩ := ha
    have haU : a ∈ U := (he hba).elim And.right (fun h => (hbZ h.1).elim)
    obtain ⟨QU, hUv, hUe⟩ := I.precolor.exists_induce_edge_cut hrUZ.1 hsUZ.1 heP
      (edge_cut_side_constancy U Z r s hint he)
    obtain ⟨QZ, hZv, hZe⟩ := I.precolor.exists_induce_edge_cut hrUZ.2 hsUZ.2 heP
      (edge_cut_side_constancy Z U r s (by rwa [Set.inter_comm]) (fun {_ _} h => (he h).symm))
    apply I.anchoredFan_extension_of_prescribed_cut hcard b hbP hbface f hf hp U Z hbU hbZ
      ⟨a, haU, haP, hba⟩ hcov ?_ he hcU.preconnected hcZ.preconnected QU hUv hUe QZ hZv hZe hUs hZs N hN hsmall hfan
    intro y hy
    rw [hint] at hy
    exact hy.elim (fun h => h ▸ hrP) (fun h => Set.mem_singleton_iff.1 h ▸ hsP)
  by_cases hbS : b ∈ S
  · exact hdo S T hcover hinter hedges hSc hTc hSsmall hTsmall hbS
  · have hbT : b ∈ T := by
      have h : b ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ b
      exact h.resolve_left hbS
    exact hdo T S (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm)
      hTc hSc hTsmall hSsmall hbT

end BoundaryInstance
end Thomassen
