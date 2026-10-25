/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ChordSeparation
public import Thomassen.ConnectedInstance

/-! Induction across a prescribed chord with the old prescription on one side. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- Cut along an already prescribed edge, when all other prescribed vertices
are retained in the second piece. The first piece has exactly that native edge
as its prescribed path. No changed-list or extension hypothesis is assumed. -/
theorem colourable_of_prescribed_edge_separation (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (hab : G.Adj a b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∈ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Connected) (hTconn : (G.induce T).Connected)
    (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  classical
  have hB : ({a, b} : Set V) ⊆ S ∩ T := fun _ hx => hinter.symm ▸ hx
  have haS := (hB (Or.inl rfl)).1
  have hbS := (hB (Or.inr (Set.mem_singleton _))).1
  have haT := (hB (Or.inl rfl)).2
  have hbT := (hB (Or.inr (Set.mem_singleton _))).2
  have hSedge : (G.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hab
  have hTedge : (G.induce T).Adj ⟨a, haT⟩ ⟨b, hbT⟩ := hab
  let : Nontrivial S := hSedge.nontrivial
  let : Nontrivial T := hTedge.nontrivial
  let P : BoundaryPrecolor G := .path (.cons hab .nil)
    (by simp [Walk.isPath_def, hab.ne]) (by simp [hab.ne])
  have hPv : ∀ x, x ∈ P.vertices ↔ x = a ∨ x = b := by
    intro x
    simp only [P, BoundaryPrecolor.vertices, Walk.support_cons, Walk.support_nil,
      List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]
  have hPS : ∀ x ∈ P.vertices, x ∈ S := fun x hx => by
    rcases (hPv x).1 hx with rfl | rfl
    · exact haS
    · exact hbS
  have hvertices : ∀ x : S, x.1 ∈ P.vertices ↔ x.1 ∈ I.precolor.vertices := by
    intro x
    rw [hPv]
    constructor
    · rintro (h | h)
      · exact h ▸ haP
      · exact h ▸ hbP
    · intro hxP
      have hx : x.1 ∈ S ∩ T := ⟨x.2, hP x.1 hxP⟩
      rw [hinter] at hx
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have hedge_equiv : ∀ x y : S, s(x.1, y.1) ∈ P.edges ↔ s(x.1, y.1) ∈ I.precolor.edges := by
    intro x y
    constructor
    · intro h
      have hends := P.endpoints_of_mem_edges h
      have hxP := (hvertices x).1 hends.1
      have hyP := (hvertices y).1 hends.2
      exact I.short_edges (P.adj_of_mem_edges h)
        (by simp [I.singleton x.1 hxP]) (by simp [I.singleton y.1 hyP])
    · intro h
      have hends := I.precolor.endpoints_of_mem_edges h
      have hx := (hPv x.1).1 ((hvertices x).2 hends.1)
      have hy := (hPv y.1).1 ((hvertices y).2 hends.2)
      have hxy := I.precolor.adj_of_mem_edges h
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact (hxy.ne (hx.trans hy.symm)).elim
      · simp only [P, BoundaryPrecolor.edges, Walk.edges_cons, Walk.edges_nil,
          List.toFinset_cons, List.toFinset_nil, hx, hy, Finset.mem_insert, true_or]
      · simp only [P, BoundaryPrecolor.edges, Walk.edges_cons, Walk.edges_nil,
          List.toFinset_cons, List.toFinset_nil, hx, hy, Sym2.eq_swap, Finset.mem_insert, true_or]
      · exact (hxy.ne (hx.trans hy.symm)).elim
  let Q := P.induce S hPS
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ I.precolor.vertices :=
    fun x => (BoundaryPrecolor.mem_vertices_induce P S hPS x).trans (hvertices x)
  have hQe : ∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ I.precolor.edges :=
    fun x y => (BoundaryPrecolor.mem_edges_induce P S hPS x y).trans (hedge_equiv x y)
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S)
    (I.inducePrecolor S hSconn.preconnected Q hQv hQe) hSsmall
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTconn.preconnected hP) hTsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcS
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    simpa only [induceConnected, inducePrecolor] using hcT
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have h : x ∈ S ∩ T := ⟨hx, hy⟩
    rw [hinter] at h
    have hxP : x ∈ I.precolor.vertices := by
      rcases h with h | h
      · exact h ▸ haP
      · exact (Set.mem_singleton_iff.1 h) ▸ hbP
    have hSc : cS ⟨x, hx⟩ = I.prescribed x :=
      Finset.mem_singleton.1 (by simpa only [I.singleton x hxP] using hS ⟨x, hx⟩)
    have hTc : cT ⟨x, hy⟩ = I.prescribed x :=
      Finset.mem_singleton.1 (by simpa only [I.singleton x hxP] using hT ⟨x, hy⟩)
    exact hSc.trans hTc.symm

/-- The complete facial-chord reduction when both ends are already prescribed
and no other prescribed vertex belongs to the arc being removed from the
exterior piece. The cut itself is obtained from the original face equations. -/
theorem colourable_of_prescribed_facial_chord (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hArc : IsFacialWalkArc I.embedding p hp)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (haP : a ∈ I.precolor.vertices) (hbP : p.penultimate ∈ I.precolor.vertices)
    (hPoutside : ∀ x ∈ I.precolor.vertices,
      x ∉ ({z | z ∈ p.support} \ {a, p.penultimate}))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSconn, hTconn,
    _, hkeep, _, _⟩ := facial_walk_chord_separation I.embedding I.outer hconn p hp hArc hroot houtside
  have hab : G.Adj a p.penultimate := (p.adj_penultimate hp.not_nil).symm
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ T :=
    fun x hx => hkeep x (I.on_outer x hx) (hPoutside x hx)
  exact I.colourable_of_prescribed_edge_separation S T hab haP hbP hcover hinter hedges
    hSconn hTconn hP hSsmall hTsmall hsmall

end Thomassen.BoundaryInstance
