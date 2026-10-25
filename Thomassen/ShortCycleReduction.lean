/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Thomassen.ConnectedInstance

/-! The separating short-cycle case of the list-extension induction. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} [Fintype V] {G : SimpleGraph V}

/-- A separating cycle of at most six vertices cannot occur in a smallest
counterexample to boundary extension. All geometric cuts and changed list
conditions are proved; induction is used only on strictly smaller graphs. -/
theorem colourable_of_separating_short_cycle (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hbound : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates I.embedding p hp)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  classical
  obtain ⟨S, T, hSsmall, hTsmall, houter, hcover, hinter, hedges, hSconn, hTconn,
    ⟨oS, _⟩, ⟨oT, hTface⟩⟩ :=
    short_native_cycle_proper_cut I.embedding I.outer I.girth hconn p hp hbound hsep
  let : Nontrivial S := oS.adj.nontrivial
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ S := fun x hx => houter x (I.on_outer x hx)
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) (I.induceConnected S hSconn.preconnected hP) hSsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by
    simpa only [induceConnected, inducePrecolor] using hcS
  have hcycle : ∀ x, x ∈ p.support → x ∈ S ∧ x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h
  have hprivate : ∀ x : T, x.1 ∉ p.support → 3 ≤ (I.lists x.1).card := by
    intro x hx
    apply I.interior_lists
    intro hf
    have h : x.1 ∈ S ∩ T := ⟨houter x.1 hf, x.2⟩
    rw [hinter] at h
    exact hx h
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x, hx⟩ else I.prescribed x
  have hfS : ∀ x : S, f x.1 = cS x := by intro x; simp only [f, dite_eq_left x.2]
  let P : BoundaryPrecolor G := .cycle p hp hbound
  have hPT : ∀ x ∈ P.vertices, x ∈ T := fun x hx =>
    (hcycle x (List.mem_toFinset.1 hx)).2
  let Q := P.induce T hPT
  have hQv : ∀ x : T, x ∈ Q.vertices ↔ x.1 ∈ p.support := by
    intro x
    simpa only [P, BoundaryPrecolor.vertices, List.mem_toFinset] using
      BoundaryPrecolor.mem_vertices_induce P T hPT x
  let L : T → Finset C := fun x => if x.1 ∈ p.support then {f x.1} else I.lists x.1
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hlength : p.length ≤ 6 := by rwa [cycle_support_card_eq_length p hp] at hbound
  have hch := short_cycle_isChordless I.girth (walk_isCycleMap p hp) hlen hlength
  let J : BoundaryInstance (G.induce T) C := {
    girth := five_le_egirth_induce T I.girth
    embedding := inducedPlaneMap I.embedding T
    outer := oT
    precolor := Q
    lists := L
    prescribed := fun x => f x.1
    on_outer := fun x hx => (hTface x).2 ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have heP := (BoundaryPrecolor.mem_edges_induce P T hPT x y).1 he
      have hends := P.endpoints_of_mem_edges heP
      have hx := (hcycle x.1 (List.mem_toFinset.1 hends.1)).1
      have hy := (hcycle y.1 (List.mem_toFinset.1 hends.2)).1
      have hxy := Q.adj_of_mem_edges he
      simpa only [f, dite_eq_left hx, dite_eq_left hy] using
        cS.valid (show (G.induce S).Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩ from hxy)
    boundary_lists := by
      intro x hx hxp
      exact (hxp ((hQv x).2 ((hTface x).1 hx))).elim
    interior_lists := by
      intro x hx
      have hxc : x.1 ∉ p.support := fun h => hx ((hTface x).2 h)
      simpa only [L, ite_eq_right hxc] using hprivate x hxc
    short_edges := by
      intro x y hxy hx hy
      have hxc : x.1 ∈ p.support := by
        by_contra h
        have hcard := hprivate x h
        simp only [L, ite_eq_right h] at hx
        omega
      have hyc : y.1 ∈ p.support := by
        by_contra h
        have hcard := hprivate y h
        simp only [L, ite_eq_right h] at hy
        omega
      apply (BoundaryPrecolor.mem_edges_induce P T hPT x y).2
      apply List.mem_toFinset.2
      apply (walkCycleVertices_edges p hp x.1 y.1).1
      apply cyclicSubgraph_of_chordless hch
      · rwa [walkCycleVertices_range p hp]
      · rwa [walkCycleVertices_range p hp]
      · exact hxy }
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) J hTsmall
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    intro x
    have hx : cT x ∈ L x := hcT x
    by_cases hxc : x.1 ∈ p.support
    · have heq : cT x = f x.1 := Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hxc] using hx)
      rw [heq, hfS ⟨x.1, (hcycle x.1 hxc).1⟩]
      exact hS ⟨x.1, (hcycle x.1 hxc).1⟩
    · simpa only [L, ite_eq_right hxc] using hx
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have hxc : x ∈ p.support := by
      have h : x ∈ S ∩ T := ⟨hx, hy⟩
      rwa [hinter] at h
    have ht : cT ⟨x, hy⟩ ∈ L ⟨x, hy⟩ := hcT ⟨x, hy⟩
    have heq : cT ⟨x, hy⟩ = f x := Finset.mem_singleton.1 (by simpa only [L, ite_eq_left hxc] using ht)
    exact ((hfS ⟨x, hx⟩).symm.trans heq.symm)

end Thomassen.BoundaryInstance
