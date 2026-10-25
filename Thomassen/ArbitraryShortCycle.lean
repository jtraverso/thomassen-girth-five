/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalCorollary

/-! Any five/six-cycle can be precoloured, including separating cycles.
Thomassen (1995), abstract and Corollary 2.2; the six-cycle version follows from
the already proved short-boundary extension and the same two-side gluing. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- Extend a prescribed short-cycle colouring in a connected plane graph by
colouring its two actual induced sides and gluing on the common cycle. -/
theorem extend_short_cycle_of_preconnected (M : PlaneMap G) (hG : G.Preconnected)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 6)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  let : Fintype V := Fintype.ofFinite V
  have hbound : p.support.toFinset.card ≤ 6 := by rw [cycle_support_card_eq_length p hp]; exact hlen
  obtain ⟨S,T,hcover,hinter,hedges,hSconn,hTconn,⟨oS,hSface⟩,⟨oT,hTface⟩⟩ :=
    short_native_cycle_separation M hg hG p hp hbound
  have hPS : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h.1
  have hPT : ∀ x ∈ p.support, x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h.2
  have hside : ∀ U : Set V, (∀ x ∈ p.support, x ∈ U) →
      ∀ o : (G.induce U).Dart,
      (∀ x : U, OnOuterFace (inducedPlaneMap M U) o x ↔ x.1 ∈ p.support) →
      ∃ c : (G.induce U).Coloring C, (∀ x, c x ∈ L x.1) ∧
        ∀ x : U, x.1 ∈ p.support → c x = f x.1 := by
    intro U hPU o hface
    let q := p.induce U hPU
    have hq : q.IsCycle := Walk.IsCycle.of_map (f := (Embedding.induce U).toHom)
      (by
        change ((p.induce _ _).map (Embedding.induce _).toHom).IsCycle
        rw [Walk.map_induce]
        exact hp)
    have hqmem : ∀ x : U, x ∈ q.support ↔ x.1 ∈ p.support := by
      intro x
      simp only [q,Walk.support_induce,List.mem_attachWith]
    have hqLen : q.length = p.length := by
      rw [← Walk.length_map (Embedding.induce U).toHom,Walk.map_induce]
      rfl
    have hch : p.IsChordless := by
      let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
      have hc := short_cycle_isChordless hg (walk_isCycleMap p hp) hp.three_le_length hlen
      apply Walk.isChordless_iff_forall_mem_edges.2
      intro x y hx hy hxy
      exact (walkCycleVertices_edges p hp x y).1
        (cyclicSubgraph_of_chordless hc (by rwa [walkCycleVertices_range p hp])
          (by rwa [walkCycleVertices_range p hp]) hxy)
    obtain ⟨c,hc,hfixed⟩ := extend_outer_short_cycle (inducedPlaneMap M U) o
      (five_le_egirth_induce U hg) q hq (by omega)
      (fun x hx => (hface x).2 ((hqmem x).1 hx)) (fun x : U => L x.1) (fun x => hL x.1)
      (fun x : U => f x.1) (fun x hx => hf x.1 ((hqmem x).1 hx)) (by
        intro x y hxy
        have hx : x.1 ∈ p.support := (hqmem x).1 (q.fst_mem_support_of_mem_edges hxy)
        have hy : y.1 ∈ p.support := (hqmem y).1 (q.snd_mem_support_of_mem_edges hxy)
        exact hproper (hch.mem_edges hx hy (q.adj_of_mem_edges hxy)))
    exact ⟨c,hc,fun x hx => hfixed x ((hqmem x).2 hx)⟩
  obtain ⟨cS,hcS,hfixedS⟩ := hside S hPS oS hSface
  obtain ⟨cT,hcT,hfixedT⟩ := hside T hPT oT hTface
  let L' : V → Finset C := fun x => if x ∈ p.support then {f x} else L x
  have hmemS : ∀ x : S, cS x ∈ L' x.1 := by
    intro x
    by_cases hx : x.1 ∈ p.support
    · simp only [L',ite_eq_left hx,Finset.mem_singleton]; exact hfixedS x hx
    · simpa only [L',ite_eq_right hx] using hcS x
  have hmemT : ∀ x : T, cT x ∈ L' x.1 := by
    intro x
    by_cases hx : x.1 ∈ p.support
    · simp only [L',ite_eq_left hx,Finset.mem_singleton]; exact hfixedT x hx
    · simpa only [L',ite_eq_right hx] using hcT x
  obtain ⟨c,hc⟩ := glue_induced_colourings S T L' (by intro x; have h := Set.mem_univ x; rwa [← hcover] at h)
    hedges cS cT hmemS hmemT (by
      intro x hx hy
      have hpX : x ∈ p.support := by have h : x ∈ S ∩ T := ⟨hx,hy⟩; rwa [hinter] at h
      exact (hfixedS ⟨x,hx⟩ hpX).trans (hfixedT ⟨x,hy⟩ hpX).symm)
  have hfixed : ∀ x ∈ p.support, c x = f x := by
    intro x hx
    simpa only [L',ite_eq_left hx,Finset.mem_singleton] using hc x
  refine ⟨c,?_,hfixed⟩
  intro x
  by_cases hx : x ∈ p.support
  · rw [hfixed x hx]; exact hf x hx
  · simpa only [L',ite_eq_right hx] using hc x

/-- The arbitrary-cycle extension: the prescribed five/six-cycle need not be
facial or bound the unbounded face, and other connected components are allowed. -/
theorem extend_any_short_cycle (M : PlaneMap G) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 6)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  let : Fintype V := Fintype.ofFinite V
  let S : Set V := {x | G.Reachable a x}
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := fun _ hx _ hxy => hx.trans hxy.reachable
  have hconn : (G.induce S).Preconnected := by
    intro x y
    obtain ⟨q⟩ := x.2.symm.trans y.2
    exact ⟨q.induce S (fun z hz => x.2.trans (q.takeUntil z hz).reachable)⟩
  have hPS : ∀ x ∈ p.support, x ∈ S := fun x hx => (p.takeUntil x hx).reachable
  let q := p.induce S hPS
  have hq : q.IsCycle := Walk.IsCycle.of_map (f := (Embedding.induce S).toHom)
    (by
        change ((p.induce _ _).map (Embedding.induce _).toHom).IsCycle
        rw [Walk.map_induce]
        exact hp)
  have hqLen : q.length = p.length := by
    rw [← Walk.length_map (Embedding.induce S).toHom,Walk.map_induce]
    rfl
  have hqmem : ∀ x : S, x ∈ q.support ↔ x.1 ∈ p.support := by
    intro x; simp only [q,Walk.support_induce,List.mem_attachWith]
  obtain ⟨cS,hcS,hfixedS⟩ := extend_short_cycle_of_preconnected (inducedPlaneMap M S) hconn
    (five_le_egirth_induce S hg) q hq (by omega) (fun x : S => L x.1) (fun x => hL x.1)
    (fun x : S => f x.1) (fun x hx => hf x.1 ((hqmem x).1 hx)) (by
      intro x y hxy
      let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
      have hch := short_cycle_isChordless hg (walk_isCycleMap p hp) hp.three_le_length hlen
      have hx : x.1 ∈ p.support := (hqmem x).1 (q.fst_mem_support_of_mem_edges hxy)
      have hy : y.1 ∈ p.support := (hqmem y).1 (q.snd_mem_support_of_mem_edges hxy)
      exact hproper ((walkCycleVertices_edges p hp x.1 y.1).1
        (cyclicSubgraph_of_chordless hch (by rwa [walkCycleVertices_range p hp])
          (by rwa [walkCycleVertices_range p hp]) (q.adj_of_mem_edges hxy))))
  obtain ⟨cT,hcT⟩ := choosable_of_boundary_extension (boundary_extension C) (G.induce Sᶜ)
    ⟨inducedPlaneMap M Sᶜ⟩ (five_le_egirth_induce Sᶜ hg) (fun x => L x.1) (fun x => hL x.1)
  let g : V → C := fun x => if hx : x ∈ S then cS ⟨x,hx⟩ else cT ⟨x,hx⟩
  refine ⟨Coloring.mk g ?_,?_,?_⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · have hy := hclosed x hx y hxy
      simpa only [g,dite_eq_left hx,dite_eq_left hy] using
        (show cS ⟨x,hx⟩ ≠ cS ⟨y,hy⟩ from cS.valid hxy)
    · have hy : y ∉ S := fun hy => hx (hclosed y hy x hxy.symm)
      simpa only [g,dite_eq_right hx,dite_eq_right hy] using
        (show cT ⟨x,hx⟩ ≠ cT ⟨y,hy⟩ from cT.valid hxy)
  · intro x
    change g x ∈ L x
    by_cases hx : x ∈ S
    · simpa only [g,dite_eq_left hx] using hcS ⟨x,hx⟩
    · simpa only [g,dite_eq_right hx] using hcT ⟨x,hx⟩
  · intro x hx
    change g x = f x
    simpa only [g,dite_eq_left (hPS x hx)] using hfixedS ⟨x,hPS x hx⟩ ((hqmem _).2 hx)

end Thomassen
