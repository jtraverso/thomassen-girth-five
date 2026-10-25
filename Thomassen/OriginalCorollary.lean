/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryExtension

/-! The outer-cycle extension statement in the original 1995 paper. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- Any proper allowed colouring of an outer cycle of length five or six
extends. Only incidence with the chosen actual face is needed; the cycle need
not exhaust that face. This exposes the already proved boundary extension. -/
theorem extend_outer_short_cycle (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length ≤ 6)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  let : Fintype V := Fintype.ofFinite V
  have hbound : p.support.toFinset.card ≤ 6 := by
    rw [cycle_support_card_eq_length p hp]
    exact hlen
  have hch : p.IsChordless := by
    let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    have h := short_cycle_isChordless hg (walk_isCycleMap p hp) hp.three_le_length hlen
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    apply (walkCycleVertices_edges p hp x y).1
    exact cyclicSubgraph_of_chordless h
      (by rw [walkCycleVertices_range p hp]; exact hx)
      (by rw [walkCycleVertices_range p hp]; exact hy) hxy
  let L' : V → Finset C := fun x => if x ∈ p.support then {f x} else L x
  let I : BoundaryInstance G C := {
    girth := hg
    embedding := M
    outer := outer
    precolor := .cycle p hp hbound
    lists := L'
    prescribed := f
    on_outer := fun x hx => hface x (List.mem_toFinset.1 hx)
    singleton := fun x hx => ite_eq_left (List.mem_toFinset.1 hx)
    proper_precolor := fun {x y} hxy => hproper (List.mem_toFinset.1 hxy)
    boundary_lists := by
      intro x _ hx
      have hn : x ∉ p.support := fun h => hx (List.mem_toFinset.2 h)
      simp only [L',ite_eq_right hn]
      exact (by omega : 2 ≤ 3).trans (hL x)
    interior_lists := by
      intro x hx
      have hn : x ∉ p.support := fun h => hx (hface x h)
      simpa only [L',ite_eq_right hn] using hL x
    short_edges := by
      intro x y hxy hx hy
      have hxs : x ∈ p.support := by
        by_contra hn
        have := hL x
        simp only [L',ite_eq_right hn] at hx
        omega
      have hys : y ∈ p.support := by
        by_contra hn
        have := hL y
        simp only [L',ite_eq_right hn] at hy
        omega
      exact List.mem_toFinset.2 (hch.mem_edges hxs hys hxy) }
  obtain ⟨c,hc⟩ := boundary_extension C V G I
  have hfixed : ∀ x ∈ p.support, c x = f x := by
    intro x hx
    have h := hc x
    change c x ∈ L' x at h
    simpa only [L',ite_eq_left hx,Finset.mem_singleton] using h
  refine ⟨c,?_,hfixed⟩
  intro x
  by_cases hx : x ∈ p.support
  · rw [hfixed x hx]; exact hf x hx
  · have h := hc x
    change c x ∈ L' x at h
    simpa only [L',ite_eq_right hx] using h

/-- Thomassen (1995), Corollary 2.2: every proper list colouring of the
outer five-cycle extends to an allowed proper colouring of the whole graph.
The hypothesis `5 ≤ egirth` also admits forests, though the supplied cycle
forces the girth to be exactly five. -/
theorem original_corollary_2_2 (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hlen : p.length = 5)
    (hface : ∀ x, OnOuterFace M outer x ↔ x ∈ p.support)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  exact extend_outer_short_cycle M outer hg p hp (by omega)
    (fun x hx => (hface x).2 hx) L hL f hf hproper

end Thomassen
