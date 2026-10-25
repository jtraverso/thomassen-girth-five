/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OuterSevenCycle
public import Thomassen.OriginalCorollary

/-! Ring extension and gluing for the original exceptional-edge induction.
The original boundary lists may have size two. The exterior colouring is
retained exactly; only the uncoloured interior needs three-lists. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A precolouring extension theorem for full three-lists automatically permits
arbitrary original lists on the prescribed set. Enlarge only those lists with
a three-colour palette from an unprescribed vertex; the fixed colours restore
the originals. If every vertex is prescribed, the given colouring suffices. -/
theorem transfer_extension_to_prescribed_lists (P : Set V) (L : V → Finset C) (f : V → C)
    (hf : ∀ x ∈ P, f x ∈ L x)
    (hproper : ∀ x ∈ P, ∀ y ∈ P, G.Adj x y → f x ≠ f y)
    (hL : ∀ x, x ∉ P → 3 ≤ (L x).card)
    (hext : ∀ L' : V → Finset C, (∀ x, 3 ≤ (L' x).card) →
      (∀ x ∈ P, f x ∈ L' x) →
      ∃ c : G.Coloring C, (∀ x, c x ∈ L' x) ∧ ∀ x ∈ P, c x = f x) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ P, c x = f x := by
  by_cases hout : ∃ w, w ∉ P
  · obtain ⟨w,hw⟩ := hout
    let L' : V → Finset C := fun x => if x ∈ P then L x ∪ L w else L x
    obtain ⟨c,hc,hfixed⟩ := hext L' (by
      intro x
      by_cases hx : x ∈ P
      · simp only [L',ite_eq_left hx]
        exact (hL w hw).trans (Finset.card_le_card Finset.subset_union_right)
      · simpa only [L',ite_eq_right hx] using hL x hx) (by
      intro x hx
      simp only [L',ite_eq_left hx]
      exact Finset.mem_union_left _ (hf x hx))
    refine ⟨c,?_,hfixed⟩
    intro x
    by_cases hx : x ∈ P
    · rw [hfixed x hx]; exact hf x hx
    · simpa only [L',ite_eq_right hx] using hc x
  · have hall : ∀ x, x ∈ P := by simpa only [not_exists,not_not] using hout
    exact ⟨Coloring.mk f (fun {x y} hxy => hproper x (hall x) y (hall y) hxy),
      fun x => hf x (hall x),fun _ _ => rfl⟩

/-- Outer cycles of length at most seven extend even with arbitrary lists on
the already coloured cycle. This permits old two-lists at a separator in the
original Theorem 2.1 argument. No interior colourability assumption is supplied. -/
theorem extend_outer_ring_of_interior_three_lists [Finite V]
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 7)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, x ∉ p.support → 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  have hch : p.IsChordless := by
    let : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    have hc := cycle_isChordless_of_length_le_seven hg (walk_isCycleMap p hp) hp.three_le_length hlen
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    exact (walkCycleVertices_edges p hp x y).1
      (cyclicSubgraph_of_chordless hc (by rwa [walkCycleVertices_range p hp])
        (by rwa [walkCycleVertices_range p hp]) hxy)
  apply transfer_extension_to_prescribed_lists {x | x ∈ p.support} L f hf
    (fun x hx y hy hxy => hproper (hch.mem_edges hx hy hxy)) hL
  intro L' hL' hf'
  by_cases hshort : p.length ≤ 6
  · exact extend_outer_short_cycle M outer hg p hp hshort hface L' hL' f hf' hproper
  · exact extend_outer_seven_cycle M outer hg p hp (by omega) hface L' hL' f hf' hproper

/-- Colour the interior of an actual separating ring of at most seven vertices
and keep every already coloured exterior vertex fixed. The original exterior
lists may include the exceptional two-list edge. Only the interior off the ring
needs lists of size three. The geometric separation and existing exterior
colouring are explicit inputs, as required for applying this in a strict
minimal-counterexample induction. -/
theorem extend_exterior_across_short_ring [Fintype V]
    (S T : Set V) (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hg : 5 ≤ G.egirth) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length ≤ 7)
    (hinter : S ∩ T = {x | x ∈ p.support})
    (M : PlaneMap (G.induce T)) (outer : (G.induce T).Dart)
    (hface : ∀ x : T, x.1 ∈ p.support → OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x : T, x.1 ∉ p.support → 3 ≤ (L x.1).card)
    (cS : (G.induce S).Coloring C) (hcS : ∀ x : S, cS x ∈ L x.1) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x : S, c x.1 = cS x := by
  have hPS : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h.1
  have hPT : ∀ x ∈ p.support, x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h.2
  let q := p.induce T hPT
  have hq : q.IsCycle := Walk.IsCycle.of_map (f := (Embedding.induce T).toHom) (by
    change ((p.induce T hPT).map (Embedding.induce T).toHom).IsCycle
    rw [Walk.map_induce]
    exact hp)
  have hqlen : q.length = p.length := by
    rw [← Walk.length_map (Embedding.induce T).toHom,Walk.map_induce]
    rfl
  have hqmem : ∀ x : T, x ∈ q.support ↔ x.1 ∈ p.support := by
    intro x; simp only [q,Walk.support_induce,List.mem_attachWith]
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x,hx⟩ else cS ⟨a,hPS a p.start_mem_support⟩
  have hfS : ∀ x : S, f x.1 = cS x := fun x => dite_eq_left x.2
  obtain ⟨cT,hcT,hfixedT⟩ := extend_outer_ring_of_interior_three_lists M outer
    (five_le_egirth_induce T hg) q hq (by omega)
    (fun x hx => hface x ((hqmem x).1 hx)) (fun x : T => L x.1)
    (fun x hx => hL x (fun h => hx ((hqmem x).2 h))) (fun x : T => f x.1) (by
      intro x hx
      have hxS := hPS x.1 ((hqmem x).1 hx)
      rw [hfS ⟨x.1,hxS⟩]
      exact hcS ⟨x.1,hxS⟩) (by
      intro x y hxy
      have hxS := hPS x.1 ((hqmem x).1 (q.fst_mem_support_of_mem_edges hxy))
      have hyS := hPS y.1 ((hqmem y).1 (q.snd_mem_support_of_mem_edges hxy))
      rw [hfS ⟨x.1,hxS⟩,hfS ⟨y.1,hyS⟩]
      exact cS.valid (show (G.induce S).Adj ⟨x.1,hxS⟩ ⟨y.1,hyS⟩ from q.adj_of_mem_edges hxy))
  have hTfixed : ∀ (x : T) (hx : x.1 ∈ S), cT x = cS ⟨x.1,hx⟩ := by
    intro x hx
    have hpX : x.1 ∈ p.support := by have h : x.1 ∈ S ∩ T := ⟨hx,x.2⟩; rwa [hinter] at h
    exact (hfixedT x ((hqmem x).2 hpX)).trans (hfS ⟨x.1,hx⟩)
  let L' : V → Finset C := fun x => if hx : x ∈ S then {cS ⟨x,hx⟩} else L x
  obtain ⟨c,hc⟩ := glue_induced_colourings S T L' (by intro x; have h := Set.mem_univ x; rwa [← hcover] at h)
    hedges cS cT (by intro x; simp only [L',dite_eq_left x.2,Finset.mem_singleton]) (by
      intro x
      by_cases hx : x.1 ∈ S
      · simp only [L',dite_eq_left hx,Finset.mem_singleton]
        exact hTfixed x hx
      · simpa only [L',dite_eq_right hx] using hcT x) (by
      intro x hx hy
      exact (hTfixed ⟨x,hy⟩ hx).symm)
  have hfixed : ∀ x : S, c x.1 = cS x := by
    intro x
    simpa only [L',dite_eq_left x.2,Finset.mem_singleton] using hc x.1
  refine ⟨c,?_,hfixed⟩
  intro x
  by_cases hx : x ∈ S
  · rw [hfixed ⟨x,hx⟩]; exact hcS ⟨x,hx⟩
  · simpa only [L',dite_eq_right hx] using hc x

end Thomassen
