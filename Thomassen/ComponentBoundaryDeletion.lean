/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedInteriorTwoPath

/-! Actual faces of every component after a connected boundary deletion. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Flattened component vertices stay in the original induced vertex set. -/
lemma componentVertexSet_subset (S : Set V) (K : (G.induce S).ConnectedComponent) :
    componentVertexSet S K ⊆ S := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

/-- An edge between retained vertices stays in its retained component. -/
lemma componentVertexSet_adj_closed (S : Set V) (K : (G.induce S).ConnectedComponent)
    {x y : V} (hx : x ∈ componentVertexSet S K) (hy : y ∈ S) (hxy : G.Adj x y) :
    y ∈ componentVertexSet S K := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, K.mem_supp_of_adj_mem_supp hz (show (G.induce S).Adj z ⟨y, hy⟩ from hxy), rfl⟩

/-- Every forward edge of the native old face has the original face orbit. -/
lemma native_facial_step_sameCycle [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (i : ℕ) (hi : i < p.length) :
    SameCycle M.facePerm outer ⟨(p.getVert i, p.getVert (i+1)), p.adj_getVert_succ hi⟩ := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have h := hroot.trans (facial_cycle_forward_sameCycle M (walk_isCycleMap p hp) hface (i : ZMod p.length))
  have hd : toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) (i : ZMod p.length)) =
      (⟨(p.getVert i, p.getVert (i+1)), p.adj_getVert_succ hi⟩ : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    apply Prod.ext
    · exact walkCycleVertices_nat_le p (by omega)
    · change walkCycleVertices p ((i : ZMod p.length) + 1) = p.getVert (i+1)
      simpa only [Nat.cast_add, Nat.cast_one] using walkCycleVertices_nat_le p (i := i+1) (by omega)
  rwa [hd] at h

/-- A component meeting the old native face has a forward old facial edge
entering the deleted set. Its last retained native index supplies that edge. -/
lemma native_cycle_component_exit {a : V} (p : G.Walk a a) (A : Set V) (ha : a ∈ A)
    (K : (G.induce Aᶜ).ConnectedComponent)
    (hmeet : ∃ x ∈ componentVertexSet Aᶜ K, x ∈ p.support) :
    ∃ i, ∃ _hi : i < p.length, p.getVert i ∈ componentVertexSet Aᶜ K ∧ p.getVert (i+1) ∈ A := by
  let S := componentVertexSet Aᶜ K
  have hAS : ∀ x ∈ S, x ∉ A := fun x hx => componentVertexSet_subset Aᶜ K hx
  let F := (Finset.range p.length).filter (fun i => p.getVert i ∈ S)
  have hF : F.Nonempty := by
    obtain ⟨x, hxS, hxp⟩ := hmeet
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hxp
    have hil : i < p.length := by
      by_contra h
      have he : i = p.length := by omega
      have hxa : x = a := by simpa only [he, Walk.getVert_length] using hix.symm
      exact hAS x hxS (hxa.symm ▸ ha)
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hil, hix ▸ hxS⟩⟩
  let i := F.max' hF
  have hiF := Finset.max'_mem F hF
  have hi : i < p.length := Finset.mem_range.1 (Finset.mem_filter.1 hiF).1
  have hiS : p.getVert i ∈ S := (Finset.mem_filter.1 hiF).2
  have hnS : p.getVert (i+1) ∉ S := by
    intro h
    by_cases hil : i+1 < p.length
    · have hnF : i+1 ∈ F := Finset.mem_filter.2 ⟨Finset.mem_range.2 hil, h⟩
      have := Finset.le_max' F (i+1) hnF
      omega
    · have he : i+1 = p.length := by omega
      exact hAS _ h (by simpa only [he, Walk.getVert_length] using ha)
  refine ⟨i, hi, hiS, ?_⟩
  by_contra hnA
  exact hnS (componentVertexSet_adj_closed Aᶜ K hiS hnA (p.adj_getVert_succ hi))

/-- Every retained component has an edge to the deleted set in a connected
original graph, even if that component meets no old face vertex. -/
lemma component_has_deleted_neighbour (hG : G.Preconnected) (A : Set V) (hA : A.Nonempty)
    (K : (G.induce Aᶜ).ConnectedComponent) :
    ∃ x ∈ componentVertexSet Aᶜ K, ∃ y ∈ A, G.Adj x y := by
  let S := componentVertexSet Aᶜ K
  obtain ⟨u, hu⟩ := K.nonempty_supp
  have huS : u.1 ∈ S := ⟨u, hu, rfl⟩
  obtain ⟨a, ha⟩ := hA
  by_contra hnone
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
    intro x hx y hxy
    by_cases hy : y ∈ A
    · exact (hnone ⟨x, hx, y, hy, hxy⟩).elim
    · exact componentVertexSet_adj_closed Aᶜ K hx hy hxy
  have hwalk : ∀ {x y : V} (p : G.Walk x y), x ∈ S → y ∈ S := by
    intro x y p
    induction p with
    | nil => exact id
    | cons hxy p ih => exact fun hx => ih (hclosed _ hx _ hxy)
  have haS := hwalk (hG u.1 a).some huS
  exact (componentVertexSet_subset Aᶜ K haS) ha

/-- A connected deletion touching the original native facial cycle exposes
its remaining neighbours on an actual face of every nontrivial component.
The old face incidences in that component are retained. No connectivity of the
whole remainder is assumed. -/
theorem exists_outer_component_after_connected_boundary_deletion [Fintype V]
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace M outer x → x ∈ p.support)
    (A : Set V) (ha : a ∈ A) (hA : ConnSet G A)
    (K : (G.induce Aᶜ).ConnectedComponent) [Nontrivial (componentVertexSet Aᶜ K)] :
    ∃ o : (G.induce (componentVertexSet Aᶜ K)).Dart,
      (∀ x : componentVertexSet Aᶜ K, OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M (componentVertexSet Aᶜ K)) o x) ∧
      (∀ x : componentVertexSet Aᶜ K, (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M (componentVertexSet Aᶜ K)) o x) := by
  let S := componentVertexSet Aᶜ K
  let φ := componentInduceIso Aᶜ K
  have hconn : (G.induce S).Preconnected := K.connected_toSimpleGraph.preconnected.map φ.toHom φ.surjective
  have hAS : ∀ x ∈ A, x ∉ S := fun x hx h => (componentVertexSet_subset Aᶜ K h) hx
  by_cases hmeet : ∃ x ∈ S, OnOuterFace M outer x
  · have hmeet' : ∃ x ∈ S, x ∈ p.support := by
      obtain ⟨x, hxS, hxf⟩ := hmeet
      exact ⟨x, hxS, hExact x hxf⟩
    obtain ⟨i, hi, hiS, hiA⟩ := native_cycle_component_exit p A ha K hmeet'
    let d : G.Dart := ⟨(p.getVert i, p.getVert (i+1)), p.adj_getVert_succ hi⟩
    obtain ⟨o, hold, hnew, _⟩ := exists_outer_induced_merging_connected_set M outer S A hconn hA hAS d
      (native_facial_step_sameCycle M outer p hp hface hroot i hi) hiS hiA
    exact ⟨o, hold, hnew⟩
  · obtain ⟨x, hxS, y, hyA, hxy⟩ := component_has_deleted_neighbour hG A ⟨a, ha⟩ K
    let d : G.Dart := ⟨(x,y), hxy⟩
    obtain ⟨o, _, hnew, _⟩ := exists_outer_induced_merging_connected_set M d S A hconn hA hAS d
      (SameCycle.refl _ _) hxS hyA
    exact ⟨o, fun x hx => (hmeet ⟨x.1, x.2, hx⟩).elim, hnew⟩

end Thomassen
