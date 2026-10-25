/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ComponentBoundaryDeletion

/-! Component faces after deletion of an arbitrary boundary vertex.
The old face orbit may repeat vertices; no facial-cycle hypothesis is needed. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} [Fintype V]

/-- A retained component meeting a selected face has an old face dart entering
the deleted boundary vertex. Follow that actual face orbit to its first exit. -/
lemma boundary_component_exit_at_vertex (M : PlaneMap G) (outer : G.Dart)
    (x : V) (hx : OnOuterFace M outer x)
    (K : (G.induce ({x} : Set V)ᶜ).ConnectedComponent)
    (hmeet : ∃ z ∈ componentVertexSet ({x} : Set V)ᶜ K, OnOuterFace M outer z) :
    ∃ d : G.Dart, SameCycle M.facePerm outer d ∧
      d.fst ∈ componentVertexSet ({x} : Set V)ᶜ K ∧ d.snd = x := by
  let S := componentVertexSet ({x} : Set V)ᶜ K
  obtain ⟨z,hzS,d,hd,hdz⟩ := hmeet
  obtain ⟨e,he,hex⟩ := hx
  obtain ⟨n,hn⟩ := (hd.symm.trans he).exists_nat_pow_eq
  have hexit : ∃ k : ℕ, ((M.facePerm ^ k) d).fst ∉ S := by
    refine ⟨n,?_⟩
    rw [hn,hex]
    exact fun h => (componentVertexSet_subset ({x} : Set V)ᶜ K h) (Set.mem_singleton x)
  let k := Nat.find hexit
  have hkout : ((M.facePerm ^ k) d).fst ∉ S := Nat.find_spec hexit
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hin : ((M.facePerm ^ k) d).fst ∈ S := by simpa only [hk0,pow_zero,Perm.one_apply,hdz] using hzS
    exact hkout hin
  let t := (M.facePerm ^ (k-1)) d
  have htS : t.fst ∈ S := by
    by_contra h
    have hmin := Nat.find_min hexit (show k-1 < Nat.find hexit by change k-1<k; omega)
    exact hmin h
  have hnext : M.facePerm t = (M.facePerm ^ k) d := by
    have heq : k = (k-1)+1 := by omega
    conv_rhs => rw [heq,pow_succ',Perm.mul_apply]
  have htout : t.snd ∉ S := by
    have hf : (M.facePerm t).fst = t.snd := M.isRotationSystem.fst_apply _
    rwa [← hf,hnext]
  have htx : t.snd = x := by
    by_contra h
    have hs : t.snd ∈ ({x} : Set V)ᶜ := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using h
    exact htout (componentVertexSet_adj_closed ({x} : Set V)ᶜ K htS hs t.adj)
  refine ⟨t,?_,htS,htx⟩
  exact hd.trans ⟨((k-1 : ℕ) : ℤ),by simp only [zpow_natCast]; rfl⟩

/-- Deleting a boundary vertex exposes all its neighbours on one actual face
of each remaining nontrivial component, preserving that component's old outer
incidences. The original graph may have cutvertices and repeated face vertices. -/
theorem exists_outer_component_after_boundary_vertex_deletion
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected)
    (x : V) (hx : OnOuterFace M outer x)
    (K : (G.induce ({x} : Set V)ᶜ).ConnectedComponent)
    [Nontrivial (componentVertexSet ({x} : Set V)ᶜ K)] :
    ∃ o : (G.induce (componentVertexSet ({x} : Set V)ᶜ K)).Dart,
      (∀ z : componentVertexSet ({x} : Set V)ᶜ K, OnOuterFace M outer z.1 →
        OnOuterFace (inducedPlaneMap M (componentVertexSet ({x} : Set V)ᶜ K)) o z) ∧
      (∀ z : componentVertexSet ({x} : Set V)ᶜ K, G.Adj z.1 x →
        OnOuterFace (inducedPlaneMap M (componentVertexSet ({x} : Set V)ᶜ K)) o z) := by
  let S := componentVertexSet ({x} : Set V)ᶜ K
  let φ := componentInduceIso ({x} : Set V)ᶜ K
  have hconn : (G.induce S).Preconnected := K.connected_toSimpleGraph.preconnected.map φ.toHom φ.surjective
  have hA : ConnSet G ({x} : Set V) := by
    refine ⟨⟨x,rfl⟩,?_⟩
    intro a ha b hb
    have ha' : a = x := ha
    have hb' : b = x := hb
    subst a; subst b
    exact .refl _
  have hAS : ∀ z ∈ ({x} : Set V), z ∉ S := by
    intro z hz hs
    exact (componentVertexSet_subset ({x} : Set V)ᶜ K hs) hz
  by_cases hmeet : ∃ z ∈ S, OnOuterFace M outer z
  · obtain ⟨d,hd,hdS,hdx⟩ := boundary_component_exit_at_vertex M outer x hx K hmeet
    obtain ⟨o,hold,hnew,_⟩ := exists_outer_induced_merging_connected_set M outer S {x}
      hconn hA hAS d hd hdS (by simpa only [Set.mem_singleton_iff] using hdx)
    exact ⟨o,hold,fun z hzx => hnew z ⟨x,rfl,hzx⟩⟩
  · obtain ⟨z,hzS,y,hy,hzy⟩ := component_has_deleted_neighbour hG ({x} : Set V) ⟨x,rfl⟩ K
    let d : G.Dart := ⟨(z,y),hzy⟩
    obtain ⟨o,_,hnew,_⟩ := exists_outer_induced_merging_connected_set M d S {x}
      hconn hA hAS d (SameCycle.refl _ _) hzS hy
    exact ⟨o,fun z hz => (hmeet ⟨z.1,z.2,hz⟩).elim,fun z hzx => hnew z ⟨x,rfl,hzx⟩⟩

end Thomassen
