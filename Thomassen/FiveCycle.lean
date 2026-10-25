/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleWalk
public import Thomassen.ThreeVertexDeletion
public import Mathlib.Tactic.FinCases

/-! Local and geometric ingredients for deleting a prescribed facial vertex. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- A vertex off a five-cycle cannot be adjacent to two cycle vertices. -/
lemma off_five_cycle_unique_neighbour (hg : 5 ≤ G.egirth) {c : ZMod 5 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c) (hax : G.Adj (c 0) x)
    {y : V} (hy : y ∈ Set.range c) (hya : y ≠ c 0) : ¬ G.Adj x y := by
  have h01 := hc.adj 0
  have h12 := hc.adj 1
  have h23 := hc.adj 2
  have h34 := hc.adj 3
  have h40 := hc.adj 4
  norm_num at h01 h12 h23 h34 h40
  obtain ⟨i, rfl⟩ := hy
  fin_cases i
  · exact (hya rfl).elim
  · intro h
    exact neighbors_nonadjacent hg h01 hax h.symm
  · intro h
    have hne : c 0 ≠ c 2 := fun heq => (by decide : (0 : ZMod 5) ≠ 2) (hc.inj heq)
    have heq := common_neighbor_unique hg hne h01 h12.symm hax h.symm
    exact hx ⟨1, heq⟩
  · intro h
    have hne : c 0 ≠ c 3 := fun heq => (by decide : (0 : ZMod 5) ≠ 3) (hc.inj heq)
    have heq := common_neighbor_unique hg hne h40.symm h34 hax h.symm
    exact hx ⟨4, heq⟩
  · intro h
    exact neighbors_nonadjacent hg h40.symm hax h.symm

lemma off_native_five_cycle_unique_neighbour {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 5)
    {x : V} (hx : x ∉ p.support) (hax : G.Adj a x)
    {y : V} (hy : y ∈ p.support) (hya : y ≠ a) : ¬ G.Adj x y := by
  let c : ZMod 5 → V := fun i => p.getVert i.val
  have hc : IsCycleMap G c := by
    have h := walk_isCycleMap p hp
    change IsCycleMap G (fun i : ZMod p.length => p.getVert i.val) at h
    rw [hlen] at h
    exact h
  have hr : Set.range c = {z | z ∈ p.support} := by
    have h := walkCycleVertices_range p hp
    change Set.range (fun i : ZMod p.length => p.getVert i.val) = {z | z ∈ p.support} at h
    rw [hlen] at h
    exact h
  have h0 : c 0 = a := by simp only [c, ZMod.val_zero, Walk.getVert_zero]
  apply off_five_cycle_unique_neighbour hg hc
  · simpa only [hr, Set.mem_ofPred_eq] using hx
  · simpa only [h0] using hax
  · simpa only [hr, Set.mem_ofPred_eq] using hy
  · simpa only [h0] using hya

/-- On a six-cycle, a second neighbour of an exterior neighbour of the root
can only be the opposite vertex. -/
lemma off_six_cycle_second_neighbour (hg : 5 ≤ G.egirth) {c : ZMod 6 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c) (hax : G.Adj (c 0) x)
    {y : V} (hy : y ∈ Set.range c) (hya : y ≠ c 0) (hxy : G.Adj x y) : y = c 3 := by
  have h01 := hc.adj 0
  have h12 := hc.adj 1
  have h23 := hc.adj 2
  have h34 := hc.adj 3
  have h45 := hc.adj 4
  have h50 := hc.adj 5
  norm_num at h01 h12 h23 h34 h45 h50
  obtain ⟨i, rfl⟩ := hy
  fin_cases i
  · exact (hya rfl).elim
  · exact (neighbors_nonadjacent hg h01 hax hxy.symm).elim
  · have hne : c 0 ≠ c 2 := fun heq => (by decide : (0 : ZMod 6) ≠ 2) (hc.inj heq)
    have heq := common_neighbor_unique hg hne h01 h12.symm hax hxy.symm
    exact (hx ⟨1, heq⟩).elim
  · rfl
  · have hne : c 0 ≠ c 4 := fun heq => (by decide : (0 : ZMod 6) ≠ 4) (hc.inj heq)
    have heq := common_neighbor_unique hg hne h50.symm h45 hax hxy.symm
    exact (hx ⟨5, heq⟩).elim
  · exact (neighbors_nonadjacent hg h50.symm hax hxy.symm).elim

lemma off_native_six_cycle_second_neighbour {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    {x : V} (hx : x ∉ p.support) (hax : G.Adj a x)
    {y : V} (hy : y ∈ p.support) (hya : y ≠ a) (hxy : G.Adj x y) :
    y = p.getVert 3 := by
  let c : ZMod 6 → V := fun i => p.getVert i.val
  have hc : IsCycleMap G c := by
    have h := walk_isCycleMap p hp
    change IsCycleMap G (fun i : ZMod p.length => p.getVert i.val) at h
    rw [hlen] at h
    exact h
  have hr : Set.range c = {z | z ∈ p.support} := by
    have h := walkCycleVertices_range p hp
    change Set.range (fun i : ZMod p.length => p.getVert i.val) = {z | z ∈ p.support} at h
    rw [hlen] at h
    exact h
  have h0 : c 0 = a := by simp only [c, ZMod.val_zero, Walk.getVert_zero]
  have heq : y = c 3 := off_six_cycle_second_neighbour hg hc
    (by simpa only [hr, Set.mem_ofPred_eq] using hx)
    (by simpa only [h0] using hax)
    (by simpa only [hr, Set.mem_ofPred_eq] using hy)
    (by simpa only [h0] using hya) hxy
  simpa only [c, show (3 : ZMod 6).val = 3 from rfl] using heq

lemma cycle_tail_dropLast_support {a : V} (p : G.Walk a a) (hp : p.IsCycle) (x : V) :
    x ∈ p.tail.dropLast.support ↔ x ∈ p.support ∧ x ≠ a := by
  have hlen := hp.three_le_length
  have ht : ¬ p.tail.Nil := by
    simp only [Walk.not_nil_iff_lt_length, Walk.length_tail]
    omega
  have hconcat := Walk.support_dropLast_concat (p := p.tail) ht
  have hnd := hp.isPath_tail.support_nodup
  rw [← hconcat] at hnd
  have hnot : a ∉ p.tail.dropLast.support := fun h =>
    List.disjoint_of_nodup_append hnd h (by simp)
  have hfull : p.support = a :: (p.tail.dropLast.support ++ [a]) :=
    (p.cons_support_tail hp.not_nil).symm.trans (congrArg (fun l => a :: l) hconcat.symm)
  constructor
  · intro hx
    refine ⟨?_, fun h => hnot (h ▸ hx)⟩
    rw [hfull]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  · rintro ⟨hx, hxa⟩
    rw [hfull] at hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    exact hx.elim (fun h => (hxa h).elim) (fun h => h.resolve_right hxa)

lemma cycle_tail_dropLast_edges {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    {x y : V} (hx : x ≠ a) (hy : y ≠ a) :
    s(x, y) ∈ p.tail.dropLast.edges ↔ s(x, y) ∈ p.edges := by
  have hlen := hp.three_le_length
  have ht : ¬ p.tail.Nil := by
    simp only [Walk.not_nil_iff_lt_length, Walk.length_tail]
    omega
  have hcons := congrArg Walk.edges (p.cons_tail_eq hp.not_nil)
  have hconcat := congrArg Walk.edges (Walk.concat_dropLast (p.tail.adj_penultimate ht))
  simp only [Walk.edges_cons] at hcons
  simp only [Walk.edges_concat] at hconcat
  rw [← hcons, ← hconcat]
  simp only [List.mem_cons, List.concat_eq_append, List.mem_append, List.not_mem_nil, Sym2.eq_iff,
    hx, hy, false_and, and_false, false_or, or_false]

variable [Fintype V]

/-- Deleting a boundary vertex exposes its neighbours on the projected face. -/
lemma exists_outer_after_boundary_vertex (M : PlaneMap G) (outer : G.Dart) (a : V)
    [Nontrivial (({a} : Set V)ᶜ : Set V)] (ha : OnOuterFace M outer a)
    (hconn : (G.induce ({a} : Set V)ᶜ).Preconnected) :
    ∃ o : (G.induce ({a} : Set V)ᶜ).Dart,
      (∀ x : (({a} : Set V)ᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M ({a} : Set V)ᶜ) o x) ∧
      (∀ x : (({a} : Set V)ᶜ : Set V), G.Adj x.1 a →
        OnOuterFace (inducedPlaneMap M ({a} : Set V)ᶜ) o x) := by
  obtain ⟨d, hd, hda⟩ := ha
  let prev := M.facePerm⁻¹ d
  have hf : (M.facePerm prev).fst = prev.snd := M.isRotationSystem.fst_apply _
  have hnext : M.facePerm prev = d := by simp [prev]
  rw [hnext, hda] at hf
  have hsnd : prev.snd = a := hf.symm
  have hkeep : prev.fst ∉ ({a} : Set V) := fun h =>
    prev.adj.ne ((Set.mem_singleton_iff.1 h).trans hsnd.symm)
  obtain ⟨o, hface, hneigh⟩ := exists_outer_induced_after_connected_deletion M outer {a}
    hconn (connSet_singleton G a) prev (hd.trans ⟨-1, by simp [prev]⟩) hkeep
    (Set.mem_singleton_iff.2 hsnd)
  exact ⟨o, hface, fun x hx => hneigh x ⟨a, Set.mem_singleton _, hx⟩⟩

end Thomassen
