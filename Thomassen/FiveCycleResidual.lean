/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FiveFaceInteriorAttachments

/-! Deleting a coloured native five-cycle leaves at least two colours. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The registered five-cycle neighbour lemma applies at every cycle vertex,
by translating its cyclic index. -/
theorem off_five_cycle_neighbours_unique (hg : 5 ≤ G.egirth) {c : ZMod 5 → V}
    (hc : IsCycleMap G c) {x : V} (hx : x ∉ Set.range c)
    {y z : V} (hy : y ∈ Set.range c) (hz : z ∈ Set.range c)
    (hxy : G.Adj x y) (hxz : G.Adj x z) : y=z := by
  obtain ⟨i,rfl⟩ := hy
  let d : ZMod 5 → V := fun j => c (i+j)
  have hd : IsCycleMap G d := {
    inj := fun j k h => add_left_cancel (hc.inj h)
    adj := fun j => by simpa only [d,add_assoc] using hc.adj (i+j) }
  have hrange : Set.range d = Set.range c := by
    ext w
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨i+j,rfl⟩
    · rintro ⟨j,rfl⟩; exact ⟨j-i,by simp only [d,add_sub_cancel]⟩
  by_contra hne
  exact off_five_cycle_unique_neighbour hg hd (by rwa [hrange])
    (by simpa only [d,add_zero] using hxy.symm) (by rwa [hrange])
    (by simpa only [d,add_zero] using (fun h => hne h.symm)) hxz

/-- A vertex outside a native five-cycle has at most one neighbour on it.
This bound is independent of the embedding and of the chosen colours. -/
theorem off_native_five_cycle_neighbours_card_le_one {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length=5)
    (x : V) (hx : x ∉ p.support) :
    (p.support.toFinset.filter (G.Adj x)).card ≤ 1 := by
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
  rw [Finset.card_le_one]
  intro y hy z hz
  obtain ⟨hy,hxy⟩ := Finset.mem_filter.1 hy
  obtain ⟨hz,hxz⟩ := Finset.mem_filter.1 hz
  exact off_five_cycle_neighbours_unique hg hc (by simpa only [hr,Set.mem_ofPred_eq] using hx)
    (by simpa only [hr,Set.mem_ofPred_eq,List.mem_toFinset] using hy)
    (by simpa only [hr,Set.mem_ofPred_eq,List.mem_toFinset] using hz) hxy hxz

/-- Original lists with at least three colours retain at least two after a
coloured native five-cycle has been deleted. -/
theorem residual_native_five_cycle_card_ge_two {a : V} (hg : 5 ≤ G.egirth)
    (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length=5)
    (L : V → Finset C) (f : V → C) (x : V) (hx : x ∉ p.support)
    (hL : 3 ≤ (L x).card) : 2 ≤ (residual G L p.support.toFinset f x).card :=
  residual_three_to_two L p.support.toFinset f x hL
    (off_native_five_cycle_neighbours_card_le_one hg p hp hlen x hx)

end Thomassen
