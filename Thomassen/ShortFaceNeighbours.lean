/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedResidualExtension

/-! Neighbours of short boundary cycles in girth at least five. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- Two neighbours of an exterior vertex cannot be consecutive, or separated
by just one vertex, on a simple cycle. -/
lemma cycle_neighbour_indices_not_near (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) {u : V} (hu : u ∉ Set.range c) (i j : ZMod k)
    (hui : G.Adj u (c i)) (huj : G.Adj u (c j)) : j ≠ i+1 ∧ j ≠ i+2 := by
  constructor
  · intro heq
    exact neighbors_nonadjacent hg hui huj (by rw [heq]; exact hc.adj i)
  · intro heq
    have hne : c i ≠ c (i+2) := by
      intro h
      have he := hc.inj h
      have hz : (2 : ZMod k) = 0 := by linear_combination -he
      exact zmod_two_ne_zero_of_three_le hk hz
    have huj' : G.Adj (c (i+2)) u := by rw [← heq]; exact huj.symm
    have hn : G.Adj (c (i+2)) (c (i+1)) := by
      simpa only [show i+1+1 = i+2 by ring] using (hc.adj (i+1)).symm
    have h := common_neighbor_unique hg hne hui.symm huj' (hc.adj i) hn
    exact hu ⟨i+1,h.symm⟩

/-- Along either direction of the cycle, distinct neighbours leave at least
three boundary edges between them. -/
lemma cycle_neighbour_nat_gaps (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) {u : V} (hu : u ∉ Set.range c) (i j : ℕ)
    (_hi : i < k) (hj : j < k) (hij : i < j)
    (hui : G.Adj u (c (i : ZMod k))) (huj : G.Adj u (c (j : ZMod k))) :
    i+3 ≤ j ∧ j+3 ≤ i+k := by
  have hforward := cycle_neighbour_indices_not_near hg hc hk hu (i : ZMod k) (j : ZMod k) hui huj
  have hbackward := cycle_neighbour_indices_not_near hg hc hk hu (j : ZMod k) (i : ZMod k) huj hui
  constructor
  · by_contra h
    rcases (by omega : j = i+1 ∨ j = i+2) with he | he
    · apply hforward.1; simp only [he,Nat.cast_add,Nat.cast_one]
    · apply hforward.2; simp only [he,Nat.cast_add,Nat.cast_ofNat]
  · by_contra h
    rcases (by omega : j+1 = i+k ∨ j+2 = i+k) with he | he
    · apply hbackward.1
      have he' := congrArg (fun n : ℕ => (n : ZMod k)) he
      simpa only [Nat.cast_add,Nat.cast_one,ZMod.natCast_self,add_zero] using he'.symm
    · apply hbackward.2
      have he' := congrArg (fun n : ℕ => (n : ZMod k)) he
      simpa only [Nat.cast_add,Nat.cast_ofNat,ZMod.natCast_self,add_zero] using he'.symm

/-- A vertex outside a cycle of at most eight vertices has at most two
neighbours on that cycle. Three cyclic gaps would require at least nine edges. -/
theorem at_most_two_neighbours_on_short_cycle [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hshort : k ≤ 8) {u : V} (hu : u ∉ Set.range c)
    (i j l : ZMod k) (hui : G.Adj u (c i)) (huj : G.Adj u (c j)) (hul : G.Adj u (c l)) :
    i = j ∨ i = l ∨ j = l := by
  by_contra h
  push Not at h
  have hij : i.val ≠ j.val := fun he => h.1 (ZMod.val_injective _ he)
  have hil : i.val ≠ l.val := fun he => h.2.1 (ZMod.val_injective _ he)
  have hjl : j.val ≠ l.val := fun he => h.2.2 (ZMod.val_injective _ he)
  have hgap : ∀ (r s : ZMod k), r.val ≠ s.val → G.Adj u (c r) → G.Adj u (c s) →
      (r.val+3 ≤ s.val ∧ s.val+3 ≤ r.val+k) ∨
      (s.val+3 ≤ r.val ∧ r.val+3 ≤ s.val+k) := by
    intro r s hrs hur hus
    rcases lt_or_gt_of_ne hrs with hrs | hrs
    · exact Or.inl (cycle_neighbour_nat_gaps hg hc hk hu r.val s.val (ZMod.val_lt r)
        (ZMod.val_lt s) hrs (by rwa [ZMod.natCast_zmod_val]) (by rwa [ZMod.natCast_zmod_val]))
    · exact Or.inr (cycle_neighbour_nat_gaps hg hc hk hu s.val r.val (ZMod.val_lt s)
        (ZMod.val_lt r) hrs (by rwa [ZMod.natCast_zmod_val]) (by rwa [ZMod.natCast_zmod_val]))
  have hab := hgap i j hij hui huj
  have hac := hgap i l hil hui hul
  have hbc := hgap j l hjl huj hul
  omega

end Thomassen
