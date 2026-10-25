/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Challenge
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
Independent contracts for the reusable SUPPORTING LEMMAS of the unfinished
Thomassen girth-five project. These contracts do not assert the main theorem.
`Challenge` contains the ten preserved planar-list-colouring contracts.
-/
@[expose] public section
open Finset

namespace LeanPool.K5MinorFreeChoosability
section Basic
variable {V C : Type*}
def ListColourable (G : SimpleGraph V) (L : V → Finset C) : Prop :=
  ∃ c : G.Coloring C, ∀ v, c v ∈ L v
end Basic
section Reach
variable {W : Type*}
def RIn (G : SimpleGraph W) (s : Set W) : W → W → Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)
def ConnSet (G : SimpleGraph W) (s : Set W) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, RIn G s a b
def restrict (G : SimpleGraph W) (s : Set W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩
end Reach
section Partial
variable {V C : Type*} [DecidableEq V]
def Col (G : SimpleGraph V) (S : Finset V) (L : V → Finset C) (M : V → V → C → C → Prop) :
    Prop :=
  ∃ c : V → C, (∀ a ∈ S, c a ∈ L a) ∧ ∀ a b, G.Adj a b → ¬ M a b (c a) (c b)
end Partial
section Minor
variable {V : Type*}
structure CliqueMinorModel (G : SimpleGraph V) (k : ℕ) where
  branch : Fin k → Finset V
  branch_nonempty : ∀ i, (branch i).Nonempty
  branch_connected : ∀ i, (G.induce (↑(branch i) : Set V)).Connected
  branch_disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  branch_adjacent : ∀ i j, i ≠ j →
    ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v

def CliqueMinorFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ Nonempty (CliqueMinorModel G k)

end Minor

section Apex
universe u_3
variable {V : Type u_3}

def apexExtend (G : SimpleGraph V) (B : Set V) : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | none, some b => b ∈ B
    | some a, none => a ∈ B
    | none, none => False
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact G.irrefl h⟩

def K5MinorFree (G : SimpleGraph V) : Prop := CliqueMinorFree G 5

def IsK5Boundary (G : SimpleGraph V) (B : Set V) : Prop := K5MinorFree (apexExtend G B)
end Apex
end LeanPool.K5MinorFreeChoosability

open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

noncomputable def residual (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) : Finset C := L v \ (S.filter (G.Adj v)).image c

def MinimalBad (G : SimpleGraph V) (S : Finset V) (L : V → Finset C) : Prop :=
  ¬ Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ∧
    ∀ T ⊂ S, Col (restrict G (↑T : Set V)) T L (fun _ _ x y => x = y)

theorem five_le_egirth_iff : 5 ≤ G.egirth ↔
    ∀ a (w : G.Walk a a), w.IsCycle → 5 ≤ w.length := by
  sorry

theorem five_le_egirth_of_le {H : SimpleGraph V} (hG : 5 ≤ G.egirth) (hHG : H ≤ G) :
    5 ≤ H.egirth := by
  sorry

theorem cliqueFree_three (hG : 5 ≤ G.egirth) : G.CliqueFree 3 := by
  sorry

theorem neighbors_nonadjacent (hG : 5 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c := by
  sorry

theorem common_neighbor_unique (hG : 5 ≤ G.egirth) {a b x y : V} (hab : a ≠ b)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  sorry

theorem edge_neighborhoods_disjoint (hG : 5 ≤ G.egirth) {a b : V} (hab : G.Adj a b) :
    Disjoint (G.neighborSet a) (G.neighborSet b) := by
  sorry

theorem deleted_edge_neighbors_independent (hG : 5 ≤ G.egirth) {a b x y : V}
    (hab : G.Adj a b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : G.Adj a x ∨ G.Adj b x) (hy : G.Adj a y ∨ G.Adj b y) : ¬ G.Adj x y := by
  sorry

lemma residual_subset (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) : residual G L S c v ⊆ L v := by
  sorry

lemma mem_residual_iff (L : V → Finset C) (S : Finset V) (c : V → C) (v : V) (x : C) :
    x ∈ residual G L S c v ↔ x ∈ L v ∧ ∀ u ∈ S, G.Adj v u → x ≠ c u := by
  sorry

lemma residual_card (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) :
    (L v).card ≤ (residual G L S c v).card + (S.filter (G.Adj v)).card := by
  sorry

lemma residual_card_one (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) (h : (S.filter (G.Adj v)).card ≤ 1) :
    (L v).card ≤ (residual G L S c v).card + 1 := by
  sorry

lemma residual_three_to_two (L : V → Finset C) (S : Finset V) (c : V → C) (v : V)
    (hL : 3 ≤ (L v).card) (h : (S.filter (G.Adj v)).card ≤ 1) :
    2 ≤ (residual G L S c v).card := by
  sorry

lemma residual_unchanged (L : V → Finset C) (S : Finset V) (c : V → C) (v : V)
    (h : ∀ u ∈ S, ¬ G.Adj v u) : residual G L S c v = L v := by
  sorry

lemma glue_residual [DecidableEq V] (S A : Finset V) (L : V → Finset C) (c d : V → C)
    (hc : ∀ a ∈ A, c a ∈ L a)
    (hpc : ∀ a ∈ A, ∀ b ∈ A, G.Adj a b → c a ≠ c b)
    (hd : ∀ a ∈ S \ A, d a ∈ residual G L A c a)
    (hpd : ∀ a ∈ S \ A, ∀ b ∈ S \ A, G.Adj a b → d a ≠ d b) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) := by
  sorry

lemma col_restrict_iff (S : Finset V) (L : V → Finset C) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ↔
      ∃ c : V → C, (∀ a ∈ S, c a ∈ L a) ∧
        ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → c a ≠ c b := by
  sorry

lemma col_univ_iff [Fintype V] (L : V → Finset C) :
    Col (restrict G (↑(univ : Finset V) : Set V)) univ L
      (fun _ _ x y => x = y) ↔ ListColourable G L := by
  sorry

lemma col_of_erase (S : Finset V) (L : V → Finset C) (w : V)
    (hc : Col (restrict G (↑(S.erase w) : Set V)) (S.erase w) L
      (fun _ _ x y => x = y))
    (hdeg : ((S.erase w).filter (G.Adj w)).card < (L w).card) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) := by
  sorry

lemma minimal_bad_exists (S : Finset V) (L : V → Finset C)
    (hbad : ¬ Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y)) :
    ∃ T ⊆ S, MinimalBad G T L := by
  sorry

lemma minimal_bad_degree {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) {w : V} (hw : w ∈ S) :
    (L w).card ≤ ((S.erase w).filter (G.Adj w)).card := by
  sorry

lemma minimal_bad_nonempty [Nonempty C] {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) : S.Nonempty := by
  sorry

lemma minimal_bad_connSet [Nonempty C] {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) : ConnSet G (↑S : Set V) := by
  sorry

lemma neighbors_in_edge_card_le_one (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (w : V) :
    (({a, b} : Finset V).filter (G.Adj w)).card ≤ 1 := by
  sorry

lemma residual_edge_card_ge_two (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (L : V → Finset C) (c : V → C) (w : V)
    (hL : 3 ≤ (L w).card) : 2 ≤ (residual G L {a, b} c w).card := by
  sorry

lemma short_residual_edge_neighbor {a b : V} (L : V → Finset C) (c : V → C)
    (w : V) (hL : 3 ≤ (L w).card)
    (hshort : (residual G L {a, b} c w).card ≤ 2) : G.Adj a w ∨ G.Adj b w := by
  sorry

lemma short_residual_edge_independent (hG : 5 ≤ G.egirth) {a b : V}
    (hab : G.Adj a b) (L : V → Finset C) (c : V → C) {x y : V}
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b} c x).card ≤ 2)
    (hyshort : (residual G L {a, b} c y).card ≤ 2) : ¬ G.Adj x y := by
  sorry

lemma delete_edge_boundary {B S : Set V} {a b : V}
    (hB : IsK5Boundary G B) (haB : a ∈ B) (hab : G.Adj a b)
    (haS : a ∉ S) (hbS : b ∉ S) :
    IsK5Boundary (restrict G S) (S ∩ (B ∪ G.neighborSet a ∪ G.neighborSet b)) := by
  sorry

/-- Contracts for the three-vertex reduction, independent of its solution module. -/
lemma short_residual_neighbor (L : V → Finset C) (S : Finset V) (c : V → C)
    (w : V) (hL : 3 ≤ (L w).card)
    (hshort : (residual G L S c w).card ≤ 2) : ∃ z ∈ S, G.Adj z w := by
  sorry

lemma neighbors_in_two_edge_path_card_le_one (hG : 5 ≤ G.egirth) {a b d w : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d) (hwb : w ≠ b) :
    (({a, b, d} : Finset V).filter (G.Adj w)).card ≤ 1 := by
  sorry

lemma residual_two_edge_path_card_ge_two (hG : 5 ≤ G.egirth) {a b d w : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d) (hwb : w ≠ b)
    (L : V → Finset C) (c : V → C) (hL : 3 ≤ (L w).card) :
    2 ≤ (residual G L {a, b, d} c w).card := by
  sorry

lemma deleted_two_edge_path_adjacent_neighbors (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (hxn : G.Adj a x ∨ G.Adj b x ∨ G.Adj d x)
    (hyn : G.Adj a y ∨ G.Adj b y ∨ G.Adj d y) (hxy : G.Adj x y) :
    (G.Adj a x ∧ G.Adj d y) ∨ (G.Adj d x ∧ G.Adj a y) := by
  sorry

lemma short_residual_two_edge_path_adjacent (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2) (hxy : G.Adj x y) :
    (G.Adj a x ∧ G.Adj d y) ∨ (G.Adj d x ∧ G.Adj a y) := by
  sorry

lemma short_residual_two_edge_path_forces_three_path (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2) (hxy : G.Adj x y) :
    ∃ p : G.Walk a d, p.IsPath ∧ p.length = 3 ∧ b ∉ p.support := by
  sorry

lemma short_residual_two_edge_path_independent (hG : 5 ≤ G.egirth) {a b d x y : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : a ≠ d)
    (hx : x ∉ ({a, b, d} : Finset V)) (hy : y ∉ ({a, b, d} : Finset V))
    (L : V → Finset C) (c : V → C)
    (hxL : 3 ≤ (L x).card) (hyL : 3 ≤ (L y).card)
    (hxshort : (residual G L {a, b, d} c x).card ≤ 2)
    (hyshort : (residual G L {a, b, d} c y).card ≤ 2)
    (hno : ∀ p : G.Walk a d, p.IsPath → p.length = 3 → b ∉ p.support → False) :
    ¬ G.Adj x y := by
  sorry

end Thomassen
