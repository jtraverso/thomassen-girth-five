/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import LeanPool.K5MinorFreeChoosability.Cases789
public import Thomassen.Girth

@[expose] public section
open Finset LeanPool.K5MinorFreeChoosability
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

open Classical in
/-- The list remaining after a finite set has been coloured and deleted. -/
noncomputable def residual (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) : Finset C := L v \ (S.filter (G.Adj v)).image c

lemma residual_subset (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) : residual G L S c v ⊆ L v := by
  classical
  exact sdiff_subset

lemma mem_residual_iff (L : V → Finset C) (S : Finset V) (c : V → C) (v : V) (x : C) :
    x ∈ residual G L S c v ↔ x ∈ L v ∧ ∀ u ∈ S, G.Adj v u → x ≠ c u := by
  classical
  simp only [residual, mem_sdiff, mem_image, mem_filter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun u hu hvu heq => h ⟨u, ⟨hu, hvu⟩, heq.symm⟩⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rintro ⟨u, ⟨hu, hvu⟩, heq⟩
    exact h u hu hvu heq.symm

/-- Deleting `t` coloured neighbours removes at most `t` available colours. -/
lemma residual_card (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) :
    (L v).card ≤ (residual G L S c v).card + (S.filter (G.Adj v)).card := by
  classical
  have h := card_sdiff_add_card (L v) ((S.filter (G.Adj v)).image c)
  have him := card_image_le (f := c) (s := S.filter (G.Adj v))
  have hun : (L v).card ≤ (L v ∪ (S.filter (G.Adj v)).image c).card := card_le_card subset_union_left
  change (L v).card ≤ (L v \ (S.filter (G.Adj v)).image c).card + _
  omega

lemma residual_card_one (G : SimpleGraph V) (L : V → Finset C) (S : Finset V)
    (c : V → C) (v : V) (h : (S.filter (G.Adj v)).card ≤ 1) :
    (L v).card ≤ (residual G L S c v).card + 1 := by
  have hcard := residual_card G L S c v
  omega

lemma residual_three_to_two (L : V → Finset C) (S : Finset V) (c : V → C) (v : V)
    (hL : 3 ≤ (L v).card) (h : (S.filter (G.Adj v)).card ≤ 1) :
    2 ≤ (residual G L S c v).card := by
  have hcard := residual_card_one G L S c v h
  omega

lemma residual_unchanged (L : V → Finset C) (S : Finset V) (c : V → C) (v : V)
    (h : ∀ u ∈ S, ¬ G.Adj v u) : residual G L S c v = L v := by
  classical
  apply Finset.ext
  intro x
  rw [mem_residual_iff]
  exact ⟨And.left, fun hx => ⟨hx, fun u hu hAdj => False.elim (h u hu hAdj)⟩⟩

/-- Gluing across the deleted set, using the existing partial-colouring predicate.
Residual lists account for edges between the two pieces. -/
lemma glue_residual [DecidableEq V] (S A : Finset V) (L : V → Finset C) (c d : V → C)
    (hc : ∀ a ∈ A, c a ∈ L a)
    (hpc : ∀ a ∈ A, ∀ b ∈ A, G.Adj a b → c a ≠ c b)
    (hd : ∀ a ∈ S \ A, d a ∈ residual G L A c a)
    (hpd : ∀ a ∈ S \ A, ∀ b ∈ S \ A, G.Adj a b → d a ≠ d b) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) := by
  classical
  refine ⟨fun a => if a ∈ A then c a else d a, ?_, ?_⟩
  · intro a ha
    by_cases hA : a ∈ A
    · simpa [hA] using hc a hA
    · simpa [hA] using (mem_residual_iff L A c a (d a)).1
        (hd a (mem_sdiff.2 ⟨ha, hA⟩)) |>.1
  · intro a b hab
    have haS : a ∈ S := hab.2.1
    have hbS : b ∈ S := hab.2.2
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
    · simp only [ha, hb, ↓reduceIte]
      exact hpc a ha b hb hab.1
    · simp only [ha, hb, ↓reduceIte]
      exact ((mem_residual_iff L A c b (d b)).1
        (hd b (mem_sdiff.2 ⟨hbS, hb⟩)) |>.2 a ha hab.1.symm).symm
    · simp only [ha, hb, ↓reduceIte]
      exact (mem_residual_iff L A c a (d a)).1
        (hd a (mem_sdiff.2 ⟨haS, ha⟩)) |>.2 b hb hab.1
    · simp only [ha, hb, ↓reduceIte]
      exact hpd a (mem_sdiff.2 ⟨haS, ha⟩) b (mem_sdiff.2 ⟨hbS, hb⟩) hab.1

end Thomassen
