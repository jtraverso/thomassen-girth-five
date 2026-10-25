/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortLists

/-!
# Updating a minor-free boundary after deleting an edge

This is an application, twice, of the registered `isK5Boundary_delete` theorem.
It records that the remaining old boundary and all newly exposed neighbours can
be included in the new boundary. No geometric extension theorem is assumed.
-/

@[expose] public section
open LeanPool.K5MinorFreeChoosability
universe u
namespace Thomassen
variable {V : Type u} {G : SimpleGraph V}

lemma delete_edge_boundary {B S : Set V} {a b : V}
    (hB : IsK5Boundary G B) (haB : a ∈ B) (hab : G.Adj a b)
    (haS : a ∉ S) (hbS : b ∉ S) :
    IsK5Boundary (restrict G S) (S ∩ (B ∪ G.neighborSet a ∪ G.neighborSet b)) := by
  classical
  let T : Set V := {v | v ≠ a}
  let B₁ : Set V := (B \ {a}) ∪ G.neighborSet a
  have h₁ : IsK5Boundary (restrict G T) B₁ := by
    apply isK5Boundary_delete hB haB (by simp [T])
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr hv
  have hb₁ : b ∈ B₁ := Or.inr hab
  have h₂ : IsK5Boundary (restrict (restrict G T) S)
      (S ∩ (B ∪ G.neighborSet a ∪ G.neighborSet b)) := by
    apply isK5Boundary_delete h₁ hb₁ hbS
    rintro v ⟨hvS, hv⟩
    have hva : v ≠ a := fun h => haS (h ▸ hvS)
    have hvb : v ≠ b := fun h => hbS (h ▸ hvS)
    rcases hv with (hv | hv) | hv
    · exact Or.inl ⟨Or.inl ⟨hv, hva⟩, hvb⟩
    · exact Or.inl ⟨Or.inr hv, hvb⟩
    · exact Or.inr ⟨hv, hab.ne.symm, hva⟩
  apply isK5Boundary_anti h₂ ?_ Set.Subset.rfl
  intro x y hxy
  exact ⟨⟨hxy.1, fun heq => haS (heq ▸ hxy.2.1),
    fun heq => haS (heq ▸ hxy.2.2)⟩, hxy.2⟩

end Thomassen
