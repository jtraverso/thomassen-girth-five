/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.Lists

/-!
# Vertex deletion and minimal uncolourable list instances

These statements use `Col` and `restrict` from the registered planar-list-colouring
package. The extension proof calls its existing `col_extend` lemma.
-/

@[expose] public section
open Finset LeanPool.K5MinorFreeChoosability
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A partial colouring in the old API is exactly a list-respecting function proper
on the induced vertex set. -/
lemma col_restrict_iff (S : Finset V) (L : V → Finset C) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ↔
      ∃ c : V → C, (∀ a ∈ S, c a ∈ L a) ∧
        ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → c a ≠ c b := by
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, fun a ha b hb hab => hp a b ⟨hab, ha, hb⟩⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, fun a b hab => hp a hab.2.1 b hab.2.2 hab.1⟩

lemma col_univ_iff [Fintype V] (L : V → Finset C) :
    Col (restrict G (↑(univ : Finset V) : Set V)) univ L
      (fun _ _ x y => x = y) ↔ ListColourable G L := by
  rw [col_restrict_iff]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨SimpleGraph.Coloring.mk c (fun hab => hp _ (mem_univ _) _ (mem_univ _) hab),
      fun a => hc a (mem_univ a)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun a _ => hc a, fun a _ b _ hab => c.valid hab⟩

/-- A vertex with fewer remaining neighbours than list colours can be restored.
The gluing operation is the already verified `col_extend`. -/
lemma col_of_erase (S : Finset V) (L : V → Finset C) (w : V)
    (hc : Col (restrict G (↑(S.erase w) : Set V)) (S.erase w) L
      (fun _ _ x y => x = y))
    (hdeg : ((S.erase w).filter (G.Adj w)).card < (L w).card) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) := by
  classical
  obtain ⟨c, hc, hp⟩ := hc
  obtain ⟨x, hxL, hxN⟩ := exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt (card_image_le (s := (S.erase w).filter (G.Adj w)) (f := c)) hdeg)
  apply col_extend (G := restrict G (↑S : Set V)) (v := w)
    (fun _ _ h => h.2.1) IsCorrespondence.eq (fun _ _ _ => Subset.rfl) c hc
    (fun a b h => hp a b ⟨h.1.1, h.2⟩) x hxL
  intro b hwb heq
  apply hxN
  rw [heq]
  exact mem_image_of_mem c (mem_filter.2
    ⟨mem_erase.2 ⟨hwb.1.ne.symm, hwb.2.2⟩, hwb.1⟩)

/-- Minimality is with respect to vertex deletion, with the original lists fixed. -/
def MinimalBad (G : SimpleGraph V) (S : Finset V) (L : V → Finset C) : Prop :=
  ¬ Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ∧
    ∀ T ⊂ S, Col (restrict G (↑T : Set V)) T L (fun _ _ x y => x = y)

lemma minimal_bad_exists (S : Finset V) (L : V → Finset C)
    (hbad : ¬ Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y)) :
    ∃ T ⊆ S, MinimalBad G T L := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hmin : ∀ T ⊂ S,
        Col (restrict G (↑T : Set V)) T L (fun _ _ x y => x = y)
    · exact ⟨S, Subset.rfl, hbad, hmin⟩
    · push Not at hmin
      obtain ⟨T, hTS, hT⟩ := hmin
      obtain ⟨U, hUT, hU⟩ := ih T hTS hT
      exact ⟨U, hUT.trans hTS.subset, hU⟩

/-- Every vertex of a minimal uncolourable instance has at least as many neighbours
inside that instance as it has colours in its list. -/
lemma minimal_bad_degree {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) {w : V} (hw : w ∈ S) :
    (L w).card ≤ ((S.erase w).filter (G.Adj w)).card := by
  by_contra hn
  exact h.1 (col_of_erase S L w (h.2 _ (erase_ssubset hw)) (lt_of_not_ge hn))

lemma minimal_bad_nonempty [Nonempty C] {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) : S.Nonempty := by
  by_contra hn
  have hS : S = ∅ := not_nonempty_iff_eq_empty.1 hn
  apply h.1
  rw [hS, col_restrict_iff]
  exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩

/-- A minimal uncolourable instance is connected. The two hypothetical components
are glued by `col_glue` from the existing planar-colouring proof. -/
lemma minimal_bad_connSet [Nonempty C] {S : Finset V} {L : V → Finset C}
    (h : MinimalBad G S L) : ConnSet G (↑S : Set V) := by
  classical
  obtain ⟨x, hx⟩ := minimal_bad_nonempty h
  refine ⟨⟨x, hx⟩, ?_⟩
  suffices hr : ∀ y ∈ S, RIn G (↑S : Set V) x y by
    exact fun a ha b hb => (hr a ha).symm.trans (hr b hb)
  intro y hy
  by_contra hxy
  let A := S.filter (fun a => RIn G (↑S : Set V) x a)
  let B := S \ A
  have hxA : x ∈ A := mem_filter.2 ⟨hx, RIn.refl x⟩
  have hyA : y ∉ A := fun hyA => hxy (mem_filter.1 hyA).2
  have hAS : A ⊂ S := Finset.ssubset_iff_subset_ne.2
    ⟨filter_subset _ _, fun heq => hyA (heq.symm ▸ hy)⟩
  have hBS : B ⊂ S := Finset.ssubset_iff_subset_ne.2
    ⟨sdiff_subset, fun heq => (mem_sdiff.1 (heq.symm ▸ hx)).2 hxA⟩
  obtain ⟨c, hc, hp⟩ := h.2 A hAS
  obtain ⟨d, hd, hq⟩ := h.2 B hBS
  apply h.1
  apply col_glue (G := restrict G (↑S : Set V)) (S₁ := A) (S₂ := B)
    (fun a ha => by
      by_cases hA : a ∈ A
      · exact mem_union_left _ hA
      · exact mem_union_right _ (mem_sdiff.2 ⟨ha, hA⟩))
    (fun a b hab => ?_) c d hc (fun a ha _ => hd a ha)
    (fun a b hab ha hb => hp a b ⟨hab.1, ha, hb⟩)
    (fun a b hab ha hb => hq a b ⟨hab.1, ha, hb⟩)
    (fun a ha hb => False.elim ((mem_sdiff.1 hb).2 ha))
  by_cases ha : a ∈ A
  · exact Or.inl ⟨ha, mem_filter.2 ⟨hab.2.2,
      (mem_filter.1 ha).2.tail hab.1 hab.2.1 hab.2.2⟩⟩
  · exact Or.inr ⟨mem_sdiff.2 ⟨hab.2.1, ha⟩, mem_sdiff.2 ⟨hab.2.2, fun hb =>
      ha (mem_filter.2 ⟨hab.2.1, (mem_filter.1 hb).2.tail hab.1.symm hab.2.2 hab.2.1⟩)⟩⟩

end Thomassen
