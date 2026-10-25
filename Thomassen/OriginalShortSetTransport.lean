/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFiveFaceUniqueness

/-! Restriction and list normalization for the original exceptional invariant. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v w
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Removing marks from the original short set preserves its shape and its
original distinguished-endpoint two-path exclusion. -/
theorem OriginalShortSet.mono (A : Set V) (hA : OriginalShortSet G A)
    (B : Set V) (hBA : B ⊆ A) : OriginalShortSet G B := by
  rcases hA with hA | ⟨x,y,hx,hy,hxy,hedge,hNo⟩
  · exact Or.inl (fun r hr s hs hrs => hA r (hBA hr) s (hBA hs) hrs)
  · by_cases hxyB : x ∈ B ∧ y ∈ B
    · exact Or.inr ⟨x,y,hxyB.1,hxyB.2,hxy,
        fun r hr s hs hrs => hedge r (hBA hr) s (hBA hs) hrs,
        fun z hz p hp hlen => hNo z (hBA hz) p hp hlen⟩
    · left
      intro r hr s hs hrs
      rcases hedge r (hBA hr) s (hBA hs) hrs with h | h
      · exact hxyB ⟨h.1 ▸ hr,h.2 ▸ hs⟩
      · exact hxyB ⟨h.2 ▸ hs,h.1 ▸ hr⟩

/-- Pull back the short-set condition through a genuine graph embedding.
This includes the flattening of a component after deletion. -/
theorem OriginalShortSet.comap {W : Type w} {H : SimpleGraph W}
    (A : Set V) (hA : OriginalShortSet G A) (f : H ↪g G) :
    OriginalShortSet H (f ⁻¹' A) := by
  rcases hA with hA | ⟨x,y,hx,hy,hxy,hedge,hNo⟩
  · exact Or.inl (fun r hr s hs hrs => hA (f r) hr (f s) hs (f.toHom.map_adj hrs))
  · by_cases hpre : (∃ r, f r = x) ∧ (∃ s, f s = y)
    · obtain ⟨⟨r,hr⟩,⟨s,hs⟩⟩ := hpre
      refine Or.inr ⟨r,s,?_,?_,?_,?_,?_⟩
      · change f r ∈ A
        rwa [hr]
      · change f s ∈ A
        rwa [hs]
      · apply f.map_rel_iff.1
        rwa [hr,hs]
      · intro a ha b hb hab
        rcases hedge (f a) ha (f b) hb (f.toHom.map_adj hab) with h | h
        · exact Or.inl ⟨f.injective (h.1.trans hr.symm),f.injective (h.2.trans hs.symm)⟩
        · exact Or.inr ⟨f.injective (h.1.trans hs.symm),f.injective (h.2.trans hr.symm)⟩
      · intro z hz p hp hlen
        let hpath := p.map f.toHom
        have hp' : hpath.IsPath := by
          change (p.map f.toHom).IsPath
          exact hp.map f.injective
        have hlen' : hpath.length = 2 := (Walk.length_map f.toHom p).trans hlen
        apply hNo (f z) hz (hpath.copy hr rfl)
        · exact (Walk.isPath_copy _ _ _).2 hp'
        · simpa only [Walk.length_copy] using hlen'
    · left
      intro a ha b hb hab
      rcases hedge (f a) ha (f b) hb (f.toHom.map_adj hab) with h | h
      · exact hpre ⟨⟨a,h.1⟩,⟨b,h.2⟩⟩
      · exact hpre ⟨⟨b,h.2⟩,⟨a,h.1⟩⟩

namespace OriginalBoundaryInstance

/-- Every actual short list is marked in the original input. -/
theorem mem_short_of_list_card_le_two (I : OriginalBoundaryInstance G C) {x : V}
    (hx : (I.lists x).card ≤ 2) : x ∈ I.short := by
  by_contra hn
  have := I.list_three x hn
  omega

/-- Mark exactly the lists of size two. Lists, fixed colours and graph are
unchanged, and the original shape condition is proved by monotonicity. -/
def pruneShort (I : OriginalBoundaryInstance G C) : OriginalBoundaryInstance G C := {
  I with
  short := {x | (I.lists x).card ≤ 2}
  on_outer := fun x hx => I.on_outer x (I.mem_short_of_list_card_le_two hx)
  short_shape := I.short_shape.mono I.short {x | (I.lists x).card ≤ 2}
    (fun _ hx => I.mem_short_of_list_card_le_two hx)
  list_three := by intro x hx; change ¬ (I.lists x).card ≤ 2 at hx; omega }

theorem pruneShort_extends_iff (I : OriginalBoundaryInstance G C) :
    I.pruneShort.Extends ↔ I.Extends := Iff.rfl

/-- In the pruned original invariant, every marked list has cardinality two. -/
theorem pruneShort_list_card (I : OriginalBoundaryInstance G C) {x : V}
    (hx : x ∈ I.pruneShort.short) : (I.pruneShort.lists x).card = 2 := by
  have htwo := I.list_two x
  change (I.lists x).card ≤ 2 at hx
  change (I.lists x).card = 2
  omega

end OriginalBoundaryInstance
end Thomassen
