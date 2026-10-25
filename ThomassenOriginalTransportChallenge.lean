module
public import Thomassen.OriginalInstance

/-! Independent contracts for short-set transport and pruning. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v w
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

theorem OriginalShortSet.mono (A : Set V) (hA : OriginalShortSet G A)
    (B : Set V) (hBA : B ⊆ A) : OriginalShortSet G B := by
  sorry

theorem OriginalShortSet.comap {W : Type w} {H : SimpleGraph W}
    (A : Set V) (hA : OriginalShortSet G A) (f : H ↪g G) :
    OriginalShortSet H (f ⁻¹' A) := by
  sorry

theorem OriginalBoundaryInstance.mem_short_of_list_card_le_two (I : OriginalBoundaryInstance G C) {x : V}
    (hx : (I.lists x).card ≤ 2) : x ∈ I.short := by
  sorry

def OriginalBoundaryInstance.pruneShort (I : OriginalBoundaryInstance G C) : OriginalBoundaryInstance G C := {
  I with
  short := {x | (I.lists x).card ≤ 2}
  on_outer := fun x hx => I.on_outer x (I.mem_short_of_list_card_le_two hx)
  short_shape := I.short_shape.mono I.short {x | (I.lists x).card ≤ 2}
    (fun _ hx => I.mem_short_of_list_card_le_two hx)
  list_three := by intro x hx; change ¬ (I.lists x).card ≤ 2 at hx; omega }


theorem OriginalBoundaryInstance.pruneShort_extends_iff (I : OriginalBoundaryInstance G C) :
    I.pruneShort.Extends ↔ I.Extends := by
  sorry

theorem OriginalBoundaryInstance.pruneShort_list_card (I : OriginalBoundaryInstance G C) {x : V}
    (hx : x ∈ I.pruneShort.short) : (I.pruneShort.lists x).card = 2 := by
  sorry

end Thomassen
