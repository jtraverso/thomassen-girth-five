/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EdgeStarExtension

/-! Compatible short-neighbour colours from a properly coloured edge. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance

/-- Any two allowed distinct edge colours extend independently to all old
short neighbours. Girth excludes a shared neighbour; the original invariant
excludes edges between the added short vertices. -/
lemma exists_edgeStar_colours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b)
    (htab : ta ≠ tb) :
    ∃ f : V → C, f a = ta ∧ f b = tb ∧ (∀ x ∈ edgeStar I a b, f x ∈ I.lists x) ∧
      (∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y) := by
  have hshort : ∀ x ∈ edgeStar I a b, x ≠ a → x ≠ b → (I.lists x).card ≤ 2 := by
    intro x hx hxa hxb
    rcases hx with (h | h) | (h | h)
    · exact (hxa h).elim
    · exact h.2
    · exact (hxb h).elim
    · exact h.2
  have hchoose : ∀ x ∈ edgeStar I a b, x ≠ a → x ≠ b →
      ∃ t ∈ I.lists x, (G.Adj a x → t ≠ ta) ∧ (G.Adj b x → t ≠ tb) := by
    intro x hx _ _
    have hcard : 1 < (I.lists x).card := by
      have h := I.outside_precolor_list_ge_two (x := x)
        (by simp only [hP, BoundaryPrecolor.vertices_empty, Finset.notMem_empty, not_false_eq_true])
      omega
    by_cases hax : G.Adj a x
    · obtain ⟨t, ht, hta⟩ := Finset.exists_mem_ne hcard ta
      exact ⟨t, ht, fun _ => hta, fun hbx => (neighbors_nonadjacent I.girth hab hax hbx).elim⟩
    · obtain ⟨t, ht, htb⟩ := Finset.exists_mem_ne hcard tb
      exact ⟨t, ht, fun h => (hax h).elim, fun _ => htb⟩
  let f : V → C := fun x => if ha : x = a then ta else if hb : x = b then tb else
    if hs : x ∈ edgeStar I a b then (hchoose x hs ha hb).choose else I.prescribed x
  have hfa : f a = ta := by simp only [f, dite_eq_left rfl]
  have hfb : f b = tb := by simp [f, hab.ne.symm]
  have hfx : ∀ x (hx : x ∈ edgeStar I a b) (hxa : x ≠ a) (hxb : x ≠ b),
      f x = (hchoose x hx hxa hxb).choose := by
    intro x hx hxa hxb
    simp only [f, dite_eq_right hxa, dite_eq_right hxb, dite_eq_left hx]
  have havoidA : ∀ x ∈ edgeStar I a b, G.Adj a x → f x ≠ f a := by
    intro x hx hax
    rw [hfa]
    by_cases hxb : x = b
    · rw [hxb, hfb]
      exact htab.symm
    · rw [hfx x hx hax.ne.symm hxb]
      exact (hchoose x hx hax.ne.symm hxb).choose_spec.2.1 hax
  have havoidB : ∀ x ∈ edgeStar I a b, G.Adj b x → f x ≠ f b := by
    intro x hx hbx
    rw [hfb]
    by_cases hxa : x = a
    · rw [hxa, hfa]
      exact htab
    · rw [hfx x hx hxa hbx.ne.symm]
      exact (hchoose x hx hxa hbx.ne.symm).choose_spec.2.2 hbx
  refine ⟨f, hfa, hfb, ?_, ?_⟩
  · intro x hx
    by_cases hxa : x = a
    · rw [hxa, hfa]; exact hta
    · by_cases hxb : x = b
      · rw [hxb, hfb]; exact htb
      · rw [hfx x hx hxa hxb]
        exact (hchoose x hx hxa hxb).choose_spec.1
  · intro x hx y hy hxy
    by_cases hxa : x = a
    · subst x; exact (havoidA y hy hxy).symm
    · by_cases hxb : x = b
      · subst x; exact (havoidB y hy hxy).symm
      · by_cases hya : y = a
        · subst y; exact havoidA x hx hxy.symm
        · by_cases hyb : y = b
          · subst y; exact havoidB x hx hxy.symm
          · have he := I.short_edges hxy (hshort x hx hxa hxb) (hshort y hy hya hyb)
            simp only [hP, BoundaryPrecolor.edges_empty, Finset.notMem_empty] at he

end BoundaryInstance
end Thomassen
