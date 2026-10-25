/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanExtension

/-! Compatible fan colours retaining original prescribed singletons. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- An external vertex has at most one neighbour on a native path of at most
two edges. Splitting at one neighbour reuses the checked endpoint lemma. -/
lemma external_short_path_neighbour_unique (hg : 5 ≤ G.egirth) {z w a b y : V}
    (p : G.Walk z w) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (ha : a ∈ p.support) (hb : b ∉ p.support) (hba : G.Adj b a)
    (hy : y ∈ p.support) (hby : G.Adj b y) : y = a := by
  let l := (p.takeUntil a ha).reverse
  let r := p.dropUntil a ha
  have heq := p.take_spec ha
  have hsupport : ∀ x, x ∈ p.support ↔ x ∈ l.support ∨ x ∈ r.support := by
    intro x
    rw [← heq, Walk.mem_support_append_iff]
    simp only [l, r, Walk.support_reverse, List.mem_reverse]
  have hsum : l.length + r.length = p.length := by
    simp only [l, r, Walk.length_reverse]
    rw [← Walk.length_append, heq]
  rcases (hsupport y).1 hy with hyl | hyr
  · exact short_path_endpoint_neighbour_unique hg l (hp.takeUntil ha).reverse (by omega)
      (fun h => hb ((hsupport b).2 (Or.inl h))) hba y hyl hby
  · exact short_path_endpoint_neighbour_unique hg r (hp.dropUntil ha) (by omega)
      (fun h => hb ((hsupport b).2 (Or.inr h))) hba y hyr hby

namespace BoundaryInstance

/-- An allowed root colour avoiding its prescribed neighbours extends to all
old short neighbours, respecting their original singleton lists. -/
lemma exists_rootStar_colours_avoiding_precolor (I : BoundaryInstance G C)
    (b : V) (t : C) (ht : t ∈ I.lists b)
    (havoid : ∀ x ∈ I.precolor.vertices, G.Adj b x → I.prescribed x ≠ t) :
    ∃ f : V → C, f b = t ∧ (∀ x ∈ rootStar I b, f x ∈ I.lists x) ∧
      (∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y) := by
  have hchoose : ∀ x, G.Adj b x → (I.lists x).card ≤ 2 → ∃ c ∈ I.lists x, c ≠ t := by
    intro x hbx _
    by_cases hxP : x ∈ I.precolor.vertices
    · exact ⟨I.prescribed x, by simp [I.singleton x hxP], havoid x hxP hbx⟩
    · exact Finset.exists_mem_ne (by have h := I.outside_precolor_list_ge_two hxP; omega) t
  let f : V → C := fun x => if hx : x = b then t else
    if ha : G.Adj b x ∧ (I.lists x).card ≤ 2 then (hchoose x ha.1 ha.2).choose else I.prescribed x
  have hfb : f b = t := by simp only [f, dite_eq_left rfl]
  have hfn : ∀ x (hx : G.Adj b x ∧ (I.lists x).card ≤ 2), f x = (hchoose x hx.1 hx.2).choose := by
    intro x hx
    simp only [f, dite_eq_right hx.1.ne.symm, dite_eq_left hx]
  refine ⟨f, hfb, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact hfb ▸ ht
    · rw [hfn x hx]
      exact (hchoose x hx.1 hx.2).choose_spec.1
  · intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy.ne rfl).elim
    · rw [hfb, hfn y hy]
      exact (hchoose y hy.1 hy.2).choose_spec.2.symm
    · rw [hfn x hx, hfb]
      exact (hchoose x hx.1 hx.2).choose_spec.2
    · exact (neighbors_nonadjacent I.girth hx.1 hy.1 hxy).elim

end BoundaryInstance
end Thomassen
