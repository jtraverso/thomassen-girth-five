/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.EndpointChordCut

/-! Exact restriction of a prescribed path across a mixed edge cut. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Avoiding the second separator vertex makes both branches at the prescribed
separator vertex constant in side membership. The retained native path has
exactly the retained original vertices and edges. -/
lemma exists_path_on_two_cut_avoiding (hv : v ∈ S) (b : V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → x ≠ b → y ≠ v → y ≠ b → (x ∈ S ↔ y ∈ S))
    {a z : V} (p : G.Walk a z) (hp : p.IsPath) (hvp : v ∈ p.support) (hb : b ∉ p.support) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  classical
  let l := p.takeUntil v hvp
  let r := p.dropUntil v hvp
  have hl : l.IsPath := hp.takeUntil hvp
  have hr : r.IsPath := hp.dropUntil hvp
  have heq : l.append r = p := p.take_spec hvp
  have hsupport : ∀ x, x ∈ p.support ↔ x ∈ l.support ∨ x ∈ r.support := by
    intro x
    rw [← heq, Walk.mem_support_append_iff]
  have hedges : ∀ x y, s(x, y) ∈ p.edges ↔ s(x, y) ∈ l.edges ∨ s(x, y) ∈ r.edges := by
    intro x y
    rw [← heq, Walk.edges_append, List.mem_append]
  have hbL : b ∉ l.support := fun h => hb ((hsupport b).2 (Or.inl h))
  have hbR : b ∉ r.support := fun h => hb ((hsupport b).2 (Or.inr h))
  have hleft : (∀ x ∈ l.support, x ∈ S) ∨
      (∀ x ∈ l.support, x ∈ S ↔ x = v) := by
    simpa only [Walk.support_reverse, List.mem_reverse] using path_side_dichotomy_avoiding_other_separator hv hsep l.reverse hl.reverse
      (by simpa only [Walk.support_reverse, List.mem_reverse] using hbL)
  rcases hleft with hlS | hlS <;>
    rcases path_side_dichotomy_avoiding_other_separator hv hsep r hr hbR with hrS | hrS
  · refine ⟨a, z, p, hp, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        refine ⟨hx, ?_⟩
        rcases (hsupport x).1 hx with hx | hx
        · exact hlS x hx
        · exact hrS x hx
      · exact And.left
    · intro x y _ _
      exact Iff.rfl
  · refine ⟨a, v, l, hl, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact ⟨(hsupport x).2 (Or.inl hx), hlS x hx⟩
      · rintro ⟨hx, hxS⟩
        rcases (hsupport x).1 hx with hx | hx
        · exact hx
        · have hxv := (hrS x hx).1 hxS
          exact hxv ▸ l.end_mem_support
    · intro x y hx hy
      rw [hedges]
      exact ⟨Or.inl, fun h => h.resolve_right
        (not_mem_edges_of_one_vertex_intersection r hrS hx hy)⟩
  · refine ⟨v, z, r, hr, ?_, ?_⟩
    · intro x
      constructor
      · intro hx
        exact ⟨(hsupport x).2 (Or.inr hx), hrS x hx⟩
      · rintro ⟨hx, hxS⟩
        rcases (hsupport x).1 hx with hx | hx
        · have hxv := (hlS x hx).1 hxS
          exact hxv ▸ r.start_mem_support
        · exact hx
    · intro x y hx hy
      rw [hedges]
      exact ⟨Or.inr, fun h => h.resolve_left
        (not_mem_edges_of_one_vertex_intersection l hlS hx hy)⟩
  · refine ⟨v, v, .nil, by simp, ?_, ?_⟩
    · intro x
      simp only [Walk.support_nil, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨hvp, hv⟩
      · rintro ⟨hx, hxS⟩
        rcases (hsupport x).1 hx with hx | hx
        · exact (hlS x hx).1 hxS
        · exact (hrS x hx).1 hxS
    · intro x y hx hy
      have hlE := not_mem_edges_of_one_vertex_intersection l hlS hx hy
      have hrE := not_mem_edges_of_one_vertex_intersection r hrS hx hy
      simp only [Walk.edges_nil, List.not_mem_nil, hedges, hlE, hrE, or_self]


/-- A mixed cut retains an exact native prescribed path, with its original
six-vertex bound. No assumption about one-sided placement is needed. -/
lemma exists_induce_path_two_cut (P : BoundaryPrecolor G)
    {a t : V} (p : G.Walk a t) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : P = .path p hp hn) (hv : v ∈ S) (hvp : v ∈ P.vertices)
    (b : V) (hb : b ∉ P.vertices)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → x ≠ b → y ≠ v → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  subst P
  obtain ⟨c, d, q, hq, hvertices, hedges⟩ := exists_path_on_two_cut_avoiding hv b hsep p hp
    (List.mem_toFinset.1 hvp) (fun h => hb (List.mem_toFinset.2 h))
  have hsmall : q.support.toFinset.card ≤ 6 :=
    (Finset.card_le_card (fun x hx => List.mem_toFinset.2
      ((hvertices x).1 (List.mem_toFinset.1 hx)).1)).trans hn
  let Q : BoundaryPrecolor G := .path q hq hsmall
  have hQ : ∀ x ∈ Q.vertices, x ∈ S :=
    fun x hx => ((hvertices x).1 (List.mem_toFinset.1 hx)).2
  refine ⟨Q.induce S hQ, ?_, ?_⟩
  · intro x
    rw [BoundaryPrecolor.mem_vertices_induce]
    change x.1 ∈ q.support.toFinset ↔ x.1 ∈ p.support.toFinset
    simp only [List.mem_toFinset, hvertices, and_iff_left x.2]
  · intro x y
    rw [BoundaryPrecolor.mem_edges_induce]
    change s(x.1, y.1) ∈ q.edges.toFinset ↔ s(x.1, y.1) ∈ p.edges.toFinset
    simpa only [List.mem_toFinset] using hedges x.1 y.1 x.2 y.2

end Thomassen
