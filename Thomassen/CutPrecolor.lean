/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedInstance

/-! Restricting a prescribed path at a cutvertex. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Along a walk avoiding the separating vertex, membership in a cut side is
constant. The hypothesis allows crossing edges only at that vertex. -/
lemma walk_side_of_avoids_cut
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (p : G.Walk a b) (havoid : v ∉ p.support) :
    ∀ x ∈ p.support, x ∈ S ↔ a ∈ S := by
  induction p with
  | nil => simpa only [Walk.support_nil, List.mem_singleton] using fun x hx => hx ▸ Iff.rfl
  | @cons a b c hab p ih =>
    have hav : a ≠ v := fun h => havoid (by simp [h])
    have hb : b ≠ v := fun h =>
      havoid (List.mem_cons_of_mem _ (h ▸ p.start_mem_support))
    have ht : v ∉ p.support := fun h => havoid (by simp [h])
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Iff.rfl
    · exact (ih ht x hx).trans (hsep hab hav hb).symm

/-- A simple path starting at the cutvertex either lies wholly in a side, or
meets that side only at its first vertex. -/
lemma path_side_dichotomy (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a : V} (p : G.Walk v a) (hp : p.IsPath) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = v) := by
  cases p with
  | nil => exact Or.inl (by simpa using hv)
  | @cons _ b _ hvb p =>
    have havoid : v ∉ p.support := (List.nodup_cons.1 hp.support_nodup).1
    have hside := walk_side_of_avoids_cut hsep p havoid
    by_cases hb : b ∈ S
    · refine Or.inl ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hv
      · exact (hside x hx).2 hb
    · refine Or.inr ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact iff_of_true hv rfl
      · have hxout : x ∉ S := fun h => hb ((hside x hx).1 h)
        have hxv : x ≠ v := fun h => havoid (h ▸ hx)
        exact iff_of_false hxout hxv

/-- A branch meeting a side at only one vertex contributes no edge inside it. -/
lemma not_mem_edges_of_one_vertex_intersection {a b : V} (p : G.Walk a b)
    (hp : ∀ x ∈ p.support, x ∈ S ↔ x = v)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : s(x, y) ∉ p.edges := by
  intro he
  have hxv := (hp x (p.fst_mem_support_of_mem_edges he)).1 hx
  have hyv := (hp y (p.snd_mem_support_of_mem_edges he)).1 hy
  exact (p.adj_of_mem_edges he).ne (hxv.trans hyv.symm)

/-- The intersection of a simple path with a cut side containing a vertex of
that path is again a simple path. Its vertex and edge sets are exact. -/
lemma exists_path_on_cut_side (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hvp : v ∈ p.support) :
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
  have hleft : (∀ x ∈ l.support, x ∈ S) ∨
      (∀ x ∈ l.support, x ∈ S ↔ x = v) := by
    simpa only [Walk.support_reverse, List.mem_reverse] using path_side_dichotomy hv hsep l.reverse hl.reverse
  rcases hleft with hlS | hlS <;>
    rcases path_side_dichotomy hv hsep r hr with hrS | hrS
  · refine ⟨a, b, p, hp, ?_, ?_⟩
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
  · refine ⟨v, b, r, hr, ?_, ?_⟩
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

/-- A simple cycle through a cutvertex lies in a side or meets it only at the
cutvertex. Removing its repeated last vertex gives the required simple path. -/
lemma cycle_side_dichotomy (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hvp : v ∈ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = v) := by
  classical
  let c := p.rotate v hvp
  have hc : c.IsCycle := hp.rotate hvp
  have hsame : ∀ x, x ∈ c.dropLast.support ↔ x ∈ p.support := by
    intro x
    have hmem : x ∈ c.support ↔ x ∈ c.dropLast.support ∨ x = v := by
      rw [← Walk.support_dropLast_concat hc.not_nil, List.mem_append, List.mem_singleton]
    have hvq : v ∈ c.dropLast.support := c.dropLast.start_mem_support
    have hiff : x ∈ c.dropLast.support ↔ x ∈ c.support := by
      rw [hmem]
      exact ⟨Or.inl, fun h => h.elim id (fun h => h ▸ hvq)⟩
    exact hiff.trans (p.mem_support_rotate_iff v hvp)
  rcases path_side_dichotomy hv hsep c.dropLast hc.isPath_dropLast with h | h
  · exact Or.inl (fun x hx => h x ((hsame x).2 hx))
  · exact Or.inr (fun x hx => h x ((hsame x).2 hx))

/-- The exact precoloured subgraph retained on either side of a cut through a
precoloured vertex is again an admissible path/cycle of at most six vertices. -/
lemma BoundaryPrecolor.exists_induce_cut (P : BoundaryPrecolor G)
    (hv : v ∈ S) (hvp : v ∈ P.vertices)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  classical
  cases P with
  | empty => simp at hvp
  | path p hp hn =>
    obtain ⟨a, b, q, hq, hvertices, hedges⟩ :=
      exists_path_on_cut_side hv hsep p hp (List.mem_toFinset.1 hvp)
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
  | cycle p hp hn =>
    rcases cycle_side_dichotomy hv hsep p hp (List.mem_toFinset.1 hvp) with hall | hpoint
    · let Q : BoundaryPrecolor G := .cycle p hp hn
      have hQ : ∀ x ∈ Q.vertices, x ∈ S := fun x hx => hall x (List.mem_toFinset.1 hx)
      exact ⟨Q.induce S hQ, BoundaryPrecolor.mem_vertices_induce Q S hQ,
        BoundaryPrecolor.mem_edges_induce Q S hQ⟩
    · let Q : BoundaryPrecolor (G.induce S) := .path (.nil (u := ⟨v, hv⟩))
        (by simp) (by simp)
      refine ⟨Q, ?_, ?_⟩
      · intro x
        change x ∈ (Walk.nil (G := G.induce S) (u := ⟨v, hv⟩)).support.toFinset ↔
          x.1 ∈ p.support.toFinset
        simp only [Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert, Finset.notMem_empty, or_false, List.mem_toFinset]
        constructor
        · rintro rfl
          exact List.mem_toFinset.1 hvp
        · intro hx
          exact Subtype.ext ((hpoint x.1 hx).1 x.2)
      · intro x y
        have hnot := not_mem_edges_of_one_vertex_intersection p hpoint x.2 y.2
        change s(x, y) ∈ (Walk.nil (G := G.induce S) (u := ⟨v, hv⟩)).edges.toFinset ↔
          s(x.1, y.1) ∈ p.edges.toFinset
        simp [hnot]

/-- Every cut side containing the separating vertex is connected when the
original graph is connected. Simple paths cannot leave and re-enter that side. -/
lemma preconnected_cut_side (hconn : G.Preconnected) (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S)) :
    (G.induce S).Preconnected := by
  classical
  have hroot : ∀ x : S, (G.induce S).Reachable ⟨v, hv⟩ x := by
    intro x
    obtain ⟨p, hp⟩ := (hconn v x.1).exists_isPath
    rcases path_side_dichotomy hv hsep p hp with hall | hpoint
    · exact ⟨p.induce S hall⟩
    · have heq : x.1 = v := (hpoint x.1 p.end_mem_support).1 x.2
      have heq' : x = ⟨v, hv⟩ := Subtype.ext heq
      rw [heq']
  exact fun x y => (hroot x).symm.trans (hroot y)

/-- Disconnection after deleting `v` supplies a genuine nontrivial cut side. -/
lemma exists_cut_side_of_delete_disconnected
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, v ∈ S ∧ (∃ a ∈ S, a ≠ v) ∧ (∃ b, b ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S) := by
  classical
  have hpair : ∃ a b : (({v} : Set V)ᶜ : Set V),
      ¬ (G.induce ({v} : Set V)ᶜ).Reachable a b := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hdisc
  obtain ⟨a, b, hab⟩ := hpair
  let S : Set V := {x | x = v ∨ ∃ hx : x ≠ v,
    (G.induce ({v} : Set V)ᶜ).Reachable a ⟨x, hx⟩}
  have hmem : ∀ x (hx : x ≠ v), x ∈ S ↔
      (G.induce ({v} : Set V)ᶜ).Reachable a ⟨x, hx⟩ := by
    intro x hx
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact (hx h).elim
      · exact h
    · exact fun h => Or.inr ⟨hx, h⟩
  refine ⟨S, Or.inl rfl, ⟨a.1, Or.inr ⟨a.2, .refl _⟩, a.2⟩,
    ⟨b.1, fun h => hab ((hmem b.1 b.2).1 h)⟩, ?_⟩
  intro x y hxy hx hy
  rw [hmem x hx, hmem y hy]
  exact ⟨fun h => h.trans (show (G.induce ({v} : Set V)ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩
    from hxy).reachable,
    fun h => h.trans (show (G.induce ({v} : Set V)ᶜ).Adj ⟨y, hy⟩ ⟨x, hx⟩
      from hxy.symm).reachable⟩

namespace BoundaryInstance
universe w
variable {C : Type w} [Fintype V]

/-- The full cutvertex reduction when the separating vertex is prescribed.
Both smaller instances retain the exact appropriate subpath/cycle and their
colourings agree at the prescribed singleton. -/
lemma colourable_of_precolored_cutvertex (I : BoundaryInstance G C) (v : V)
    (hvP : v ∈ I.precolor.vertices) (hconn : G.Preconnected)
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  classical
  obtain ⟨S, hv, ⟨a, ha, hav⟩, ⟨b, hb⟩, hsep⟩ :=
    exists_cut_side_of_delete_disconnected hdisc
  let T : Set V := insert v Sᶜ
  have hvT : v ∈ T := Or.inl rfl
  have hbT : b ∈ T := Or.inr hb
  have hbv : b ≠ v := fun h => hb (h ▸ hv)
  have haT : a ∉ T := by simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff,
    hav, false_or, not_not] using ha
  let : Nontrivial S := ⟨⟨⟨a, ha⟩, ⟨v, hv⟩, fun h => hav (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨b, hbT⟩, ⟨v, hvT⟩, fun h => hbv (congrArg Subtype.val h)⟩⟩
  have hsepT : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ T ↔ y ∈ T) := by
    intro x y hxy hx hy
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, hx, hy, false_or] using
      not_congr (hsep hxy hx hy)
  obtain ⟨PS, hPSv, hPSe⟩ := I.precolor.exists_induce_cut hv hvP hsep
  obtain ⟨PT, hPTv, hPTe⟩ := I.precolor.exists_induce_cut hvT hvP hsepT
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S)
    (I.inducePrecolor S (preconnected_cut_side hconn hv hsep) PS hPSv hPSe)
    (card_induced_vertices_lt S hb)
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T)
    (I.inducePrecolor T (preconnected_cut_side hconn hvT hsepT) PT hPTv hPTe)
    (card_induced_vertices_lt T haT)
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcS
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcT
  refine glue_induced_colourings S T I.lists ?_ ?_ cS cT hS hT ?_
  · intro x
    exact Classical.em (x ∈ S) |>.imp_right (fun h => Or.inr h)
  · intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact Or.inl ⟨hx, hy⟩
      · have hxv : x = v := by
          by_contra hxv
          exact hy ((hsep hxy hxv (fun h => hy (h ▸ hv))).1 hx)
        exact Or.inr ⟨Or.inl hxv, Or.inr hy⟩
    · by_cases hy : y ∈ S
      · have hyv : y = v := by
          by_contra hyv
          exact hx ((hsep hxy (fun h => hx (h ▸ hv)) hyv).2 hy)
        exact Or.inr ⟨Or.inr hx, Or.inl hyv⟩
      · exact Or.inr ⟨Or.inr hx, Or.inr hy⟩
  · intro x hx hy
    rcases hy with heq | hy
    · subst x
      have hcvS : cS ⟨v, hv⟩ = I.prescribed v :=
        Finset.mem_singleton.1 (by simpa only [I.singleton v hvP] using hS ⟨v, hv⟩)
      have hcvT : cT ⟨v, hvT⟩ = I.prescribed v :=
        Finset.mem_singleton.1 (by simpa only [I.singleton v hvP] using hT ⟨v, hvT⟩)
      exact hcvS.trans hcvT.symm
    · exact (hy hx).elim

end BoundaryInstance

end Thomassen
