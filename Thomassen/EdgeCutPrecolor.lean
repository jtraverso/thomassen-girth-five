/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CutPrecolor

/-! Exact prescribed intersections at a cut along a prescribed edge. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a b : V} {S : Set V}

/-- A path from one separator endpoint, avoiding the other endpoint, stays in
one side or meets it only at its initial vertex. -/
lemma path_side_dichotomy_of_avoids_other (ha : a ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z : V} (p : G.Walk a z) (hp : p.IsPath) (hb : b ∉ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a) := by
  cases p with
  | nil => exact Or.inl (by simpa using ha)
  | @cons _ c _ hac p =>
    have havoid : a ∉ p.support := (List.nodup_cons.1 hp.support_nodup).1
    have hbavoid : b ∉ p.support := fun h => hb (List.mem_cons_of_mem _ h)
    have hside : ∀ x ∈ p.support, x ∈ S ↔ c ∈ S := by
      have key : ∀ {z w : V} (q : G.Walk z w), a ∉ q.support → b ∉ q.support →
          ∀ x ∈ q.support, x ∈ S ↔ z ∈ S := by
        intro z w q
        induction q with
        | nil => simp
        | @cons z w t hzw q ih =>
          intro ha' hb' x hx
          have hzA : z ≠ a := fun h => ha' (by simp [h])
          have hzB : z ≠ b := fun h => hb' (by simp [h])
          have hqA : a ∉ q.support := fun h => ha' (by simp [h])
          have hqB : b ∉ q.support := fun h => hb' (by simp [h])
          have hwA : w ≠ a := fun h => hqA (h ▸ q.start_mem_support)
          have hwB : w ≠ b := fun h => hqB (h ▸ q.start_mem_support)
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Iff.rfl
          · exact (ih hqA hqB x hx).trans (hsep hzw hzA hzB hwA hwB).symm
      exact key p havoid hbavoid
    by_cases hc : c ∈ S
    · exact Or.inl (fun x hx => (List.mem_cons.1 hx).elim (fun h => h ▸ ha)
        (fun h => (hside x h).2 hc))
    · refine Or.inr ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact iff_of_true ha rfl
      · exact iff_of_false (fun h => hc ((hside x hx).1 h))
          (fun h => havoid (h ▸ hx))

/-- Oriented-edge version of the exact prescribed path restriction. -/
lemma exists_path_on_oriented_edge_cut (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (he : hab.toWalk.IsSubwalk p) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  obtain ⟨l, r, heq⟩ := he
  have hconcat : (l.concat hab).IsPath := by
    have h := hp
    rw [heq] at h
    exact h.of_append_left
  have hcons : (Walk.cons hab r).IsPath := by
    have h := hp
    rw [heq, ← Walk.append_assoc] at h
    exact h.of_append_right
  have hl : l.IsPath := (Walk.isPath_concat hab).1 hconcat |>.1
  have hr : r.IsPath := hcons.of_cons
  have hbL : b ∉ l.support := (Walk.isPath_concat hab).1 hconcat |>.2
  have haR : a ∉ r.support := (List.nodup_cons.1 hcons.support_nodup).1
  have hvertices : ∀ x, x ∈ p.support ↔ x ∈ l.support ∨ x ∈ r.support := by
    intro x
    rw [heq, Walk.mem_support_append_iff, Walk.mem_support_append_iff]
    simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl hx
      · rcases hx with rfl | rfl
        · exact Or.inl l.end_mem_support
        · exact Or.inr r.start_mem_support
      · exact Or.inr hx
    · exact fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have hedges : ∀ x y, s(x, y) ∈ p.edges ↔
      s(x, y) ∈ l.edges ∨ s(x, y) = s(a, b) ∨ s(x, y) ∈ r.edges := by
    intro x y
    rw [heq, Walk.edges_append, Walk.edges_append]
    simp only [Adj.toWalk, Walk.edges_cons, Walk.edges_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  have hlD := path_side_dichotomy_of_avoids_other ha hsep l.reverse hl.reverse
    (by simpa only [Walk.support_reverse, List.mem_reverse] using hbL)
  simp only [Walk.support_reverse, List.mem_reverse] at hlD
  have hrD := path_side_dichotomy_of_avoids_other hb
    (fun {_ _} hxy hxa hxb hya hyb => hsep hxy hxb hxa hyb hya) r hr haR
  rcases hlD with hlS | hlS <;> rcases hrD with hrS | hrS
  · refine ⟨z, w, p, hp, ?_, fun _ _ _ _ => Iff.rfl⟩
    intro x
    exact ⟨fun hx => ⟨hx, ((hvertices x).1 hx).elim (hlS x) (hrS x)⟩, And.left⟩
  · refine ⟨z, b, l.concat hab, hconcat, ?_, ?_⟩
    · intro x
      simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
      constructor
      · rintro (hx | rfl)
        · exact ⟨(hvertices x).2 (Or.inl hx), hlS x hx⟩
        · exact ⟨(hvertices x).2 (Or.inr r.start_mem_support), hb⟩
      · rintro ⟨hx, hxS⟩
        exact ((hvertices x).1 hx).elim Or.inl (fun h => Or.inr ((hrS x h).1 hxS))
    · intro x y hx hy
      have hnot := not_mem_edges_of_one_vertex_intersection r hrS hx hy
      simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, hedges, hnot, or_false]
  · refine ⟨a, w, Walk.cons hab r, hcons, ?_, ?_⟩
    · intro x
      simp only [Walk.support_cons, List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact ⟨(hvertices x).2 (Or.inl l.end_mem_support), ha⟩
        · exact ⟨(hvertices x).2 (Or.inr hx), hrS x hx⟩
      · rintro ⟨hx, hxS⟩
        exact ((hvertices x).1 hx).elim (fun h => Or.inl ((hlS x h).1 hxS)) Or.inr
    · intro x y hx hy
      have hnot := not_mem_edges_of_one_vertex_intersection l hlS hx hy
      simp only [Walk.edges_cons, List.mem_cons, hedges, hnot, false_or]
  · refine ⟨a, b, hab.toWalk, hab.isPath_toWalk, ?_, ?_⟩
    · intro x
      simp only [Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨(hvertices x).2 (Or.inl l.end_mem_support), ha⟩
        · exact ⟨(hvertices x).2 (Or.inr r.start_mem_support), hb⟩
      · rintro ⟨hx, hxS⟩
        exact ((hvertices x).1 hx).elim
          (fun h => Or.inl ((hlS x h).1 hxS)) (fun h => Or.inr ((hrS x h).1 hxS))
    · intro x y hx hy
      have hlnot := not_mem_edges_of_one_vertex_intersection l hlS hx hy
      have hrnot := not_mem_edges_of_one_vertex_intersection r hrS hx hy
      simp only [Adj.toWalk, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false, hedges, hlnot, hrnot, false_or, or_false]

/-- The exact path restriction works for either orientation of the prescribed
separator edge. Its support, edges and vertex bound can be transported intact. -/
lemma exists_path_on_edge_cut (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (he : s(a, b) ∈ p.edges) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  rcases (Walk.isSubwalk_toWalk_iff_mem_edges hab).2 he with h | h
  · exact exists_path_on_oriented_edge_cut ha hb hab hsep p hp h
  · exact exists_path_on_oriented_edge_cut hb ha hab.symm
      (fun {_ _} hxy hxa hxb hya hyb => hsep hxy hxb hxa hyb hya) p hp h

/-- A simple cycle rooted at one end of a prescribed separator edge lies in
one side or meets it exactly in the two ends of that edge. -/
lemma rooted_cycle_side_dichotomy_on_edge (ha : a ∈ S) (hb : b ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    (p : G.Walk a a) (hp : p.IsCycle) (he : s(a, b) ∈ p.edges) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a ∨ x = b) := by
  cases p with
  | nil => simp at he
  | @cons _ c _ hac q =>
    have hpq : q.IsPath := by
      apply Walk.IsPath.mk'
      simpa only [Walk.support_cons, List.tail_cons] using hp.support_nodup
    have hqnot : ¬ q.Nil := by
      have hlen := hp.three_le_length
      intro hn
      have hz := hn.length_eq_zero
      simp only [Walk.length_cons] at hlen
      omega
    have hqsupport : q.support = q.dropLast.support ++ [a] :=
      (Walk.support_dropLast_concat hqnot).symm
    have havoid : a ∉ q.dropLast.support := by
      have hnd := hpq.support_nodup
      rw [hqsupport] at hnd
      exact fun h => List.disjoint_of_nodup_append hnd h (by simp)
    have hsupport : ∀ x, x ∈ (Walk.cons hac q).support ↔ x = a ∨ x ∈ q.dropLast.support := by
      intro x
      simp only [Walk.support_cons, hqsupport, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false]
      tauto
    have hchain : (∀ x ∈ q.dropLast.support, x ∈ S) ∨
        (∀ x ∈ q.dropLast.support, x ∈ S ↔ x = b) := by
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · have hcb : c = b := by
          rcases Sym2.eq_iff.1 he with h | h
          · exact h.2.symm
          · exact h.1.symm.trans h.2.symm
        subst c
        exact path_side_dichotomy_of_avoids_other hb
          (fun {_ _} hxy hxb hxa hyb hya => hsep hxy hxa hxb hya hyb)
          q.dropLast hpq.dropLast havoid
      · have hbq : b = q.penultimate := hpq.eq_penultimate_of_mem_edges he
        let r := q.dropLast.reverse.copy hbq.symm rfl
        have hr : r.IsPath := (Walk.isPath_copy _ _ _).2 hpq.dropLast.reverse
        have hav : a ∉ r.support := by
          simpa only [r, Walk.support_copy, Walk.support_reverse, List.mem_reverse] using havoid
        have h := path_side_dichotomy_of_avoids_other hb
          (fun {_ _} hxy hxb hxa hyb hya => hsep hxy hxa hxb hya hyb) r hr hav
        simpa only [r, Walk.support_copy, Walk.support_reverse, List.mem_reverse] using h
    rcases hchain with hall | hpoint
    · exact Or.inl (fun x hx => ((hsupport x).1 hx).elim (fun h => h ▸ ha) (hall x))
    · refine Or.inr ?_
      intro x hx
      rcases (hsupport x).1 hx with hxa | hxq
      · subst x
        exact iff_of_true ha (Or.inl rfl)
      · constructor
        · exact fun hxS => Or.inr ((hpoint x hxq).1 hxS)
        · rintro (hxa | hxb)
          · exact hxa ▸ ha
          · exact hxb ▸ hb

/-- Rotation gives the same cycle dichotomy independently of its native root. -/
lemma cycle_side_dichotomy_on_edge (ha : a ∈ S) (hb : b ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {z : V} (p : G.Walk z z) (hp : p.IsCycle) (he : s(a, b) ∈ p.edges) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a ∨ x = b) := by
  have haP := p.fst_mem_support_of_mem_edges he
  let r := p.rotate a haP
  have hr : r.IsCycle := hp.rotate haP
  have heR : s(a, b) ∈ r.edges := (p.rotate_edges a haP).perm.mem_iff.2 he
  rcases rooted_cycle_side_dichotomy_on_edge ha hb hsep r hr heR with h | h
  · exact Or.inl (fun x hx => h x ((p.mem_support_rotate_iff a haP).2 hx))
  · exact Or.inr (fun x hx => h x ((p.mem_support_rotate_iff a haP).2 hx))

/-- Restricting the exact prescription at a two-vertex cut containing one of
its edges again gives a native prescribed path/cycle, even when the old
prescription has vertices on both sides of the cut. -/
lemma BoundaryPrecolor.exists_induce_edge_cut (P : BoundaryPrecolor G)
    (ha : a ∈ S) (hb : b ∈ S) (he : s(a, b) ∈ P.edges)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  have hab := P.adj_of_mem_edges he
  cases P with
  | empty => simp at he
  | path p hp hn =>
    obtain ⟨c, d, q, hq, hvertices, hedges⟩ :=
      exists_path_on_edge_cut ha hb hab hsep p hp (List.mem_toFinset.1 he)
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
    rcases cycle_side_dichotomy_on_edge ha hb hsep p hp (List.mem_toFinset.1 he) with hall | hpoint
    · let Q : BoundaryPrecolor G := .cycle p hp hn
      have hQ : ∀ x ∈ Q.vertices, x ∈ S := fun x hx => hall x (List.mem_toFinset.1 hx)
      exact ⟨Q.induce S hQ, BoundaryPrecolor.mem_vertices_induce Q S hQ,
        BoundaryPrecolor.mem_edges_induce Q S hQ⟩
    · let Q : BoundaryPrecolor G := .path hab.toWalk hab.isPath_toWalk (by
        have h : ({a, b} : Finset V).card ≤ 6 := Finset.card_le_two.trans (by decide)
        simpa only [Adj.support_toWalk, List.toFinset_cons, List.toFinset_nil,
          Finset.insert_empty] using h)
      have hQv : ∀ x, x ∈ Q.vertices ↔ x = a ∨ x = b := by
        intro x
        simp only [Q, BoundaryPrecolor.vertices, List.mem_toFinset, Adj.support_toWalk,
          List.mem_cons, List.not_mem_nil, or_false]
      have hQS : ∀ x ∈ Q.vertices, x ∈ S := fun x hx =>
        ((hQv x).1 hx).elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      have hvertices : ∀ x : S, x.1 ∈ Q.vertices ↔ x.1 ∈ p.support.toFinset := by
        intro x
        rw [hQv, List.mem_toFinset]
        constructor
        · rintro (rfl | rfl)
          · exact p.fst_mem_support_of_mem_edges (List.mem_toFinset.1 he)
          · exact p.snd_mem_support_of_mem_edges (List.mem_toFinset.1 he)
        · intro hx
          exact (hpoint x.1 hx).1 x.2
      have hQe : ∀ x y, s(x, y) ∈ Q.edges ↔ s(x, y) = s(a, b) := by
        intro x y
        simp only [Q, BoundaryPrecolor.edges, Adj.toWalk, Walk.edges_cons, Walk.edges_nil,
          List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]
      refine ⟨Q.induce S hQS, ?_, ?_⟩
      · intro x
        exact (BoundaryPrecolor.mem_vertices_induce Q S hQS x).trans (hvertices x)
      · intro x y
        rw [BoundaryPrecolor.mem_edges_induce, hQe]
        constructor
        · intro heq
          exact heq ▸ he
        · intro hxy
          have hx := (hpoint x.1 (p.fst_mem_support_of_mem_edges (List.mem_toFinset.1 hxy))).1 x.2
          have hy := (hpoint y.1 (p.snd_mem_support_of_mem_edges (List.mem_toFinset.1 hxy))).1 y.2
          have hadj := p.adj_of_mem_edges (List.mem_toFinset.1 hxy)
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · exact (hadj.ne (hx.trans hy.symm)).elim
          · simp only [hx, hy]
          · simp only [hx, hy, Sym2.eq_swap]
          · exact (hadj.ne (hx.trans hy.symm)).elim

end Thomassen
