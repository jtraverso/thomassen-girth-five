/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FacialFiveReduction
public import Thomassen.FaceBoundary
public import LeanPool.K5MinorFreeChoosability.Planar.FaceApex

/-! A boundary minor obstruction for choosing a removable facial six-cycle vertex. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Four pairwise adjacent disjoint connected bags meeting a minor-free
boundary would give a fifth bag at its apex. -/
lemma not_isK5Boundary_of_rooted_four_bags (B : Set V) (X : Fin 4 → Finset V)
    (hconn : ∀ i, ConnSet G ↑(X i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hadj : ∀ i j, i ≠ j → ∃ a ∈ X i, ∃ b ∈ X j, G.Adj a b)
    (hroot : ∀ i, ∃ a ∈ X i, a ∈ B) : ¬ IsK5Boundary G B := by
  intro hB
  let br : Fin 5 → Finset (Option V) := fun i =>
    if h : i.val < 4 then (X ⟨i.val, h⟩).image some else {none}
  apply hB
  refine ⟨CliqueMinorModel.ofConnSet br ?_ ?_ ?_⟩
  · intro i
    by_cases hi : i.val < 4
    · simpa only [br, dite_eq_left hi] using connSet_image_some (B := B) (hconn ⟨i.val, hi⟩)
    · simpa only [br, dite_eq_right hi, Finset.coe_singleton] using
        connSet_singleton (apexExtend G B) none
  · intro i j hij
    by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
    · simp only [br, dite_eq_left hi, dite_eq_left hj]
      apply (Finset.disjoint_image (Option.some_injective V)).2
      exact hdisj ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun h => hij (Fin.ext (congrArg (fun t : Fin 4 => t.val) h)))
    · simp only [br, dite_eq_left hi, dite_eq_right hj, Finset.disjoint_singleton_right]
      simp
    · simp only [br, dite_eq_right hi, dite_eq_left hj, Finset.disjoint_singleton_left]
      simp
    · exact (hij (Fin.ext (by omega))).elim
  · intro i j hij
    by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
    · obtain ⟨a, ha, b, hb, hab⟩ := hadj ⟨i.val, hi⟩ ⟨j.val, hj⟩
        (fun h => hij (Fin.ext (congrArg (fun t : Fin 4 => t.val) h)))
      refine ⟨some a, ?_, some b, ?_, hab⟩
      · simpa only [br, dite_eq_left hi] using Finset.mem_image_of_mem some ha
      · simpa only [br, dite_eq_left hj] using Finset.mem_image_of_mem some hb
    · obtain ⟨a, ha, haB⟩ := hroot ⟨i.val, hi⟩
      refine ⟨some a, ?_, none, ?_, haB⟩
      · simpa only [br, dite_eq_left hi] using Finset.mem_image_of_mem some ha
      · simp only [br, dite_eq_right hj, Finset.mem_singleton]
    · obtain ⟨b, hb, hbB⟩ := hroot ⟨j.val, hj⟩
      refine ⟨none, ?_, some b, ?_, hbB⟩
      · simp only [br, dite_eq_right hi, Finset.mem_singleton]
      · simpa only [br, dite_eq_left hj] using Finset.mem_image_of_mem some hb
    · exact (hij (Fin.ext (by omega))).elim

/-- Two consecutive pairs of opposite vertices of a six-cycle cannot both
have exterior common neighbours in a minor-free boundary. -/
lemma six_cycle_no_consecutive_opposite_neighbours (hg : 5 ≤ G.egirth)
    {c : ZMod 6 → V} (hc : IsCycleMap G c) (hB : IsK5Boundary G (Set.range c))
    {x y : V} (hx : x ∉ Set.range c) (hy : y ∉ Set.range c)
    (h0x : G.Adj (c 0) x) (hx3 : G.Adj x (c 3))
    (h1y : G.Adj (c 1) y) (hy4 : G.Adj y (c 4)) : False := by
  have h01 := hc.adj 0
  have h12 := hc.adj 1
  have h23 := hc.adj 2
  have h34 := hc.adj 3
  have h45 := hc.adj 4
  have h50 := hc.adj 5
  norm_num at h01 h12 h23 h34 h45 h50
  change G.Adj (c 5) (c 0) at h50
  have hcx : ∀ i, c i ≠ x := fun i h => hx ⟨i, h⟩
  have hcy : ∀ i, c i ≠ y := fun i h => hy ⟨i, h⟩
  have hxy : x ≠ y := fun h => neighbors_nonadjacent hg h01 h0x (h ▸ h1y)
  let X : Fin 4 → Finset V := ![{x, c 5, c 0}, {y, c 1}, {c 2, c 3}, {c 4}]
  apply not_isK5Boundary_of_rooted_four_bags (Set.range c) X ?_ ?_ ?_ ?_ hB
  · intro i
    fin_cases i
    · simpa [X] using
        ((connSet_singleton G (c 0)).insert_adj (Set.mem_singleton _) h50).insert_adj
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)) h0x.symm
    · simpa [X] using (connSet_singleton G (c 1)).insert_adj
          (Set.mem_singleton _) h1y.symm
    · simpa [X] using (connSet_singleton G (c 3)).insert_adj
          (Set.mem_singleton _) h23
    · simpa [X] using connSet_singleton G (c 4)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [X, Finset.disjoint_left, hc.inj.eq_iff, hcx, hcy,
        fun i => (hcx i).symm, fun i => (hcy i).symm, hxy, hxy.symm] at hij ⊢ <;> decide
  · have hforward : ∀ i j : Fin 4, i < j → ∃ a ∈ X i, ∃ b ∈ X j, G.Adj a b := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact ⟨c 0, by simp [X], c 1, by simp [X], h01⟩
      · exact ⟨x, by simp [X], c 3, by simp [X], hx3⟩
      · exact ⟨c 5, by simp [X], c 4, by simp [X], h45.symm⟩
      · exact ⟨c 1, by simp [X], c 2, by simp [X], h12⟩
      · exact ⟨y, by simp [X], c 4, by simp [X], hy4⟩
      · exact ⟨c 3, by simp [X], c 4, by simp [X], h34⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hforward i j h
    · obtain ⟨a, ha, b, hb, hab⟩ := hforward j i h
      exact ⟨b, hb, a, ha, hab.symm⟩
  · intro i
    fin_cases i
    · exact ⟨c 0, by simp [X], ⟨0, rfl⟩⟩
    · exact ⟨c 1, by simp [X], ⟨1, rfl⟩⟩
    · exact ⟨c 2, by simp [X], ⟨2, rfl⟩⟩
    · exact ⟨c 4, by simp [X], ⟨4, rfl⟩⟩

/-- It suffices that deletion preserves connectivity at vertices of the chosen
face: the registered apex construction then gives its minor-free boundary. -/
lemma isK5Boundary_of_face_deletions [Finite V] (M : PlaneMap G) (outer : G.Dart)
    (hconn : ∀ v, OnOuterFace M outer v → (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsK5Boundary G {v | OnOuterFace M outer v} := by
  have hB := isK5Boundary_face M outer (fun d e hfst => ?_)
  · have hverts : FaceApex.faceVerts M outer = {v | OnOuterFace M outer v} := by
      ext x
      exact ⟨fun ⟨e, he⟩ => ⟨e.1, e.2, he⟩,
        fun ⟨e, he, hex⟩ => ⟨⟨e, he⟩, hex⟩⟩
    rwa [hverts] at hB
  · apply Subtype.ext
    apply eq_of_same_face_of_fst M (d.property.symm.trans e.property) hfst
    intro a b ha hb
    have : Nonempty ↥(({d.1.fst} : Set V)ᶜ) := ⟨⟨a, ha⟩⟩
    have hc : (G.induce ({d.1.fst} : Set V)ᶜ).Connected :=
      SimpleGraph.Connected.mk (hconn d.1.fst ⟨d.1, d.2, rfl⟩)
    exact ((connSet_iff_induce_connected _ _).2 hc).2 a ha b hb

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- The complete prescribed facial six-cycle reduction. If an opposite pair has
an exterior common neighbour, the rooted four-bag obstruction permits deleting
the next cycle vertex instead. All changed-list conditions use the already
proved facial deletion reduction. -/
theorem colourable_of_facial_six_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hdeletions : ∀ v ∈ p.support, (G.induce ({v} : Set V)ᶜ).Preconnected
  swap
  · push Not at hdeletions
    obtain ⟨v, hv, hcut⟩ := hdeletions
    exact I.colourable_of_precolored_cutvertex v ((hP v).2 hv) hconn hcut hsmall
  by_cases hnone : ∀ x, x ∉ p.support → ¬ (G.Adj a x ∧ G.Adj x (p.getVert 3))
  · exact I.colourable_of_facial_six_cycle_without_opposite_neighbour hconn p hp hlen hP hface hnone hsmall
  push Not at hnone
  obtain ⟨x, hx, hax, hx3⟩ := hnone
  let c : ZMod 6 → V := fun i => p.getVert i.val
  have hc : IsCycleMap G c := by
    have h := walk_isCycleMap p hp
    change IsCycleMap G (fun i : ZMod p.length => p.getVert i.val) at h
    rw [hlen] at h
    exact h
  have hr : Set.range c = {z | z ∈ p.support} := by
    have h := walkCycleVertices_range p hp
    change Set.range (fun i : ZMod p.length => p.getVert i.val) = {z | z ∈ p.support} at h
    rw [hlen] at h
    exact h
  have h0 : c 0 = a := by simp only [c, ZMod.val_zero, Walk.getVert_zero]
  have h3 : c 3 = p.getVert 3 := rfl
  have hB : IsK5Boundary G (Set.range c) := by
    have h := isK5Boundary_of_face_deletions I.embedding I.outer
      (fun v hv => hdeletions v ((hface v).1 hv))
    have heq : Set.range c = {z | OnOuterFace I.embedding I.outer z} := by
      rw [hr]
      ext z
      exact (hface z).symm
    rwa [← heq] at h
  have h01 := hc.adj 0
  have h12 := hc.adj 1
  have h23 := hc.adj 2
  have h34 := hc.adj 3
  have h45 := hc.adj 4
  have h50 := hc.adj 5
  norm_num at h01 h12 h23 h34 h45 h50
  change G.Adj (c 5) (c 0) at h50
  let q : G.Walk (c 1) (c 1) := .cons h12 (.cons h23 (.cons h34 (.cons h45 (.cons h50 (.cons h01 .nil)))))
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).2
    constructor
    · simp [Walk.isPath_def, Walk.support_cons, hc.inj.eq_iff]
      decide
    · simp [Walk.edges_cons, Walk.edges_nil, hc.inj.eq_iff]
      decide
  have hqsupport : ∀ z, z ∈ q.support ↔ z ∈ Set.range c := by
    intro z
    constructor
    · simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;>
        simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] <;>
        first
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (Or.inl rfl))
        | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  apply I.colourable_of_facial_six_cycle_without_opposite_neighbour hconn q hq rfl
    (fun z => (hP z).trans (by rw [hqsupport z, hr]; rfl))
    (fun z => (hface z).trans (by rw [hqsupport z, hr]; rfl)) ?_ hsmall
  intro y hy hyadj
  apply six_cycle_no_consecutive_opposite_neighbours I.girth hc hB
    (by simpa only [hr, Set.mem_ofPred_eq] using hx)
    (fun h => hy ((hqsupport y).2 h))
    (by simpa only [h0] using hax) (by simpa only [h3] using hx3) hyadj.1
  exact hyadj.2

/-- Every prescribed facial cycle allowed by the six-vertex invariant is now
covered. Girth leaves only the five- and six-cycle cases. -/
theorem colourable_of_facial_short_cycle (I : BoundaryInstance G C) (hconn : G.Preconnected)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hface : ∀ x, OnOuterFace I.embedding I.outer x ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hlower := five_le_egirth_iff.1 I.girth a p hp
  have hupper : p.length ≤ 6 := by rwa [cycle_support_card_eq_length p hp] at hbound
  rcases (by omega : p.length = 5 ∨ p.length = 6) with h | h
  · exact I.colourable_of_facial_five_cycle hconn p hp h hP hface hsmall
  · exact I.colourable_of_facial_six_cycle hconn p hp h hP hface hsmall

end BoundaryInstance

end Thomassen
