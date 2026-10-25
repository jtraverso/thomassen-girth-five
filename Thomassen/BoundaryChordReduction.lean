/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CentralChordCut

/-! Complete boundary-chord reduction for the main extension induction. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- Every facial-boundary chord is closed for an arbitrary six-vertex native
prescribed path, including all three formerly open central branch splits. -/
theorem colourable_of_path_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hiP : c i ∈ I.precolor.vertices <;> by_cases hjP : c j ∈ I.precolor.vertices
  · exact I.colourable_of_prescribed_boundary_chord hc hk hface hG i j hadj hforward hbackward hiP hjP hsmall
  · obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
      full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
    exact I.colourable_of_mixed_prescription_edge_cut S T (c i) (c j) hadj hi hj hiP hjP p hp hn hP
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  · obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
      full_face_chord_separation_at I.embedding hc hk hface hG j i hadj.symm hbackward hforward
    exact I.colourable_of_mixed_prescription_edge_cut S T (c j) (c i) hadj.symm hj hi hjP hiP p hp hn hP
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  · exact I.colourable_of_unprescribed_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj hiP hjP hsmall


/-- Every chord of the actual facial boundary is a complete strict-induction
case, for every permitted original prescription. No placement or short-neighbour
capture hypothesis is supplied. -/
theorem colourable_of_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  cases hP : I.precolor with
  | empty =>
    exact I.colourable_of_unprescribed_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj
      (by simp [hP]) (by simp [hP]) hsmall
  | path p hp hn =>
    exact I.colourable_of_path_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj p hp hn hP hsmall
  | cycle p hp hn =>
    exact I.colourable_of_prescribed_cycle p hp hn (by simp [hP, BoundaryPrecolor.vertices]) hsmall

/-- In a smallest counterexample every edge between facial-boundary vertices
is an edge of that actual boundary cycle. -/
lemma boundary_adj_consecutive_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hi : OnOuterFace I.embedding I.outer (c i))
    (hj : OnOuterFace I.embedding I.outer (c j)) (hadj : G.Adj (c i) (c j)) :
    j = i + 1 ∨ i = j + 1 := by
  by_contra h
  push Not at h
  exact hbad (I.colourable_of_boundary_chord hG hc hk hface i j hadj h.1 h.2 hi hj hsmall)

/-- The normalized native facial boundary of a smallest counterexample is
chordless in the whole graph, with the original boundary vertices and corners. -/
theorem minimal_counterexample_has_chordless_native_face_cycle (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.IsChordless ∧
        p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  obtain ⟨hG, hcard, hdel, a, p, hp, hlen, hverts, hface, hroot⟩ :=
    I.minimal_counterexample_has_native_face_cycle hbad hsmall
  have hplen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hch : p.IsChordless := by
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro x y hx hy hxy
    obtain ⟨i, hi⟩ := (walkCycleVertices_range p hp).symm ▸ (show x ∈ {z | z ∈ p.support} from hx)
    obtain ⟨j, hj⟩ := (walkCycleVertices_range p hp).symm ▸ (show y ∈ {z | z ∈ p.support} from hy)
    have hcon := I.boundary_adj_consecutive_of_minimal_counterexample hG (walk_isCycleMap p hp) hplen hface hbad hsmall i j
      (by rw [hi]; exact (hverts x).1 hx) (by rw [hj]; exact (hverts y).1 hy) (by rw [hi, hj]; exact hxy)
    apply (walkCycleVertices_edges p hp x y).1
    rw [← hi, ← hj]
    apply (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) i _).2
    exact hcon.elim (fun h => Or.inl (congrArg (walkCycleVertices p) h))
      (fun h => Or.inr (congrArg (walkCycleVertices p) (by linear_combination -h)))
  exact ⟨hG, hcard, hdel, a, p, hp, hch, hlen, hverts, hface, hroot⟩

end BoundaryInstance
end Thomassen
