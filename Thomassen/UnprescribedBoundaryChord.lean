/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.UnprescribedEdgeCut

/-! Actual boundary chords with unprescribed ends. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma walk_side_of_avoids_two_cut {a b : V} {S : Set V}
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {s t : V} (p : G.Walk s t) (ha : a ∉ p.support) (hb : b ∉ p.support) :
    ∀ x ∈ p.support, x ∈ S ↔ s ∈ S := by
  induction p with
  | nil => simpa only [Walk.support_nil, List.mem_singleton] using fun x hx => hx ▸ Iff.rfl
  | @cons s t u hst p ih =>
    have hsa : s ≠ a := fun h => ha (by simp [h])
    have hsb : s ≠ b := fun h => hb (by simp [h])
    have hta : t ≠ a := fun h => ha (List.mem_cons_of_mem _ (h ▸ p.start_mem_support))
    have htb : t ≠ b := fun h => hb (List.mem_cons_of_mem _ (h ▸ p.start_mem_support))
    have hpa : a ∉ p.support := fun h => ha (List.mem_cons_of_mem _ h)
    have hpb : b ∉ p.support := fun h => hb (List.mem_cons_of_mem _ h)
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Iff.rfl
    · exact (ih hpa hpb x hx).trans (hsep hst hsa hsb hta htb).symm

lemma BoundaryPrecolor.edge_cut_dichotomy_avoiding (P : BoundaryPrecolor G) (a b : V)
    (ha : a ∉ P.vertices) (hb : b ∉ P.vertices) (S : Set V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    (∀ x ∈ P.vertices, x ∈ S) ∨ (∀ x ∈ P.vertices, x ∉ S) := by
  have hwalk : ∀ {s t : V} (p : G.Walk s t), a ∉ p.support → b ∉ p.support →
      (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∉ S) := by
    intro s t p hpa hpb
    have hsides := walk_side_of_avoids_two_cut hsep p hpa hpb
    by_cases hs : s ∈ S
    · exact Or.inl (fun x hx => (hsides x hx).2 hs)
    · exact Or.inr (fun x hx h => hs ((hsides x hx).1 h))
  cases P with
  | empty => exact Or.inl (by simp)
  | path p _ _ =>
    simpa only [BoundaryPrecolor.vertices, List.mem_toFinset] using
      hwalk p (fun h => ha (List.mem_toFinset.2 h)) (fun h => hb (List.mem_toFinset.2 h))
  | cycle p _ _ =>
    simpa only [BoundaryPrecolor.vertices, List.mem_toFinset] using
      hwalk p (fun h => ha (List.mem_toFinset.2 h)) (fun h => hb (List.mem_toFinset.2 h))

namespace BoundaryInstance
variable [Fintype V]

/-- With both separator ends unprescribed, the old native prescription lies
in one side. The complete two-endpoint fan theorem closes the other side. -/
theorem colourable_of_unprescribed_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∉ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  rcases I.precolor.edge_cut_dichotomy_avoiding a b haP hbP S (edge_cut_side_constancy S T a b hinter hedges) with hPS | hPS
  · apply I.colourable_of_edge_cut_with_one_sided_prescription T S a b hab ha hb
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm) hTc hSc
      ?_ hTsmall hSsmall hsmall
    intro x hxT hxP
    have hx : x ∈ S ∩ T := ⟨hPS x hxP, hxT⟩
    rw [hinter] at hx
    exact hx.elim Or.inl (fun h => Or.inr (Set.mem_singleton_iff.1 h))
  · apply I.colourable_of_edge_cut_with_one_sided_prescription S T a b hab ha hb hcover hinter hedges hSc hTc
      ?_ hSsmall hTsmall hsmall
    intro x hxS hxP
    exact (hPS x hxP hxS).elim

/-- Close every actual facial-boundary chord with two unprescribed ends,
without a minimality or short-neighbour capture assumption on its cut. -/
theorem colourable_of_unprescribed_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∉ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
  exact I.colourable_of_unprescribed_edge_cut S T (c i) (c j) hadj hi hj hiP hjP
    hcover hinter hedges hSc hTc hSsmall hTsmall hsmall

/-- A remaining boundary chord of a smallest counterexample has exactly one
prescribed end. Chords with zero or two prescribed ends are now both closed. -/
lemma boundary_chord_exactly_one_prescribed_end (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j)) :
    (c i ∈ I.precolor.vertices ∧ c j ∉ I.precolor.vertices) ∨
      (c i ∉ I.precolor.vertices ∧ c j ∈ I.precolor.vertices) := by
  by_cases hiP : c i ∈ I.precolor.vertices <;> by_cases hjP : c j ∈ I.precolor.vertices
  · exact (hbad (I.colourable_of_prescribed_boundary_chord hc hk hface hG i j hadj hforward hbackward hiP hjP hsmall)).elim
  · exact Or.inl ⟨hiP, hjP⟩
  · exact Or.inr ⟨hiP, hjP⟩
  · exact (hbad (I.colourable_of_unprescribed_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj hiP hjP hsmall)).elim

end BoundaryInstance
end Thomassen
