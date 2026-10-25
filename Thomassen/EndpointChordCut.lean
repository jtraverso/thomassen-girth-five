/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.UnprescribedBoundaryChord

/-! Chords meeting an endpoint of the original prescribed path. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

lemma path_side_dichotomy_avoiding_other_separator {a b t : V} {S : Set V} (haS : a ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    (p : G.Walk a t) (hp : p.IsPath) (hb : b ∉ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a) := by
  cases p with
  | nil => exact Or.inl (by simpa using haS)
  | @cons _ s _ has p =>
    have hpa : a ∉ p.support := (List.nodup_cons.1 hp.support_nodup).1
    have hpb : b ∉ p.support := fun h => hb (List.mem_cons_of_mem _ h)
    have hside := walk_side_of_avoids_two_cut hsep p hpa hpb
    by_cases hs : s ∈ S
    · refine Or.inl ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact haS
      · exact (hside x hx).2 hs
    · refine Or.inr ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact iff_of_true haS rfl
      · have hxout : x ∉ S := fun h => hs ((hside x hx).1 h)
        have hxa : x ≠ a := fun h => hpa (h ▸ hx)
        exact iff_of_false hxout hxa

namespace BoundaryInstance
variable [Fintype V]

/-- An edge cut at an endpoint of the prescribed path retains the entire
prescription in one side, even when the other separator end is unprescribed. -/
theorem colourable_of_path_endpoint_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b t : V} (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hbP : b ∉ I.precolor.vertices) (p : G.Walk a t) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have haST : a ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hpb : b ∉ p.support := fun h => hbP ((hP b).2 h)
  rcases path_side_dichotomy_avoiding_other_separator haST.1
    (edge_cut_side_constancy S T a b hinter hedges) p hp hpb with hPS | hPS
  · apply I.colourable_of_edge_cut_with_one_sided_prescription T S a b hab ha hb
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm) hTc hSc
      ?_ hTsmall hSsmall hsmall
    intro x hxT hxP
    have hx : x ∈ S ∩ T := ⟨hPS x ((hP x).1 hxP), hxT⟩
    rw [hinter] at hx
    exact hx.elim Or.inl (fun h => Or.inr (Set.mem_singleton_iff.1 h))
  · apply I.colourable_of_edge_cut_with_one_sided_prescription S T a b hab ha hb hcover hinter hedges hSc hTc
      ?_ hSsmall hTsmall hsmall
    intro x hxS hxP
    exact Or.inl ((hPS x ((hP x).1 hxP)).1 hxS)

/-- A chord incident with the initial prescribed-path vertex is completely
reduced on the actual facial boundary. Reversing the path covers its other end. -/
theorem colourable_of_path_endpoint_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hjP : c j ∉ I.precolor.vertices) {t : V} (p : G.Walk (c i) t) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
  exact I.colourable_of_path_endpoint_edge_cut S T hadj hi hj hjP p hp hP hcover hinter hedges hSc hTc hSsmall hTsmall hsmall

end BoundaryInstance
end Thomassen
