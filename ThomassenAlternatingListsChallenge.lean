/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortFaceCompletion

/-! Independent contracts for the alternating boundary-list case.
The new proof module is not imported. The unconditional main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Exact native rebasing preserves the entire support, including the root. -/
lemma native_rebase_support_eq {a b : V} (p : G.Walk a a) (hp : p.IsCycle) (q : G.Walk b b)
    (s : ℕ) (hlen : q.length = p.length)
    (horder : ∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s+i : ℕ) : ZMod p.length)) :
    ∀ x, x ∈ q.support ↔ x ∈ p.support := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [Fintype V] {a : V}

/-- With the first facial edge prescribed, a short fourth backward list is
resolved by precolouring a five-vertex native boundary path. The only enlarged
list gets the adjacent prescribed colour as its extra colour, so every resulting
colouring restores that original list. Only the strict main induction is used. -/
theorem colourable_of_prescribed_edge_short_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : 7 ≤ p.length) (hfourth : (I.lists (p.getVert (p.length-4))).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- The whole short-second-list branch for a prescribed edge is closed.
The good-fourth case uses the checked deletion; the alternating case uses
compatible five-vertex precolouring and restores its one enlarged list. -/
theorem colourable_of_prescribed_edge_short_second (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x = a ∨ x = p.getVert 1)
    (hlen : 6 ≤ p.length) (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every actual native facial case with an edge prescribed is closed under
the strict main induction. This combines the five-vertex face, good-second-list
branch and the complete short-second-list branch. -/
theorem colourable_of_prescribed_edge_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
