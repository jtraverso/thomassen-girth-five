/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexPathClosure
public import Thomassen.Assembly

/-! Close the boundary-extension induction for arbitrary finite vertex types. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical

/-- Strong induction discharges all boundary instances: every possible
remaining counterexample would have the now completed six-vertex prescription. -/
theorem boundary_instances_colourable_at_card (C : Type v) (n : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (I : BoundaryInstance G C),
      Nat.card V=n → ListColourable G I.lists := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V instFinite G I hcard
    let : Fintype V := Fintype.ofFinite V
    have hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
        Nat.card W < Nat.card V → ListColourable H J.lists := by
      intro W instFiniteW H J hW
      exact ih (Nat.card W) (by omega) W H J rfl
    by_contra hbad
    obtain ⟨a,t,r,hr,hn,hP,hrlen⟩ := I.remaining_counterexample_has_six_prescribed_vertices hbad hsmall
    exact hbad (I.colourable_of_six_vertex_prescribed_path r hr hn hP hrlen hsmall)

/-- The full boundary-extension theorem. This is proved, rather than assumed
as a parameter of the unconditional planar list-colouring result. -/
theorem boundary_extension (C : Type v) : BoundaryExtension.{u,v} C := by
  intro V instFinite G I
  exact boundary_instances_colourable_at_card C (Nat.card V) V G I rfl

end Thomassen

namespace PlanarChoosability

/-- Thomassen (1995): every finite planar graph of extended girth at least
five is three-choosable over any colour type. -/
theorem choosableWith_three_of_isPlanar {V : Type*} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : ChoosableWith G C 3 :=
  choosableWith_three_of_boundary_extension (Thomassen.boundary_extension C) G hplanar hgirth

end PlanarChoosability
