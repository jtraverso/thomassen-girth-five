/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.Instance
public import Solution

/-!
# Definition-preserving assembly of the main theorem

This module defines `BoundaryExtension` and the conditional bridge from it to
finite three-choosability. The complete extension property is proved in
`Thomassen/BoundaryExtension.lean`, which applies this bridge to obtain the
unconditional target checked by comparator.json. Arbitrary colour types and
edgeless graphs are covered without an extra nonemptiness assumption.
-/

@[expose] public section
open LeanPool.K5MinorFreeChoosability
universe u v
namespace Thomassen

/-- The boundary-extension property proved in `Thomassen/BoundaryExtension.lean`. -/
def BoundaryExtension (C : Type v) : Prop :=
  ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (I : BoundaryInstance G C),
    ListColourable G I.lists

/-- Once the boundary-extension theorem is proved, the finite three-choosability
target follows. The extension property is an explicit hypothesis here. -/
theorem choosable_of_boundary_extension {C : Type v} (hext : BoundaryExtension.{u, v} C)
    {V : Type u} [Finite V] (G : SimpleGraph V) (hplanar : IsPlanar G)
    (hgirth : 5 ≤ G.egirth) : ChoosableWith G C 3 := by
  classical
  intro L hL
  have hn : ∀ x, (L x).Nonempty := fun x => Finset.card_pos.1 (by have := hL x; omega)
  let c : V → C := fun x => (hn x).choose
  by_cases hedge : ∃ a b, G.Adj a b
  · obtain ⟨a, b, hab⟩ := hedge
    obtain ⟨M⟩ := hplanar
    exact hext V G (BoundaryInstance.of_three_lists M ⟨(a, b), hab⟩ hgirth L hL c)
  · exact ⟨SimpleGraph.Coloring.mk c (fun {a b} hab => False.elim (hedge ⟨a, b, hab⟩)),
      fun x => (hn x).choose_spec⟩

end Thomassen

namespace PlanarChoosability

/-- Conditional bridge to the exact original namespace and definitions.
The unconditional result applies it to the proved boundary-extension theorem. -/
theorem choosableWith_three_of_boundary_extension {C : Type v}
    (hext : Thomassen.BoundaryExtension.{u, v} C) {V : Type u} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth) :
    ChoosableWith G C 3 :=
  choosableWith_of_lib
    (Thomassen.choosable_of_boundary_extension hext G ((isPlanar_iff_lib G).1 hplanar) hgirth)

end PlanarChoosability
