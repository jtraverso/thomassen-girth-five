/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Challenge
public import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Independent unconditional main target

The original mathematical statement is kept unchanged. Its proof is supplied
by ThomassenSolution; this challenge deliberately retains only the contract.
-/

@[expose] public section
namespace PlanarChoosability

/-- Thomassen (1995): every finite planar graph of girth at least five is
3-choosable, for lists over an arbitrary colour type. Extended girth includes
forests and edgeless graphs. -/
theorem choosableWith_three_of_isPlanar {V : Type*} [Finite V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (hgirth : 5 ≤ G.egirth)
    (C : Type*) : ChoosableWith G C 3 := by
  sorry

end PlanarChoosability
