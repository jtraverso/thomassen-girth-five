/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedInstance

/-! Exterior incidence certificates for possibly disconnected plane graphs. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- A disconnected plane graph has one unbounded face but generally several
dart orbits along that face. In each component with an edge, the marked boundary
vertices must lie on one actual face orbit of the restricted plane map.
Isolated vertices impose no dart condition. No colouring property is encoded. -/
def ComponentOuterBoundary (M : PlaneMap G) (B : Set V) : Prop :=
  ∀ K : G.ConnectedComponent, Nonempty K.toSimpleGraph.Dart →
    ∃ outer : K.toSimpleGraph.Dart, ∀ x : K,
      x.1 ∈ B → OnOuterFace (inducedPlaneMap M K.supp) outer x

end Thomassen
