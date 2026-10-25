/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryExtension
public import Mathlib.Combinatorics.Compactness

/-! Infinite list colouring by the already formalized Rado selection principle.
The finite girth-five theorem is due to Thomassen (1995); the compactness
mechanism follows Rado (1949), as implemented in Mathlib, and the classical
de Bruijn–Erdős (1951) finite-subgraph principle. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- Finite-list colourability is compact: choose a compatible global colouring
from arbitrary allowed colourings of every finite induced subgraph. Neither
the vertex type nor the union of all lists is required to be finite. -/
theorem listColourable_of_finite_induced
    (L : V → Finset C)
    (hfinite : ∀ S : Finset V, ListColourable (G.induce (↑S : Set V)) (fun x => L x.1)) :
    ListColourable G L := by
  let β : V → Type v := fun x => {c : C // c ∈ L x}
  let g (S : Finset V) (x : S) : β x.1 :=
    ⟨(hfinite S).choose x,(hfinite S).choose_spec x⟩
  obtain ⟨χ,hχ⟩ := Finset.rado_selection_subtype g
  let f : V → C := fun x => (χ x).1
  refine ⟨Coloring.mk f ?_,fun x => (χ x).2⟩
  intro x y hxy he
  obtain ⟨T,hST,hT⟩ := hχ {x,y}
  have hx : x ∈ ({x,y} : Finset V) := by simp
  have hy : y ∈ ({x,y} : Finset V) := by simp
  have hxT : x ∈ T := hST hx
  have hyT : y ∈ T := hST hy
  have hxcol : f x = (hfinite T).choose ⟨x,hxT⟩ :=
    congrArg Subtype.val (hT ⟨x,hx⟩)
  have hycol : f y = (hfinite T).choose ⟨y,hyT⟩ :=
    congrArg Subtype.val (hT ⟨y,hy⟩)
  exact (hfinite T).choose.valid
    (show (G.induce (↑T : Set V)).Adj ⟨x,hxT⟩ ⟨y,hyT⟩ from hxy)
    (hxcol.symm.trans (he.trans hycol))

/-- Infinite girth-five extension of Thomassen's finite theorem: if every
finite induced subgraph has a plane map and girth at least five, every finite
list assignment of size at least three admits a global proper colouring.
This states finite-subgraph planarity explicitly, rather than introducing an
unverified notion of an infinite plane map. -/
theorem infinite_three_list_colourable
    (hplanar : ∀ S : Finset V, IsPlanar (G.induce (↑S : Set V)))
    (hgirth : ∀ S : Finset V, 5 ≤ (G.induce (↑S : Set V)).egirth)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card) : ListColourable G L := by
  apply listColourable_of_finite_induced L
  intro S
  exact choosable_of_boundary_extension (boundary_extension C) (G.induce (↑S : Set V))
    (hplanar S) (hgirth S) (fun x => L x.1) (fun x => hL x.1)

/-- The same infinite extension using Mathlib's global extended girth. -/
theorem infinite_three_list_colourable_of_egirth
    (hplanar : ∀ S : Finset V, IsPlanar (G.induce (↑S : Set V)))
    (hgirth : 5 ≤ G.egirth)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card) : ListColourable G L := by
  exact infinite_three_list_colourable hplanar
    (fun S => five_le_egirth_induce (↑S : Set V) hgirth) L hL

end Thomassen
