/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorBoundaryNeighbours

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Retain a connected part of the old prescription on a proper piece with
its actual exposed face. The original lists are unchanged, and the six-vertex
bound is inherited by every simple path in the retained prescribed set. -/
theorem colourable_induced_retaining_connected_prescription (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected)
    (hPconn : ConnSet G {x | x ∈ I.precolor.vertices ∧ x ∈ S})
    (hOldFace : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → OnOuterFace M o x)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable (G.induce S) (fun x => I.lists x.1) := by
  let P : Set V := {x | x ∈ I.precolor.vertices ∧ x ∈ S}
  let J : ConnectedPrescription (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := M
    outer := o
    vertices := {x : S | x.1 ∈ I.precolor.vertices}
    connected := by
      have hc := connSet_induce_of_subset P S hPconn (fun _ h => h.2)
      simpa only [P,Set.mem_ofPred_eq,and_iff_left_of_imp (fun _ => Subtype.coe_prop _)] using hc
    paths_short := by
      intro a b p hp hs
      have hsub : (p.map (Embedding.induce S).toHom).support.toFinset ⊆ I.precolor.vertices := by
        intro z hz
        rw [Walk.support_map] at hz
        obtain ⟨x,hx,he⟩ := List.mem_map.1 (List.mem_toFinset.1 hz)
        change x.1 = z at he
        exact he ▸ hs x hx
      have hPcard := I.precolor.card_vertices_le
      have hc := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup (hp.map Subtype.val_injective).support_nodup,
        Walk.length_support,Walk.length_map] at hc
      omega
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := fun x hx => hOldFace x (I.on_outer x.1 hx)
    singleton := fun x hx => I.singleton x.1 hx
    proper := fun {x y} hx hy hxy => I.proper_on_precolored_vertices hx hy hxy
    boundary_lists := fun x _ hx => I.outside_precolor_list_ge_two hx
    interior_lists := fun x hx => I.interior_lists x.1 (fun h => hx (hOldFace x h))
    short_edges := fun {x y} hxy hx hy => I.precolor.endpoints_of_mem_edges
      (I.short_edges (x := x.1) (y := y.1) hxy hx hy) }
  exact connectedPrescription_extension_of_smaller (Nat.card V) hsmall J hconn hSsmall

end Thomassen.BoundaryInstance
