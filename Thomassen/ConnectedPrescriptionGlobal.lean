/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryExtension

/-! Unconditional extension of bounded connected prescriptions, including disconnected graphs. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.ConnectedPrescription
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- Discharge the auxiliary induction from the proved boundary extension.
Only the component containing the actual outer dart carries short lists. -/
theorem colourable (I : ConnectedPrescription G C) : ListColourable G I.lists := by
  let : Fintype V := Fintype.ofFinite V
  let S : Set V := {x | G.Reachable I.outer.fst x}
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S :=
    fun _ hx _ hxy => hx.trans hxy.reachable
  have hroot : I.outer.fst ∈ S := Reachable.refl _
  have hPsub : I.vertices ⊆ S := fun x hx =>
    reachable_of_onOuterFace I.embedding I.outer (I.on_outer x hx)
  have hconn : (G.induce S).Preconnected := by
    intro x y
    obtain ⟨p⟩ := x.2.symm.trans y.2
    exact ⟨p.induce S (fun z hz => x.2.trans (p.takeUntil z hz).reachable)⟩
  let : Nontrivial S := (show (G.induce S).Adj
    ⟨I.outer.fst,hroot⟩ ⟨I.outer.snd,hclosed _ hroot _ I.outer.adj⟩ from I.outer.adj).nontrivial
  have hPconn : ConnSet G (I.vertices ∩ S) := by
    have heq : I.vertices ∩ S = I.vertices := Set.inter_eq_left.2 hPsub
    rw [heq]
    exact I.connected
  let J := I.induce S hconn hPconn
  obtain ⟨cS,hcS⟩ := connectedPrescription_extension_of_smaller (Nat.card S+1)
    (fun W _ H K _ => boundary_extension C W H K) J hconn (by omega)
  have hT : ListColourable (G.induce Sᶜ) (fun x => I.lists x.1) := by
    apply choosable_of_boundary_extension (boundary_extension C) (G.induce Sᶜ)
      ⟨inducedPlaneMap I.embedding Sᶜ⟩ (five_le_egirth_induce Sᶜ I.girth)
    intro x
    exact I.interior_lists x.1
      (fun h => x.2 (reachable_of_onOuterFace I.embedding I.outer h))
  obtain ⟨cT,hcT⟩ := hT
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x,hx⟩ else cT ⟨x,hx⟩
  refine ⟨Coloring.mk f ?_,?_⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · have hy := hclosed x hx y hxy
      simpa only [f,dite_eq_left hx,dite_eq_left hy] using
        (show cS ⟨x,hx⟩ ≠ cS ⟨y,hy⟩ from cS.valid hxy)
    · have hy : y ∉ S := fun hy => hx (hclosed y hy x hxy.symm)
      simpa only [f,dite_eq_right hx,dite_eq_right hy] using
        (show cT ⟨x,hx⟩ ≠ cT ⟨y,hy⟩ from cT.valid hxy)
  · intro x
    change f x ∈ I.lists x
    by_cases hx : x ∈ S
    · simpa only [f,dite_eq_left hx,J,induce] using hcS ⟨x,hx⟩
    · simpa only [f,dite_eq_right hx] using hcT ⟨x,hx⟩

end Thomassen.ConnectedPrescription
