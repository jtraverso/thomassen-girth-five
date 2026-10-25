/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedPrescriptionGlobal

/-! Public source-aligned interfaces for short connected boundary prescriptions.
Theorem 1 of Dvořák–Kawarabayashi, arXiv:1109.2976, attributes the short-path
extension to Thomassen. Proper chords between prescribed vertices are allowed. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- Any connected outer prescription on at most six vertices has the bounded
simple-path property required by the already proved auxiliary extension. -/
theorem colourable_connected_boundary_set_six
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (B : Finset V) (hB : B.card ≤ 6) (hconn : ConnSet G (↑B : Set V))
    (L : V → Finset C) (f : V → C)
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hsingle : ∀ x ∈ B, L x = {f x})
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x, OnOuterFace M outer x → x ∉ B → 2 ≤ (L x).card)
    (hinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (hshort : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∧ y ∈ B) :
    ListColourable G L := by
  let I : ConnectedPrescription G C := {
    girth := hg
    embedding := M
    outer := outer
    vertices := (↑B : Set V)
    connected := hconn
    paths_short := by
      intro a b p hp hs
      have hsub : p.support.toFinset ⊆ B := fun x hx => hs x (List.mem_toFinset.1 hx)
      have hcard := (Finset.card_le_card hsub).trans hB
      rw [List.toFinset_card_of_nodup hp.support_nodup,p.length_support] at hcard
      omega
    lists := L
    prescribed := f
    on_outer := hface
    singleton := hsingle
    proper := fun {x y} hx hy hxy => hproper x hx y hy hxy
    boundary_lists := hboundary
    interior_lists := hinterior
    short_edges := hshort }
  exact I.colourable

/-- Dvořák–Kawarabayashi (2011), Theorem 1 (attributed there to Thomassen).
A prescribed proper colouring of a boundary path of at most five edges extends.
Proper chords of the prescribed path are allowed. Interior lists of size at
least three generalize the source's exactly-three convention. -/
theorem dvorak_kawarabayashi_theorem_1
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ 5)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (f : V → C)
    (hsingle : ∀ x ∈ p.support, L x = {f x})
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x, OnOuterFace M outer x → x ∉ p.support → 2 ≤ (L x).card)
    (hinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (hshort : ∀ x, (L x).card = 2 → ∀ y, (L y).card ≤ 2 → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  have houtside : ∀ x, x ∉ p.support → 2 ≤ (L x).card := by
    intro x hx
    by_cases hxf : OnOuterFace M outer x
    · exact hboundary x hxf hx
    · exact (by omega : 2 ≤ 3).trans (hinterior x hxf)
  obtain ⟨c,hc⟩ := colourable_connected_boundary_set_six M outer hg p.support.toFinset
    (by rw [List.toFinset_card_of_nodup hp.support_nodup,p.length_support]; omega)
    (by simpa only [List.coe_toFinset] using walk_support_connSet p) L f
    (fun x hx => hface x (List.mem_toFinset.1 hx))
    (fun x hx => hsingle x (List.mem_toFinset.1 hx))
    (fun x hx y hy => hproper x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy))
    (fun x hx hn => hboundary x hx (fun h => hn (List.mem_toFinset.2 h))) hinterior (by
      intro x y hxy hx hy
      have hxP : x ∈ p.support := by
        by_contra hn
        have h2 := houtside x hn
        exact hshort x (by omega) y hy hxy
      have hyP : y ∈ p.support := by
        by_contra hn
        have h2 := houtside y hn
        exact hshort y (by omega) x hx hxy.symm
      exact ⟨List.mem_toFinset.2 hxP,List.mem_toFinset.2 hyP⟩)
  exact ⟨c,hc,fun x hx => Finset.mem_singleton.1 (by simpa only [hsingle x hx] using hc x)⟩

end Thomassen
