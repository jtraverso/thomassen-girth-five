/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedEdgeClosure

/-! Connected boundary prescriptions with bounded simple paths.

Branching prescriptions arise after colouring neighbours of a deleted boundary
arc. This auxiliary state records their actual vertices and induced edges.
It contains no colouring-extension hypothesis.
-/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A prescribed graph with at most four vertices capable of having two
prescribed neighbours has no simple path of more than five edges. Pendant
vertices need not be bounded in number. -/
lemma path_length_le_five_of_small_core (P : Set V) (B : Finset V) (hB : B.card ≤ 4)
    (hpendant : ∀ x ∈ P, x ∉ B → ∀ r ∈ P, ∀ s ∈ P,
      G.Adj x r → G.Adj x s → r = s)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hsub : ∀ x ∈ p.support, x ∈ P) : p.length ≤ 5 := by
  by_cases hlen : p.length ≤ 1
  · omega
  · have hcore : ∀ i : Fin (p.length-1), p.getVert (i.val+1) ∈ B := by
      intro i
      by_contra hi
      have hil := i.isLt
      have heq := hpendant _ (hsub _ (p.getVert_mem_support _)) hi
        _ (hsub _ (p.getVert_mem_support i.val))
        _ (hsub _ (p.getVert_mem_support (i.val+2)))
        (p.adj_getVert_succ (by omega)).symm
        (by simpa only [Nat.add_assoc] using p.adj_getVert_succ (by omega : i.val+1 < p.length))
      have he := hp.getVert_injOn (by change i.val ≤ p.length; omega)
        (by change i.val+2 ≤ p.length; omega) heq
      omega
    let f : Fin (p.length-1) → B := fun i => ⟨p.getVert (i.val+1),hcore i⟩
    have hf : Function.Injective f := by
      intro i j hij
      have hi := i.isLt
      have hj := j.isLt
      have he := hp.getVert_injOn (by change i.val+1 ≤ p.length; omega)
        (by change j.val+1 ≤ p.length; omega) (congrArg Subtype.val hij)
      apply Fin.ext
      omega
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega

/-- Lift a connected set into an induced graph retaining all its vertices. -/
lemma connSet_induce_of_subset (P S : Set V) (hP : ConnSet G P) (hPS : P ⊆ S) :
    ConnSet (G.induce S) {x : S | x.1 ∈ P} := by
  obtain ⟨a,ha⟩ := hP.1
  let f : V → S := fun x => if hx : x ∈ S then ⟨x,hx⟩ else ⟨a,hPS ha⟩
  refine ⟨⟨⟨a,hPS ha⟩,ha⟩, ?_⟩
  intro x hx y hy
  have hm : RIn (G.induce S) {x : S | x.1 ∈ P} (f x.1) (f y.1) :=
    (hP.2 x.1 hx y.1 hy).map f (by
      intro z w hzw hz hw
      simpa only [f,dite_eq_left (hPS hz),dite_eq_left (hPS hw)] using
        RIn.single (G := G.induce S) (s := {x : S | x.1 ∈ P})
          (a := ⟨z,hPS hz⟩) (b := ⟨w,hPS hw⟩) hzw hz hw)
  simpa only [f,dite_eq_left x.2,dite_eq_left y.2] using hm

/-- Restriction to a side of a clique separator preserves connectedness of
a prescribed set containing the separator. The retraction collapses the other
side onto one separator vertex. -/
lemma connSet_inter_of_clique_separator (P S T : Set V) (hP : ConnSet G P)
    (_hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hclique : ∀ x ∈ S ∩ T, ∀ y ∈ S ∩ T, x ≠ y → G.Adj x y)
    (hsepP : S ∩ T ⊆ P) {a : V} (ha : a ∈ S ∩ T) :
    ConnSet G (P ∩ S) := by
  let f : V → V := fun x => if x ∈ S then x else a
  have hcross : ∀ {x y}, G.Adj x y → x ∈ S → y ∉ S → x ∈ S ∩ T := by
    intro x y hxy hx hy
    rcases hedges hxy with h | h
    · exact (hy h.2).elim
    · exact ⟨hx, h.1⟩
  have hmap : ∀ x y, G.Adj x y → x ∈ P → y ∈ P →
      RIn G (P ∩ S) (f x) (f y) := by
    intro x y hxy hx hy
    by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S
    · simpa only [f, ite_eq_left hxS, ite_eq_left hyS] using
        RIn.single (s := P ∩ S) hxy ⟨hx, hxS⟩ ⟨hy, hyS⟩
    · simp only [f, ite_eq_left hxS, ite_eq_right hyS]
      by_cases hxa : x = a
      · subst x; exact .refl _
      · exact .single (hclique x (hcross hxy hxS hyS) a ha hxa)
          ⟨hx, hxS⟩ ⟨hsepP ha, ha.1⟩
    · simp only [f, ite_eq_right hxS, ite_eq_left hyS]
      by_cases hya : y = a
      · subst y; exact .refl _
      · exact .single (hclique a ha y (hcross hxy.symm hyS hxS) (Ne.symm hya))
          ⟨hsepP ha, ha.1⟩ ⟨hy, hyS⟩
    · simp only [f, ite_eq_right hxS, ite_eq_right hyS]
      exact .refl _
  refine ⟨⟨a, hsepP ha, ha.1⟩, ?_⟩
  intro x hx y hy
  simpa only [f, ite_eq_left hx.2, ite_eq_left hy.2] using
    (hP.2 x hx.1 y hy.1).map f hmap

/-- Every path in the prescribed induced graph has at most five edges.
This bound is inherited by cuts, including prescriptions with arbitrarily many
short pendant branches. -/
structure ConnectedPrescription (G : SimpleGraph V) (C : Type v) where
  girth : 5 ≤ G.egirth
  embedding : PlaneMap G
  outer : G.Dart
  vertices : Set V
  connected : ConnSet G vertices
  paths_short : ∀ {a b : V} (p : G.Walk a b), p.IsPath →
    (∀ x ∈ p.support, x ∈ vertices) → p.length ≤ 5
  lists : V → Finset C
  prescribed : V → C
  on_outer : ∀ x ∈ vertices, OnOuterFace embedding outer x
  singleton : ∀ x ∈ vertices, lists x = {prescribed x}
  proper : ∀ {x y}, x ∈ vertices → y ∈ vertices → G.Adj x y → prescribed x ≠ prescribed y
  boundary_lists : ∀ x, OnOuterFace embedding outer x → x ∉ vertices → 2 ≤ (lists x).card
  interior_lists : ∀ x, ¬ OnOuterFace embedding outer x → 3 ≤ (lists x).card
  short_edges : ∀ {x y}, G.Adj x y → (lists x).card ≤ 2 → (lists y).card ≤ 2 →
    x ∈ vertices ∧ y ∈ vertices

namespace ConnectedPrescription

lemma outside_list_ge_two (I : ConnectedPrescription G C) {x : V} (hx : x ∉ I.vertices) :
    2 ≤ (I.lists x).card := by
  by_cases hb : OnOuterFace I.embedding I.outer x
  · exact I.boundary_lists x hb hx
  · have := I.interior_lists x hb; omega

/-- Produce the ordinary main-induction instance once a native prescription
with exactly the required vertices and all its induced edges has been found. -/
def toBoundaryInstance (I : ConnectedPrescription G C) (P : BoundaryPrecolor G)
    (hv : ∀ x, x ∈ P.vertices ↔ x ∈ I.vertices)
    (he : ∀ {x y}, x ∈ I.vertices → y ∈ I.vertices → G.Adj x y → s(x,y) ∈ P.edges) :
    BoundaryInstance G C where
  girth := I.girth
  embedding := I.embedding
  outer := I.outer
  precolor := P
  lists := I.lists
  prescribed := I.prescribed
  on_outer := fun x hx => I.on_outer x ((hv x).1 hx)
  singleton := fun x hx => I.singleton x ((hv x).1 hx)
  proper_precolor := fun {x y} hxy => I.proper
    ((hv x).1 (P.endpoints_of_mem_edges hxy).1)
    ((hv y).1 (P.endpoints_of_mem_edges hxy).2) (P.adj_of_mem_edges hxy)
  boundary_lists := fun x hb hx => I.boundary_lists x hb (fun h => hx ((hv x).2 h))
  interior_lists := I.interior_lists
  short_edges := fun {_ _} hxy hx hy =>
    he (I.short_edges hxy hx hy).1 (I.short_edges hxy hx hy).2 hxy

variable [Fintype V]

/-- Restrict the actual lists and prescription to a connected induced side.
No list is enlarged, and the short-simple-path bound is transported by the
injective inclusion of native walks. -/
noncomputable def induce (I : ConnectedPrescription G C) (S : Set V) [Nontrivial S]
    (hS : (G.induce S).Preconnected) (hP : ConnSet G (I.vertices ∩ S)) :
    ConnectedPrescription (G.induce S) C := by
  let hex := exists_outer_induced_of_preconnected I.embedding I.outer S hS
  let Q : Set S := {x | x.1 ∈ I.vertices}
  have hc : ConnSet (G.induce S) Q := by
    obtain ⟨a, ha⟩ := hP.1
    refine ⟨⟨⟨a, ha.2⟩, ha.1⟩, ?_⟩
    intro x hx y hy
    let f : V → S := fun z => if hz : z ∈ S then ⟨z, hz⟩ else ⟨a, ha.2⟩
    have hm : RIn (G.induce S) Q (f x.1) (f y.1) :=
      (hP.2 x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩).map f (by
        intro z w hzw hz hw
        simpa only [f, dite_eq_left hz.2, dite_eq_left hw.2] using
          RIn.single (G := G.induce S) (s := Q) (a := ⟨z, hz.2⟩) (b := ⟨w, hw.2⟩)
            hzw hz.1 hw.1)
    simpa only [f, dite_eq_left x.2, dite_eq_left y.2] using hm
  refine {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := hex.choose
    vertices := Q
    connected := hc
    paths_short := ?_
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := fun x hx => hex.choose_spec x (I.on_outer x.1 hx)
    singleton := fun x hx => I.singleton x.1 hx
    proper := fun {_ _} hx hy hxy => I.proper hx hy hxy
    boundary_lists := fun x _ hx => I.outside_list_ge_two hx
    interior_lists := fun x hx => I.interior_lists x.1 (fun h => hx (hex.choose_spec x h))
    short_edges := fun {_ _} hxy hx hy => I.short_edges hxy hx hy }
  intro x y p hp hsub
  have h := I.paths_short (p.map (Embedding.induce S).toHom)
    (hp.map Subtype.val_injective) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (by simpa only [Walk.support_map] using hz)
      exact hsub w hw)
  simpa only [Walk.length_map] using h

end ConnectedPrescription
end Thomassen
