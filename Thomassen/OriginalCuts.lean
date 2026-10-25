/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalInstance
public import Thomassen.FacialChordNormalization
public import Thomassen.CutSidePair

/-! Strict cuts for the exceptional-edge induction of the original Theorem 2.1. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
/-- Glue actual induced colourings and retain the two prescribed values.
The list-colouring glue is reused with a pinned list at each vertex of S. -/
theorem extends_of_glued_colourings (I : OriginalBoundaryInstance G C)
    (S T : Set V) (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x, cS x ∈ I.lists x.1) (hcT : ∀ x, cT x ∈ I.lists x.1)
    (hagree : ∀ (x : V) (hx : x ∈ S) (hy : x ∈ T), cS ⟨x,hx⟩ = cT ⟨x,hy⟩)
    (hca : cS ⟨I.a,haS⟩ = I.ta) (hcb : cS ⟨I.b,hbS⟩ = I.tb) : I.Extends := by
  let L' : V → Finset C := fun x => if hx : x ∈ S then {cS ⟨x,hx⟩} else I.lists x
  obtain ⟨c,hc⟩ := glue_induced_colourings S T L'
    (by intro x; have h := Set.mem_univ x; rwa [← hcover] at h) hedges cS cT
    (by intro x; simp only [L',dite_eq_left x.2,Finset.mem_singleton]) (by
      intro x
      by_cases hx : x.1 ∈ S
      · simp only [L',dite_eq_left hx,Finset.mem_singleton]
        exact (hagree x.1 hx x.2).symm
      · simpa only [L',dite_eq_right hx] using hcT x) hagree
  have hfixed : ∀ x : S, c x.1 = cS x := by
    intro x
    simpa only [L',dite_eq_left x.2,Finset.mem_singleton] using hc x.1
  refine ⟨c,?_,(hfixed ⟨I.a,haS⟩).trans hca,(hfixed ⟨I.b,hbS⟩).trans hcb⟩
  intro x
  by_cases hx : x ∈ S
  · rw [hfixed ⟨x,hx⟩]; exact hcS ⟨x,hx⟩
  · simpa only [L',dite_eq_right hx] using hc x

/-- In a strictly smaller induced graph, a permitted colour on an actual
face vertex extends using an incident dart of that face as the new fixed edge.
The allowed second colour is chosen from a genuine list of size at least two. -/
theorem extend_vertex_on_induced_face_of_smaller (I : OriginalBoundaryInstance G C)
    (S : Set V) (outer : (G.induce S).Dart)
    (hAface : ∀ x : S, x.1 ∈ I.short → OnOuterFace (inducedPlaneMap I.embedding S) outer x)
    (w : S) (hw : OnOuterFace (inducedPlaneMap I.embedding S) outer w)
    (tw : C) (htw : tw ∈ I.lists w.1) (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧ c w = tw := by
  obtain ⟨d,hd,hdw⟩ := hw
  obtain ⟨tz,htz,htzw⟩ := Finset.exists_mem_ne (s := I.lists d.snd.1)
    (by have := I.list_two d.snd.1; omega) tw
  have hz : OnOuterFace (inducedPlaneMap I.embedding S) outer d.snd :=
    ⟨(inducedPlaneMap I.embedding S).facePerm d,hd.apply_right,
      (inducedPlaneMap I.embedding S).isRotationSystem.fst_apply d.symm⟩
  let J : OriginalBoundaryInstance (G.induce S) C := {
    embedding := inducedPlaneMap I.embedding S
    outer := outer
    girth := five_le_egirth_induce S I.girth
    short := {x : S | x.1 ∈ I.short}
    on_outer := hAface
    short_shape := I.short_shape.induce I.short S
    lists := fun x => I.lists x.1
    list_two := fun x => I.list_two x.1
    list_three := fun x hx => I.list_three x.1 hx
    a := d.fst
    b := d.snd
    edge := d.adj
    a_outer := ⟨d,hd,rfl⟩
    b_outer := hz
    ta := tw
    tb := tz
    ta_mem := by simpa only [hdw] using htw
    tb_mem := htz
    colours_ne := htzw.symm }
  obtain ⟨c,hc,hca,_⟩ := hsmall S (G.induce S) J hSsmall
  exact ⟨c,hc,by change c d.fst = tw at hca; simpa only [hdw] using hca⟩

/-- Original proof, step (2): every cutvertex is eliminated. The component
containing the old fixed edge is coloured first. For the other side, the cut
vertex is on the projected old face, or the old selected face misses that
side altogether. In both cases an actual suitable face is constructed. -/
theorem extends_of_cutvertex (I : OriginalBoundaryInstance G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  obtain ⟨S,hwS,haS,hbS,⟨l,hlS,hlw⟩,⟨r,hrS⟩,hsep⟩ :=
    exists_cut_side_containing_edge w I.a I.b I.edge hdisc
  let T : Set V := insert w Sᶜ
  have hwT : w ∈ T := Or.inl rfl
  have hrT : r ∈ T := Or.inr hrS
  have hrw : r ≠ w := fun h => hrS (h ▸ hwS)
  have hlT : l ∉ T := by
    simpa only [T,Set.mem_insert_iff,Set.mem_compl_iff,hlw,false_or,not_not] using hlS
  let : Nontrivial S := ⟨⟨⟨l,hlS⟩,⟨w,hwS⟩,fun h => hlw (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨r,hrT⟩,⟨w,hwT⟩,fun h => hrw (congrArg Subtype.val h)⟩⟩
  obtain ⟨hcover,hinter,hedges,hsepT⟩ := cut_side_pair_properties hwS hsep
  have hSc := preconnected_cut_side hG hwS hsep
  have hTc := preconnected_cut_side hG hwT hsepT
  let JS := I.induceWithEdge S hSc I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) JS (card_induced_vertices_lt S hrS)
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := hcS
  obtain ⟨oT,hwface,hAface⟩ : ∃ oT : (G.induce T).Dart,
      OnOuterFace (inducedPlaneMap I.embedding T) oT ⟨w,hwT⟩ ∧
      ∀ x : T, x.1 ∈ I.short → OnOuterFace (inducedPlaneMap I.embedding T) oT x := by
    by_cases hwold : OnOuterFace I.embedding I.outer w
    · obtain ⟨oT,hoT⟩ := exists_outer_induced_of_preconnected I.embedding I.outer T hTc
      exact ⟨oT,hoT _ hwold,fun x hx => hoT x (I.on_outer x.1 hx)⟩
    · have hNoFace : ∀ x : T, ¬ OnOuterFace I.embedding I.outer x.1 := by
        intro x hxface
        have hpath : RIn G ({w} : Set V)ᶜ I.a x.1 :=
          ((onOuterFace_connSet I.embedding I.outer).2 I.a I.a_outer x.1 hxface).mono_set
            (fun z hz h => hwold (h ▸ hz))
        have hxS := (rIn_side_of_avoids_cut hsep hpath).1 haS
        have hxw : x.1 = w := by
          have h : x.1 ∈ S ∩ T := ⟨hxS,x.2⟩
          rwa [hinter] at h
        exact hwold (hxw ▸ hxface)
      obtain ⟨z,hwz⟩ := hTc.exists_adj_of_nontrivial (⟨w,hwT⟩ : T)
      let oT : (G.induce T).Dart := ⟨(⟨w,hwT⟩,z),hwz⟩
      exact ⟨oT,onOuterFace_self _ _,fun x hx => (hNoFace x (I.on_outer x.1 hx)).elim⟩
  obtain ⟨cT,hcT,hcw⟩ := I.extend_vertex_on_induced_face_of_smaller T oT hAface ⟨w,hwT⟩
    hwface (cS ⟨w,hwS⟩) (hS _) (card_induced_vertices_lt T hlT) hsmall
  apply I.extends_of_glued_colourings S T hcover hedges haS hbS cS cT hS hcT ?_ hca hcb
  intro x hx hy
  have hxw : x = w := by have h : x ∈ S ∩ T := ⟨hx,hy⟩; rwa [hinter] at h
  subst x
  exact hcw.symm

/-- Original proof, step (3), for an actual edge separator. Colour the side
containing the fixed edge, then use the separator edge as the fixed edge of
the other strictly smaller original instance. Exceptional short sets and their
no-two-path condition are inherited by the proved induced restriction. -/
theorem extends_of_edge_separation (I : OriginalBoundaryInstance G C)
    (S T : Set V) (u w : V) (huw : G.Adj u w)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (haS : I.a ∈ S) (hbS : I.b ∈ S)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  have huST : u ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hwST : w ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
  have hAdjS : (G.induce S).Adj ⟨u,huST.1⟩ ⟨w,hwST.1⟩ := huw
  have hAdjT : (G.induce T).Adj ⟨u,huST.2⟩ ⟨w,hwST.2⟩ := huw
  let : Nontrivial S := hAdjS.nontrivial
  let : Nontrivial T := hAdjT.nontrivial
  let JS := I.induceWithEdge S hSc I.a I.b haS hbS I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne
  obtain ⟨cS,hcS,hca,hcb⟩ := hsmall S (G.induce S) JS hSsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := hcS
  let JT := I.induceWithEdge T hTc u w huST.2 hwST.2 huw hu hw
    (cS ⟨u,huST.1⟩) (cS ⟨w,hwST.1⟩) (hS _) (hS _) (cS.valid hAdjS)
  obtain ⟨cT,hcT,hcu,hcw⟩ := hsmall T (G.induce T) JT hTsmall
  apply I.extends_of_glued_colourings S T hcover hedges haS hbS cS cT hS hcT ?_ hca hcb
  intro x hx hy
  have hxI : x ∈ ({u,w} : Set V) := hinter ▸ (show x ∈ S ∩ T from ⟨hx,hy⟩)
  rcases hxI with rfl | hxw
  · exact hcu.symm
  · have he : x = w := Set.mem_singleton_iff.1 hxw
    subst x
    exact hcw.symm

/-- All orientations of the fixed edge relative to an actual edge cut.
An original graph edge cannot straddle the supplied pieces. -/
theorem extends_of_edge_cut (I : OriginalBoundaryInstance G C)
    (S T : Set V) (u w : V) (huw : G.Adj u w)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {u,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  rcases hedges I.edge with h | h
  · exact I.extends_of_edge_separation S T u w huw hu hw hcover hinter hedges hSc hTc
      h.1 h.2 hSsmall hTsmall hsmall
  · exact I.extends_of_edge_separation T S u w huw hu hw
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm])
      (fun {_ _} h => (hedges h).symm) hTc hSc h.1 h.2 hTsmall hSsmall hsmall

/-- An actual chord of a simple facial boundary cannot occur in a smallest
counterexample to the original invariant. The strict cut is constructed from
its native face corners, rather than assumed as a topological diagram. -/
theorem extends_of_boundary_chord (I : OriginalBoundaryInstance G C)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ) (hG : G.Preconnected)
    (houter : ∀ i, OnOuterFace I.embedding I.outer (c i))
    (i j : ZMod k) (hadj : G.Adj (c i) (c j))
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  obtain ⟨S,T,hS,hT,hcover,hinter,hedges,hSc,hTc⟩ := full_face_chord_separation_at
    I.embedding hc hk hface hG i j hadj hforward hbackward
  exact I.extends_of_edge_cut S T (c i) (c j) hadj (houter i) (houter j)
    hcover hinter hedges hSc.preconnected hTc.preconnected hS hT hsmall

end Thomassen.OriginalBoundaryInstance
