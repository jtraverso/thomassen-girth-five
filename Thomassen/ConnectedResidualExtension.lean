/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundedPrescriptionExtension

/-! Residual colourings with connected branching boundary prescriptions. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- After a connected boundary deletion, extend a proper connected residual
prescription whose simple paths have at most six vertices. Prescribed vertices
may be newly exposed neighbours of the deletion. Each actual remaining
component is treated separately, so deletion connectivity is not assumed. -/
theorem colourable_of_connected_residual_prescription (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ p.support)
    (A : Finset V) (ha : a ∈ A) (hA : ConnSet G (↑A : Set V))
    (f : V → C) (hf : ∀ x ∈ A, f x ∈ I.lists x)
    (hproper : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (Q : Set V) (hQconn : ConnSet G Q) (hQA : ∀ x ∈ Q, x ∉ A)
    (hQface : ∀ x ∈ Q, OnOuterFace I.embedding I.outer x ∨ ∃ y ∈ A, G.Adj x y)
    (hQpaths : ∀ {x y : V} (q : G.Walk x y), q.IsPath →
      (∀ z ∈ q.support, z ∈ Q) → q.length ≤ 5)
    (hQshort : ∀ x ∈ Q, (residual G I.lists A f x).card ≤ 2)
    (g : V → C) (hg : ∀ x ∈ Q, g x ∈ residual G I.lists A f x)
    (hgp : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y)
    (hTwo : ∀ x, x ∉ A → x ∉ Q → 2 ≤ (residual G I.lists A f x).card)
    (hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 →
      x ∈ Q ∧ y ∈ Q)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let S : Set V := (↑A : Set V)ᶜ
  let r := residual G I.lists A f
  let L : V → Finset C := fun x => if x ∈ Q then {g x} else r x
  have hLsub : ∀ x, L x ⊆ r x := by
    intro x c hc
    by_cases hx : x ∈ Q
    · have heq : c = g x := Finset.mem_singleton.1 (by simpa only [L,ite_eq_left hx] using hc)
      exact heq ▸ hg x hx
    · simpa only [L,ite_eq_right hx] using hc
  have hnonempty : ∀ x ∈ S, (L x).Nonempty := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · simp only [L,ite_eq_left hxQ]; exact Finset.singleton_nonempty _
    · simp only [L,ite_eq_right hxQ]
      have h2 : 2 ≤ (r x).card := hTwo x hx hxQ
      exact Finset.card_pos.1 (by omega)
  have hcomponent : ∀ K : (G.induce S).ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, ∀ x, c x ∈ L x.1.1 := by
    intro K
    let T := componentVertexSet S K
    let φ := componentInduceIso S K
    have hc : ListColourable (G.induce T) (fun x => L x.1) := by
      by_cases hnt : Nontrivial T
      · let : Nontrivial T := hnt
        obtain ⟨o,hold,hnew⟩ := exists_outer_component_after_connected_boundary_deletion I.embedding I.outer hG
          p hp hface hroot hExact (↑A : Set V) ha hA K
        have hQTface : ∀ x : T, x.1 ∈ Q → OnOuterFace (inducedPlaneMap I.embedding T) o x := by
          intro x hx
          rcases hQface x.1 hx with h | h
          · exact hold x h
          · exact hnew x h
        have hInterior : ∀ x : T, ¬ OnOuterFace (inducedPlaneMap I.embedding T) o x →
            3 ≤ (L x.1).card := by
          intro x hx
          have hxQ : x.1 ∉ Q := fun h => hx (hQTface x h)
          have hr : r x.1 = I.lists x.1 := by
            apply residual_unchanged
            intro y hy hxy
            exact hx (hnew x ⟨y,hy,hxy⟩)
          simp only [L,ite_eq_right hxQ,hr]
          exact I.interior_lists x.1 (fun h => hx (hold x h))
        have hTcard : Nat.card T < Nat.card V := card_induced_vertices_lt T
          (x := a) (fun h => (componentVertexSet_subset S K h) ha)
        by_cases hmeet : ∃ x ∈ T, x ∈ Q
        · obtain ⟨x,hxT,hxQ⟩ := hmeet
          have hQT : Q ⊆ T := by
            intro y hy
            have hr := hQconn.2 x hxQ y hy
            induction hr with
            | refl => exact hxT
            | @tail z w _ hzw ih =>
              exact componentVertexSet_adj_closed S K (ih hzw.2.1) (hQA w hzw.2.2) hzw.1
          let J : ConnectedPrescription (G.induce T) C := {
            girth := five_le_egirth_induce T I.girth
            embedding := inducedPlaneMap I.embedding T
            outer := o
            vertices := {x : T | x.1 ∈ Q}
            connected := connSet_induce_of_subset Q T hQconn hQT
            paths_short := by
              intro x y q hq hsub
              have hm := hQpaths (q.map (Embedding.induce T).toHom) (hq.map Subtype.val_injective) (by
                intro z hz
                rw [Walk.support_map] at hz
                obtain ⟨w,hw,heq⟩ := List.mem_map.1 hz
                change w.1 = z at heq
                exact heq ▸ hsub w hw)
              simpa only [Walk.length_map] using hm
            lists := fun x => L x.1
            prescribed := fun x => g x.1
            on_outer := hQTface
            singleton := fun x hx => by
              change x.1 ∈ Q at hx
              exact ite_eq_left hx
            proper := fun {x y} hx hy hxy => hgp x.1 hx y.1 hy hxy
            boundary_lists := fun x _ hx => by
              change x.1 ∉ Q at hx
              change 2 ≤ (if x.1 ∈ Q then {g x.1} else r x.1).card
              rw [ite_eq_right hx]
              exact hTwo x.1 (componentVertexSet_subset S K x.2) hx
            interior_lists := hInterior
            short_edges := by
              intro x y hxy hx hy
              have hxS := componentVertexSet_subset S K x.2
              have hyS := componentVertexSet_subset S K y.2
              by_cases hxQ : x.1 ∈ Q <;> by_cases hyQ : y.1 ∈ Q
              · exact ⟨hxQ,hyQ⟩
              · have hys : (r y.1).card ≤ 2 := by simpa only [L,ite_eq_right hyQ] using hy
                have hxs : (r x.1).card ≤ 2 := hQshort x.1 hxQ
                exact (hyQ (hShort x.1 hxS y.1 hyS hxy hxs hys).2).elim
              · have hxs : (r x.1).card ≤ 2 := by simpa only [L,ite_eq_right hxQ] using hx
                have hys : (r y.1).card ≤ 2 := hQshort y.1 hyQ
                exact (hxQ (hShort x.1 hxS y.1 hyS hxy hxs hys).1).elim
              · exact hShort x.1 hxS y.1 hyS hxy
                  (by simpa only [L,ite_eq_right hxQ] using hx)
                  (by simpa only [L,ite_eq_right hyQ] using hy) }
          have hconn : (G.induce T).Preconnected := K.connected_toSimpleGraph.preconnected.map φ.toHom φ.surjective
          exact connectedPrescription_extension_of_smaller (Nat.card V) hsmall J hconn hTcard
        · let J : BoundaryInstance (G.induce T) C := {
            girth := five_le_egirth_induce T I.girth
            embedding := inducedPlaneMap I.embedding T
            outer := o
            precolor := .empty
            lists := fun x => L x.1
            prescribed := fun x => g x.1
            on_outer := by simp
            singleton := by simp
            proper_precolor := by simp
            boundary_lists := fun x _ _ => by
              have hx : x.1 ∉ Q := fun h => hmeet ⟨x.1,x.2,h⟩
              simpa only [L,ite_eq_right hx] using hTwo x.1 (componentVertexSet_subset S K x.2) hx
            interior_lists := hInterior
            short_edges := by
              intro x y hxy hx hy
              have hxQ : x.1 ∉ Q := fun h => hmeet ⟨x.1,x.2,h⟩
              have hyQ : y.1 ∉ Q := fun h => hmeet ⟨y.1,y.2,h⟩
              exact (hxQ (hShort x.1 (componentVertexSet_subset S K x.2)
                y.1 (componentVertexSet_subset S K y.2) hxy
                (by simpa only [L,ite_eq_right hxQ] using hx)
                (by simpa only [L,ite_eq_right hyQ] using hy)).1).elim }
          exact hsmall T (G.induce T) J hTcard
      · let c : T → C := fun x => (hnonempty x.1 (componentVertexSet_subset S K x.2)).choose
        exact ⟨Coloring.mk c (fun {x y} hxy => (hnt hxy.nontrivial).elim), fun x =>
          (hnonempty x.1 (componentVertexSet_subset S K x.2)).choose_spec⟩
    obtain ⟨c,hc⟩ := hc
    exact ⟨c.comp φ.toHom,fun x => hc (φ x)⟩
  let c : (G.induce S).Coloring C := (G.induce S).homOfConnectedComponents (fun K => (hcomponent K).choose)
  have hc : ∀ x : S, c x ∈ r x.1 := fun x => hLsub x.1
    ((hcomponent ((G.induce S).connectedComponentMk x)).choose_spec ⟨x,ConnectedComponent.connectedComponentMk_mem⟩)
  let d : V → C := fun x => if hx : x ∈ A then f x else c ⟨x,hx⟩
  have hne : ∀ x ∈ Finset.univ \ A, x ∉ A := fun x hx => (Finset.mem_sdiff.1 hx).2
  apply (col_univ_iff I.lists).1
  apply glue_residual Finset.univ A I.lists f d hf hproper
  · intro x hx
    simpa only [d,dite_eq_right (hne x hx)] using hc ⟨x,hne x hx⟩
  · intro x hx y hy hxy
    simpa only [d,dite_eq_right (hne x hx),dite_eq_right (hne y hy)] using
      c.valid (show (G.induce S).Adj ⟨x,hne x hx⟩ ⟨y,hne y hy⟩ from hxy)

end BoundaryInstance
end Thomassen
