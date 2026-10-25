/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedInstance
public import Thomassen.FaceRestriction

/-! Boundary instances on connected induced pieces, with exact prescribed subgraphs. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
lemma BoundaryPrecolor.reachable_vertices (P : BoundaryPrecolor G) {x y : V}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) : G.Reachable x y := by
  classical
  cases P with
  | empty => simp at hx
  | path p _ _ =>
    exact (p.takeUntil x (List.mem_toFinset.1 hx)).reachable.symm.trans
      (p.takeUntil y (List.mem_toFinset.1 hy)).reachable
  | cycle p _ _ =>
    exact (p.takeUntil x (List.mem_toFinset.1 hx)).reachable.symm.trans
      (p.takeUntil y (List.mem_toFinset.1 hy)).reachable

/-- The original vertices of a component of an induced graph. -/
def componentVertexSet (S : Set V) (K : (G.induce S).ConnectedComponent) : Set V :=
  Subtype.val '' K.supp

/-- Flatten the two subtypes without changing any edge. -/
noncomputable def componentInduceIso (S : Set V) (K : (G.induce S).ConnectedComponent) :
    K.toSimpleGraph ≃g G.induce (componentVertexSet S K) where
  toFun x := ⟨x.1.1, x.1, x.2, rfl⟩
  invFun x := ⟨x.2.choose, x.2.choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (show componentVertexSet S K x.1.1 from ⟨x.1, x.2, rfl⟩).choose_spec.2
  right_inv x := Subtype.ext x.property.choose_spec.2
  map_rel_iff' := Iff.rfl

omit [Fintype V] in
/-- Glue actual induced colourings that agree on a separator. Every original
edge is required to lie in one of the two pieces. -/
lemma glue_induced_colourings (S T : Set V) (L : V → Finset C)
    (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x, cS x ∈ L x.1) (hcT : ∀ x, cT x ∈ L x.1)
    (hagree : ∀ (x : V) (hx : x ∈ S) (hy : x ∈ T), cS ⟨x, hx⟩ = cT ⟨x, hy⟩) :
    ListColourable G L := by
  classical
  let f : V → C := fun x => if hx : x ∈ S then cS ⟨x, hx⟩ else
    cT ⟨x, (hcover x).resolve_left hx⟩
  have hfS : ∀ (x : V) (hx : x ∈ S), f x = cS ⟨x, hx⟩ := by
    intro x hx
    simp only [f, dite_eq_left hx]
  have hfT : ∀ (x : V) (hx : x ∈ T), f x = cT ⟨x, hx⟩ := by
    intro x hx
    by_cases hy : x ∈ S
    · exact (hfS x hy).trans (hagree x hy hx)
    · simp only [f, dite_eq_right hy]
  refine ⟨Coloring.mk f ?_, ?_⟩
  · intro x y hxy
    rcases hedges hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hfS x hx, hfS y hy]
      exact cS.valid hxy
    · rw [hfT x hx, hfT y hy]
      exact cT.valid hxy
  · intro x
    change f x ∈ L x
    rcases hcover x with hx | hx
    · rw [hfS x hx]
      exact hcS ⟨x, hx⟩
    · rw [hfT x hx]
      exact hcT ⟨x, hx⟩

namespace BoundaryInstance

/-- Transport a boundary instance to a connected induced graph once the actual
restricted prescribed path/cycle has been identified. Vertices and edges are
checked separately, so a cut cannot silently change the prescribed subgraph. -/
noncomputable def inducePrecolor (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (P : BoundaryPrecolor (G.induce S))
    (hvertices : ∀ x : S, x ∈ P.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hedges : ∀ x y : S, s(x, y) ∈ P.edges ↔ s(x.1, y.1) ∈ I.precolor.edges) :
    BoundaryInstance (G.induce S) C := by
  classical
  let hex := exists_outer_induced_of_preconnected I.embedding I.outer S hconn
  let outer := hex.choose
  have hface := hex.choose_spec
  refine {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := outer
    precolor := P
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := fun x hx => hface x (I.on_outer x.1 ((hvertices x).1 hx))
    singleton := fun x hx => I.singleton x.1 ((hvertices x).1 hx)
    proper_precolor := fun {x y} hxy => I.proper_precolor ((hedges x y).1 hxy)
    boundary_lists := ?_
    interior_lists := ?_
    short_edges := fun {x y} hxy hx hy => (hedges x y).2 (I.short_edges hxy hx hy) }
  · intro x _ hxp
    exact I.outside_precolor_list_ge_two (fun hp => hxp ((hvertices x).2 hp))
  · intro x hx
    exact I.interior_lists x.1 (fun hf => hx (hface x hf))

/-- Retain the entire prescribed path/cycle in any connected induced graph.
The original face is allowed to merge with other faces. -/
noncomputable def induceConnected (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected)
    (hP : ∀ x ∈ I.precolor.vertices, x ∈ S) : BoundaryInstance (G.induce S) C :=
  I.inducePrecolor S hconn (I.precolor.induce S hP)
    (BoundaryPrecolor.mem_vertices_induce _ S hP)
    (BoundaryPrecolor.mem_edges_induce _ S hP)

/-- A connected induced piece disjoint from the prescribed vertices retains
the same lists and has an empty prescribed path. -/
noncomputable def induceUnprecolored (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected)
    (hP : ∀ x ∈ S, x ∉ I.precolor.vertices) : BoundaryInstance (G.induce S) C := by
  classical
  refine I.inducePrecolor S hconn .empty (fun x => by simp [hP x.1 x.2]) ?_
  intro x y
  have he : s(x.1, y.1) ∉ I.precolor.edges :=
    fun h => hP x.1 x.2 (I.precolor.endpoints_of_mem_edges h).1
  simp [he]

/-- The boundary-extension induction colours every proper induced vertex set
that retains the prescribed walk, even when that induced graph is disconnected.
Every component is strictly smaller than the original graph. -/
lemma colourable_induce_of_smaller (I : BoundaryInstance G C) (S : Set V)
    (hP : ∀ x ∈ I.precolor.vertices, x ∈ S) (hproper : ∃ x, x ∉ S)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable (G.induce S) (fun x => I.lists x.1) := by
  classical
  have hcomponent : ∀ K : (G.induce S).ConnectedComponent,
      ∃ c : K.toSimpleGraph.Coloring C, ∀ x, c x ∈ I.lists x.1.1 := by
    intro K
    let T := componentVertexSet S K
    let φ := componentInduceIso S K
    have hconn : (G.induce T).Preconnected :=
      K.connected_toSimpleGraph.preconnected.map φ.toHom φ.surjective
    have hTsub : T ⊆ S := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have hTsmall : Nat.card T < Nat.card V := by
      obtain ⟨x, hx⟩ := hproper
      exact card_induced_vertices_lt T (fun h => hx (hTsub h))
    have hc : ListColourable (G.induce T) (fun x => I.lists x.1) := by
      by_cases hnt : Nontrivial T
      · let : Nontrivial T := hnt
        by_cases hmeet : ∃ x : S, x ∈ K.supp ∧ x.1 ∈ I.precolor.vertices
        · obtain ⟨a, haK, haP⟩ := hmeet
          have hPT : ∀ x ∈ I.precolor.vertices, x ∈ T := by
            intro x hx
            let p := I.precolor.induce S hP
            have ha : a ∈ p.vertices :=
              (BoundaryPrecolor.mem_vertices_induce _ S hP a).2 haP
            have hb : (⟨x, hP x hx⟩ : S) ∈ p.vertices :=
              (BoundaryPrecolor.mem_vertices_induce _ S hP _).2 hx
            have hr := p.reachable_vertices ha hb
            have heq := SimpleGraph.ConnectedComponent.sound hr
            have hbK : (⟨x, hP x hx⟩ : S) ∈ K.supp := heq.symm.trans haK
            exact ⟨⟨x, hP x hx⟩, hbK, rfl⟩
          simpa only [induceConnected, inducePrecolor] using
            hsmall T (G.induce T) (I.induceConnected T hconn hPT) hTsmall
        · have hPT : ∀ x ∈ T, x ∉ I.precolor.vertices := by
            rintro x ⟨y, hyK, rfl⟩ hyP
            exact hmeet ⟨y, hyK, hyP⟩
          simpa only [induceUnprecolored, inducePrecolor] using
            hsmall T (G.induce T) (I.induceUnprecolored T hconn hPT) hTsmall
      · let f : T → C := fun x => (I.list_nonempty x.1).choose
        exact ⟨Coloring.mk f (fun {x y} hxy => False.elim (hnt hxy.nontrivial)),
          fun x => (I.list_nonempty x.1).choose_spec⟩
    obtain ⟨c, hc⟩ := hc
    exact ⟨c.comp φ.toHom, fun x => hc (φ x)⟩
  let c := (G.induce S).homOfConnectedComponents (fun K => (hcomponent K).choose)
  exact ⟨c, fun x => (hcomponent ((G.induce S).connectedComponentMk x)).choose_spec
    ⟨x, ConnectedComponent.connectedComponentMk_mem⟩⟩

/-- Delete an unprescribed vertex with fewer neighbours than list colours,
apply the strict induction to the remaining components, and restore the vertex
using the registered partial-colouring extension lemma. -/
lemma colourable_of_few_neighbours (I : BoundaryInstance G C) (x : V)
    (hx : x ∉ I.precolor.vertices)
    (hdegree : (Finset.univ.filter (G.Adj x)).card < (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  classical
  let S : Finset V := Finset.univ.erase x
  have hP : ∀ y ∈ I.precolor.vertices, y ∈ (↑S : Set V) := by
    intro y hy
    exact Finset.mem_erase.2 ⟨fun heq => hx (heq ▸ hy), Finset.mem_univ _⟩
  have hcolour := I.colourable_induce_of_smaller (↑S : Set V) hP
    ⟨x, by simp [S]⟩ hsmall
  have hc := (col_restrict_iff_listColourable_induce S I.lists I.prescribed).2 hcolour
  have hle : (S.filter (G.Adj x)).card ≤ (Finset.univ.filter (G.Adj x)).card :=
    Finset.card_le_card (fun y hy => Finset.mem_filter.2
      ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩)
  exact (col_univ_iff I.lists).1
    (col_of_erase Finset.univ I.lists x hc (lt_of_le_of_lt hle hdegree))

end BoundaryInstance
end Thomassen
