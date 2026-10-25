/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedInstance

/-! Contracts over the previously checked instance and induced-map infrastructure.
Neither FaceRestriction, ConnectedInstance nor CutPrecolor is imported.
Strict smaller-cardinality induction hypotheses are explicit in the reductions.
-/

@[expose] public section
section FaceRestrictionContracts
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

omit [Fintype V] in
private lemma face_fst (M : PlaneMap G) (d : G.Dart) :
    (M.facePerm d).fst = d.snd := by
  sorry

/-- Gaps at incidences of the same original face belong to the same retained
face, provided the retained subgraph is connected on its active vertices. -/
lemma sameCycle_restrict_of_same_original_face (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d t : G.Dart} {e f : H.Dart}
    (hface : SameCycle M.facePerm d t)
    (hd : IsNextH M hH d e) (ht : IsNextH M hH t f) :
    SameCycle (restrictMap M hH).facePerm e f := by
  sorry

/-- All retained active vertices on an old face lie on the projected new face. -/
lemma onOuterFace_restrict_of_connected (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer : G.Dart) {d : G.Dart} {e : H.Dart}
    (hd : SameCycle M.facePerm outer d) (he : IsNextH M hH d e)
    {x : V} (hx : x ∈ subVerts H) (hxf : OnOuterFace M outer x) :
    OnOuterFace (restrictMap M hH) e x := by
  sorry

omit [Fintype V] in
/-- In a nontrivial connected induced graph, all retained vertices are active. -/
lemma subVerts_restrict_of_preconnected (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) : subVerts (restrict G S) = S := by
  sorry

omit [Fintype V] in
/-- A connected induced graph is connected also in the ambient restriction API. -/
lemma restrict_reachable_of_induce_preconnected (S : Set V)
    (hconn : (G.induce S).Preconnected) :
    ∀ a ∈ subVerts (restrict G S), ∀ b ∈ subVerts (restrict G S),
      (restrict G S).Reachable a b := by
  sorry

/-- A chosen original face projects to some face of any nontrivial connected
induced subgraph. Only an implication is asserted: restriction may merge faces. -/
lemma exists_outer_induced_of_preconnected (M : PlaneMap G) (outer : G.Dart)
    (S : Set V) [Nontrivial S] (hconn : (G.induce S).Preconnected) :
    ∃ o : (G.induce S).Dart, ∀ x : S, OnOuterFace M outer x.1 →
      OnOuterFace (inducedPlaneMap M S) o x := by
  sorry

/-- Deleting a connected set through an edge of the old face exposes every
remaining neighbour of that set on the same new face. The remaining induced
graph must be connected; original face incidences are retained as well. -/
lemma exists_outer_induced_after_connected_deletion (M : PlaneMap G) (outer : G.Dart)
    (A : Set V) [Nontrivial (Aᶜ : Set V)]
    (hremain : (G.induce Aᶜ).Preconnected) (hA : ConnSet G A)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∉ A) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce Aᶜ).Dart,
      (∀ x : (Aᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ x : (Aᶜ : Set V), (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) := by
  sorry

end Thomassen

end FaceRestrictionContracts


section ConnectedInstanceContracts
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
lemma BoundaryPrecolor.reachable_vertices (P : BoundaryPrecolor G) {x y : V}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) : G.Reachable x y := by
  sorry

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
  sorry

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
  sorry

/-- Delete an unprescribed vertex with fewer neighbours than list colours,
apply the strict induction to the remaining components, and restore the vertex
using the registered partial-colouring extension lemma. -/
lemma colourable_of_few_neighbours (I : BoundaryInstance G C) (x : V)
    (hx : x ∉ I.precolor.vertices)
    (hdegree : (Finset.univ.filter (G.Adj x)).card < (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end ConnectedInstanceContracts


section CutPrecolorContracts
open LeanPool.K5MinorFreeChoosability SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {v : V} {S : Set V}

/-- Along a walk avoiding the separating vertex, membership in a cut side is
constant. The hypothesis allows crossing edges only at that vertex. -/
lemma walk_side_of_avoids_cut
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (p : G.Walk a b) (havoid : v ∉ p.support) :
    ∀ x ∈ p.support, x ∈ S ↔ a ∈ S := by
  sorry

/-- A simple path starting at the cutvertex either lies wholly in a side, or
meets that side only at its first vertex. -/
lemma path_side_dichotomy (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a : V} (p : G.Walk v a) (hp : p.IsPath) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = v) := by
  sorry

/-- A branch meeting a side at only one vertex contributes no edge inside it. -/
lemma not_mem_edges_of_one_vertex_intersection {a b : V} (p : G.Walk a b)
    (hp : ∀ x ∈ p.support, x ∈ S ↔ x = v)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : s(x, y) ∉ p.edges := by
  sorry

/-- The intersection of a simple path with a cut side containing a vertex of
that path is again a simple path. Its vertex and edge sets are exact. -/
lemma exists_path_on_cut_side (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hvp : v ∈ p.support) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧
      (∀ x, x ∈ q.support ↔ x ∈ p.support ∧ x ∈ S) ∧
      (∀ x y, x ∈ S → y ∈ S → (s(x, y) ∈ q.edges ↔ s(x, y) ∈ p.edges)) := by
  sorry

/-- A simple cycle through a cutvertex lies in a side or meets it only at the
cutvertex. Removing its repeated last vertex gives the required simple path. -/
lemma cycle_side_dichotomy (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S))
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hvp : v ∈ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = v) := by
  sorry

/-- The exact precoloured subgraph retained on either side of a cut through a
precoloured vertex is again an admissible path/cycle of at most six vertices. -/
lemma BoundaryPrecolor.exists_induce_cut (P : BoundaryPrecolor G)
    (hv : v ∈ S) (hvp : v ∈ P.vertices)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S)) :
    ∃ Q : BoundaryPrecolor (G.induce S),
      (∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ P.vertices) ∧
      (∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ P.edges) := by
  sorry

/-- Every cut side containing the separating vertex is connected when the
original graph is connected. Simple paths cannot leave and re-enter that side. -/
lemma preconnected_cut_side (hconn : G.Preconnected) (hv : v ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S)) :
    (G.induce S).Preconnected := by
  sorry

/-- Disconnection after deleting `v` supplies a genuine nontrivial cut side. -/
lemma exists_cut_side_of_delete_disconnected
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, v ∈ S ∧ (∃ a ∈ S, a ≠ v) ∧ (∃ b, b ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v → (x ∈ S ↔ y ∈ S) := by
  sorry

namespace BoundaryInstance
universe w
variable {C : Type w} [Fintype V]

/-- The full cutvertex reduction when the separating vertex is prescribed.
Both smaller instances retain the exact appropriate subpath/cycle and their
colourings agree at the prescribed singleton. -/
lemma colourable_of_precolored_cutvertex (I : BoundaryInstance G C) (v : V)
    (hvP : v ∈ I.precolor.vertices) (hconn : G.Preconnected)
    (hdisc : ¬ (G.induce ({v} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance

end Thomassen

end CutPrecolorContracts
