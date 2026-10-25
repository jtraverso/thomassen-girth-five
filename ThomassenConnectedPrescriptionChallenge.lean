/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AlternatingBoundaryLists

/-! Separate contracts for mirrored embeddings, the complete prescribed-edge
reduction and connected branching prescriptions below the strict main bound.
None of the ten new solution modules is imported. The final contract checks
one unprescribed outer vertex. The unconditional main theorem is not asserted. -/
@[expose] public section
universe u v

section MirrorEmbeddingContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical

lemma cycleCount_inv_eq {D : Type*} (σ : Perm D) : cycleCount σ⁻¹ = cycleCount σ := by
  sorry
lemma numComponents_inv_left {D : Type*} (σ α : Perm D) :
    numComponents σ⁻¹ α = numComponents σ α := by
  sorry
variable {V : Type u} {G : SimpleGraph V}

@[simp] lemma mirror_dartSymm_inv_apply (d : G.Dart) : (dartSymm G)⁻¹ d = d.symm := by
  sorry
lemma mirror_fst_rot_inv (M : PlaneMap G) (d : G.Dart) : (M.rot⁻¹ d).fst = d.fst := by
  sorry
/-- Reverse the rotation at every vertex, preserving the genus-zero certificate. -/
def mirrorPlaneMap (M : PlaneMap G) : PlaneMap G where
  rot := M.rot⁻¹
  isRotationSystem := {
    fst_apply := mirror_fst_rot_inv M
    sameCycle := fun d e h => (M.isRotationSystem.sameCycle d e h).inv }
  eulerDefect_eq_zero := by
    have heq : M.rot⁻¹ * dartSymm G = (dartSymm G).permCongr (M.rot * dartSymm G)⁻¹ := by
      apply Equiv.ext
      intro d
      simp [mul_inv_rev, dartSymm]
    change eulerDefect M.rot⁻¹ (dartSymm G) = 0
    unfold eulerDefect
    rw [numComponents_inv_left, cycleCount_inv_eq, heq, cycleCount_permCongr, cycleCount_inv_eq]
    exact M.eulerDefect_eq_zero

/-- The mirrored face permutation is the dart reversal conjugate of the
inverse old face permutation. -/
lemma mirror_facePerm (M : PlaneMap G) :
    (mirrorPlaneMap M).facePerm = (dartSymm G).permCongr M.facePerm⁻¹ := by
  sorry
lemma mirror_face_sameCycle (M : PlaneMap G) (d e : G.Dart) :
    SameCycle (mirrorPlaneMap M).facePerm d.symm e.symm ↔ SameCycle M.facePerm d e := by
  sorry
/-- Mirroring changes the directed boundary traversal but retains precisely
the same incident vertices on the selected face. -/
lemma mirror_onOuterFace_iff (M : PlaneMap G) (outer : G.Dart) (x : V) :
    OnOuterFace (mirrorPlaneMap M) outer.symm x ↔ OnOuterFace M outer x := by
  sorry
/-- A complete native facial cycle gives the exact selected face vertex set;
its corner equations cover the whole face orbit, not just a subset of it. -/
lemma native_facial_cycle_support_iff [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (x : V) :
    x ∈ p.support ↔ OnOuterFace M outer x := by
  sorry
/-- Full indexed facial corner equations reverse in the mirrored embedding. -/
lemma mirrored_cycle_isFacial [Fintype V] (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) :
    IsFacialCycleAlong (mirrorPlaneMap M) hc.reverse Set.univ := by
  sorry
/-- Reverse the old native facial order in the actual mirrored map. The new
face orbit is exactly the old selected face with its darts reversed. -/
theorem exists_mirrored_native_face_cycle [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) :
    ∃ q : G.Walk a a, ∃ hq : q.IsCycle, q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p (-(i : ZMod p.length))) ∧
      IsFacialCycleAlong (mirrorPlaneMap M) (walk_isCycleMap q hq) Set.univ ∧
      SameCycle (mirrorPlaneMap M).facePerm outer.symm (walkArcRoot q hq) := by
  sorry
/-- Reverse the actual facial order starting at any chosen old native vertex. -/
theorem exists_mirrored_native_face_cycle_at [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (s : ℕ) (hs : s < p.length) :
    ∃ q : G.Walk (p.getVert s) (p.getVert s), ∃ hq : q.IsCycle, q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s : ZMod p.length)-(i : ZMod p.length))) ∧
      IsFacialCycleAlong (mirrorPlaneMap M) (walk_isCycleMap q hq) Set.univ ∧
      SameCycle (mirrorPlaneMap M).facePerm outer.symm (walkArcRoot q hq) := by
  sorry
namespace BoundaryInstance
variable {C : Type v}

/-- Mirror the embedding while retaining every original list, prescribed
colour, native prescribed path/cycle and short-edge condition. -/
def mirror (I : BoundaryInstance G C) : BoundaryInstance G C where
  girth := I.girth
  embedding := mirrorPlaneMap I.embedding
  outer := I.outer.symm
  precolor := I.precolor
  lists := I.lists
  prescribed := I.prescribed
  on_outer := fun x hx => (mirror_onOuterFace_iff I.embedding I.outer x).2 (I.on_outer x hx)
  singleton := I.singleton
  proper_precolor := I.proper_precolor
  boundary_lists := fun x hx hp => I.boundary_lists x ((mirror_onOuterFace_iff I.embedding I.outer x).1 hx) hp
  interior_lists := fun x hx => I.interior_lists x (fun h => hx ((mirror_onOuterFace_iff I.embedding I.outer x).2 h))
  short_edges := I.short_edges


variable [instFT : Fintype V]
include instFT

/-- The prescription-free three-path reduction also applies when its terminal
boundary endpoint has a short list. Mirroring preserves actual face geometry
and transports the exact open native arc. -/
theorem colourable_of_interior_three_path_free_arc_terminal_short (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hnshort : (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n-2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- A short list at either boundary endpoint closes this prescription-free
three-path cut. Both orientations use actual native face orbits. -/
theorem colourable_of_interior_three_path_free_arc_one_short_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hshort : (I.lists a).card ≤ 2 ∨ (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n-2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end BoundaryInstance
end Thomassen

end MirrorEmbeddingContracts

section PrescribedEdgeClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Every instance with exactly a native edge prescribed is a complete main
induction case. Connectivity, a native facial cycle, placement of the edge and
its two possible orientations are all derived, not assumed. -/
theorem colourable_of_prescribed_edge (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end PrescribedEdgeClosureContracts

section ConnectedPrescriptionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
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
  sorry
/-- Lift a connected set into an induced graph retaining all its vertices. -/
lemma connSet_induce_of_subset (P S : Set V) (hP : ConnSet G P) (hPS : P ⊆ S) :
    ConnSet (G.induce S) {x : S | x.1 ∈ P} := by
  sorry
/-- Restriction to a side of a clique separator preserves connectedness of
a prescribed set containing the separator. The retraction collapses the other
side onto one separator vertex. -/
lemma connSet_inter_of_clique_separator (P S T : Set V) (hP : ConnSet G P)
    (_hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hclique : ∀ x ∈ S ∩ T, ∀ y ∈ S ∩ T, x ≠ y → G.Adj x y)
    (hsepP : S ∩ T ⊆ P) {a : V} (ha : a ∈ S ∩ T) :
    ConnSet G (P ∩ S) := by
  sorry
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
  sorry
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

variable [instFT : Fintype V]
include instFT

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

end ConnectedPrescriptionContracts

section BoundedPrescriptionBaseContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A connected vertex set of maximum induced degree two, whose simple paths
have at most five edges, is exactly a native path or cycle on at most six
vertices. Every induced edge belongs to the resulting native prescription. -/
theorem exists_native_precolor_of_connected_degree_two (P : Set V) (hP : ConnSet G P)
    (hshort : ∀ {a b : V} (p : G.Walk a b), p.IsPath →
      (∀ x ∈ p.support, x ∈ P) → p.length ≤ 5)
    (hthird : ∀ x ∈ P, ∀ r ∈ P, ∀ s ∈ P, ∀ t ∈ P,
      G.Adj x r → G.Adj x s → G.Adj x t → r ≠ s → t = r ∨ t = s) :
    ∃ Q : BoundaryPrecolor G, (∀ x, x ∈ Q.vertices ↔ x ∈ P) ∧
      ∀ {x y}, x ∈ P → y ∈ P → G.Adj x y → s(x,y) ∈ Q.edges := by
  sorry
end Thomassen

end BoundedPrescriptionBaseContracts

section BoundedPrescriptionCutsContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT
namespace ConnectedPrescription

/-- A nonempty clique separator contained in the prescribed set splits the
auxiliary problem into strictly smaller actual instances with unchanged lists.
The restrictions remain connected by the proved clique retraction. -/
theorem colourable_of_clique_cut (I : ConnectedPrescription G C)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hclique : ∀ x ∈ S ∩ T, ∀ y ∈ S ∩ T, x ≠ y → G.Adj x y)
    (hsepP : S ∩ T ⊆ I.vertices) (hne : (S ∩ T).Nonempty)
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hScard : Nat.card S < Nat.card V) (hTcard : Nat.card T < Nat.card V)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  sorry
/-- A piece avoiding all prescribed vertices is an ordinary empty instance.
The selected face is obtained from the actual induced embedding. -/
noncomputable def induceEmpty (I : ConnectedPrescription G C) (T : Set V) [Nontrivial T]
    (hT : (G.induce T).Preconnected) (hdis : ∀ x ∈ T, x ∉ I.vertices) :
    BoundaryInstance (G.induce T) C := by
  let hex := exists_outer_induced_of_preconnected I.embedding I.outer T hT
  exact {
    girth := five_le_egirth_induce T I.girth
    embedding := inducedPlaneMap I.embedding T
    outer := hex.choose
    precolor := .empty
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := by simp
    singleton := by simp
    proper_precolor := by simp
    boundary_lists := fun x _ _ => I.outside_list_ge_two (hdis x.1 x.2)
    interior_lists := fun x hx => I.interior_lists x.1 (fun h => hx (hex.choose_spec x h))
    short_edges := fun {x _} hxy hx hy => (hdis x.1 x.2 (I.short_edges hxy hx hy).1).elim }

/-- At an unprescribed attachment, first colour the side containing the entire
prescription. Then the existing proved root-fan induction fixes that colour in
the other strictly smaller piece, including every old short neighbour. -/
theorem colourable_of_unprescribed_cut (I : ConnectedPrescription G C)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (hwP : w ∉ I.vertices) (hPS : I.vertices ⊆ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hScard : Nat.card S < Nat.card V) (hTcard : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  sorry
/-- Every cutvertex is eliminated in the auxiliary connected-prescription
induction. If it is outside the prescription, connectedness puts the complete
prescription on one side; if it is interior, face connectivity proves that the
other side has three-lists everywhere. -/
theorem colourable_of_cutvertex (I : ConnectedPrescription G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  sorry
end ConnectedPrescription
end Thomassen

end BoundedPrescriptionCutsContracts

section BoundedPrescriptionExtensionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT
namespace ConnectedPrescription

/-- On a simple facial boundary, split each prescribed chord using the actual
strict face cut. Once no such chord remains, the prescribed graph has maximum
degree two, and the bounded-path lemma gives a valid native main instance. -/
theorem colourable_of_facial_boundary (I : ConnectedPrescription G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  sorry
end ConnectedPrescription
omit instFT

/-- A connected branching prescription whose every simple path has at most six
vertices extends below the strict main induction bound. The complete auxiliary
strong induction handles all cutvertices and prescribed chords; its base invokes
the main induction only on graphs of cardinality strictly less than `N`. -/
theorem connectedPrescription_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : ConnectedPrescription G C)
    (hG : G.Preconnected) (hN : Nat.card V < N) : ListColourable G I.lists := by
  sorry
end Thomassen

end BoundedPrescriptionExtensionContracts

section ConnectedResidualExtensionContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT
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
  sorry
end BoundaryInstance
end Thomassen

end ConnectedResidualExtensionContracts

section ShortFaceNeighboursContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} {c : ZMod k → V}

/-- Two neighbours of an exterior vertex cannot be consecutive, or separated
by just one vertex, on a simple cycle. -/
lemma cycle_neighbour_indices_not_near (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) {u : V} (hu : u ∉ Set.range c) (i j : ZMod k)
    (hui : G.Adj u (c i)) (huj : G.Adj u (c j)) : j ≠ i+1 ∧ j ≠ i+2 := by
  sorry
/-- Along either direction of the cycle, distinct neighbours leave at least
three boundary edges between them. -/
lemma cycle_neighbour_nat_gaps (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) {u : V} (hu : u ∉ Set.range c) (i j : ℕ)
    (_hi : i < k) (hj : j < k) (hij : i < j)
    (hui : G.Adj u (c (i : ZMod k))) (huj : G.Adj u (c (j : ZMod k))) :
    i+3 ≤ j ∧ j+3 ≤ i+k := by
  sorry
/-- A vertex outside a cycle of at most eight vertices has at most two
neighbours on that cycle. Three cyclic gaps would require at least nine edges. -/
theorem at_most_two_neighbours_on_short_cycle [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hshort : k ≤ 8) {u : V} (hu : u ∉ Set.range c)
    (i j l : ZMod k) (hui : G.Adj u (c i)) (huj : G.Adj u (c j)) (hul : G.Adj u (c l)) :
    i = j ∨ i = l ∨ j = l := by
  sorry
end Thomassen

end ShortFaceNeighboursContracts

section BoundaryPendantGeometryContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- The support of a native walk is connected. -/
lemma walk_support_connSet {a b : V} (p : G.Walk a b) : ConnSet G {x | x ∈ p.support} := by
  sorry
/-- Attaching any number of vertices, each adjacent to a connected set,
preserves connectedness of the prescribed union. -/
lemma connSet_adjoin_attached_vertices (P R : Set V) (hP : ConnSet G P)
    (hR : ∀ x ∈ R, ∃ y ∈ P, G.Adj x y) : ConnSet G (P ∪ R) := by
  sorry
/-- If a prescribed induced path contains all cycle vertices except `a`,
its initial endpoint is adjacent to `a`. The two cycle neighbours cannot both
be the unique prescribed neighbour of that endpoint. -/
lemma path_endpoint_adjacent_to_single_cycle_complement {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k) {a b t : V}
    (r : G.Walk b t) (hr : r.IsPath) (_ha : a ∉ r.support)
    (hcover : ∀ x, x ∈ Set.range c ↔ x = a ∨ x ∈ r.support)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges) :
    G.Adj b a := by
  sorry
/-- A short prescribed path with independent leaves attached only to its
internal vertices has no simple prescribed path on more than six vertices.
The four internal old vertices form the entire possible branching core. -/
lemma short_path_with_pendant_vertices_paths_short [Fintype V] {a b : V}
    (r : G.Walk a b) (hr : r.IsPath) (hlen : r.length ≤ 5) (hab : a ≠ b)
    (hedges : ∀ {x y}, x ∈ r.support → y ∈ r.support → G.Adj x y → s(x,y) ∈ r.edges)
    (R : Set V)
    (hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y)
    (hRunique : ∀ x ∈ R, ∀ y ∈ r.support, ∀ z ∈ r.support,
      G.Adj x y → G.Adj x z → y = z)
    (hRends : ∀ x ∈ R, ¬ G.Adj x a ∧ ¬ G.Adj x b)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath)
    (hsub : ∀ z ∈ q.support, z ∈ {z | z ∈ r.support} ∪ R) : q.length ≤ 5 := by
  sorry
end Thomassen

end BoundaryPendantGeometryContracts

section SingleBoundaryComplementContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The actual facial case with one unprescribed boundary vertex, including a
six-vertex prescription on a seven-vertex face. New short neighbours attached
to the old path are coloured as pendant vertices; the complete auxiliary
induction handles their arbitrarily many branches and disconnected remainders. -/
theorem colourable_of_single_boundary_complement (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (haP : a ∉ I.precolor.vertices)
    (hcover : ∀ x, x ∈ p.support ↔ x = a ∨ x ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The full strict main-induction case when exactly one vertex of the
original selected outer face lies outside the prescribed native path.
Connectivity, chordlessness, facial placement and rebasing are all derived. -/
theorem colourable_of_unique_unprescribed_outer_vertex (I : BoundaryInstance G C)
    {b t : V} (r : G.Walk b t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (x : V)
    (hxf : OnOuterFace I.embedding I.outer x) (hxP : x ∉ I.precolor.vertices)
    (hunique : ∀ y, OnOuterFace I.embedding I.outer y → y ∉ I.precolor.vertices → y = x)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end SingleBoundaryComplementContracts
