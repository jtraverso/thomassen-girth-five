/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PrescribedPathOrder

/-! Independent contracts for anchored fan induction and the complete boundary
chord reduction. None of the ten new proof modules is imported.
The unconditional main theorem remains open. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section AnchoredFanContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance

/-- Star colours compatible with original lists extend to a proper colouring
of the union with the original prescription, preserving every singleton. -/
lemma exists_prescribed_rootStar_colours (I : BoundaryInstance G C) (b : V) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y) :
    ∃ g : V → C, (∀ x ∈ rootStar I b, g x = f x) ∧
      (∀ x ∈ I.precolor.vertices, g x = I.prescribed x) ∧
      (∀ x, x ∈ I.precolor.vertices ∨ x ∈ rootStar I b → g x ∈ I.lists x) ∧
      (∀ x, x ∈ I.precolor.vertices ∨ x ∈ rootStar I b →
        ∀ y, y ∈ I.precolor.vertices ∨ y ∈ rootStar I b → G.Adj x y → g x ≠ g y) := by
  sorry

/-- If the union of the old prescription and fixed root fan is a native
induced path on at most six vertices, the strict main induction extends it.
Every original singleton and every fixed short-neighbour colour is retained. -/
theorem rootStar_extension_of_prescribed_path (I : BoundaryInstance G C)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    {a t : V} (q : G.Walk a t) (hq : q.IsPath) (hlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ I.precolor.vertices ∨ x ∈ rootStar I b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanContracts

section AnchoredFanCutsContracts
namespace Thomassen
open Classical

/-- The recursive fan obligation, with its own strictly smaller vertex bound.
The old prescription has at most three vertices and is adjacent to the root. -/
def AnchoredFanBelow (C : Type v) (n : ℕ) : Prop :=
  ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
    J.precolor.vertices.card ≤ 3 → ∀ b : W, b ∉ J.precolor.vertices →
    (∃ a ∈ J.precolor.vertices, H.Adj b a) → H.Preconnected →
    OnOuterFace J.embedding J.outer b → ∀ f : W → C,
    (∀ x ∈ rootStar J b, f x ∈ J.lists x) →
    (∀ x ∈ rootStar J b, ∀ y ∈ rootStar J b, H.Adj x y → f x ≠ f y) →
    Nat.card W < n → RootStarExtension J b f

variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

omit [Fintype V] in
/-- Restriction decreases the number of original prescribed vertices. -/
lemma induced_precolor_card_le (I : BoundaryInstance G C) (S : Set V)
    (Q : BoundaryPrecolor (G.induce S))
    (hv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ I.precolor.vertices) :
    Q.vertices.card ≤ I.precolor.vertices.card := by
  sorry

/-- Apply the auxiliary strict induction on an exact induced prescription.
All root-star memberships and colours are transported from the original graph. -/
lemma anchoredFan_on_induced (I : BoundaryInstance G C) (hcard : I.precolor.vertices.card ≤ 3)
    (b : V) (hbP : b ∉ I.precolor.vertices) (hbface : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hp : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    (S : Set V) [Nontrivial S] (hSc : (G.induce S).Preconnected) (hbS : b ∈ S)
    (ha : ∃ a ∈ S, a ∈ I.precolor.vertices ∧ G.Adj b a)
    (Q : BoundaryPrecolor (G.induce S))
    (hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hQe : ∀ x y : S, s(x, y) ∈ Q.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (hSsmall : Nat.card S < Nat.card V) (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) :
    ∃ cS : (G.induce S).Coloring C, (∀ x : S, cS x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ rootStar I b → cS x = f x.1 := by
  sorry

/-- An auxiliary spoke piece containing no private original prescription is
solved by the already verified two-endpoint fan theorem. The fixed spoke is
short in the original instance, so no extra fixed colours are invented. -/
lemma rootStar_on_released_spoke_piece (I : BoundaryInstance G C)
    (b x : V) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (hxface : OnOuterFace I.embedding I.outer x)
    (hb3 : 3 ≤ (I.lists b).card) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (T : Set V) [Nontrivial T] (hTc : (G.induce T).Preconnected) (hbT : b ∈ T) (hxT : x ∈ T)
    (hPcap : ∀ y ∈ T, y ∈ I.precolor.vertices → y = b ∨ y = x)
    (N : ℕ) (hTsmall : Nat.card T < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) :
    ∃ cT : (G.induce T).Coloring C, (∀ y : T, cT y ∈ I.lists y.1) ∧
      ∀ y : T, y.1 ∈ rootStar I b → cT y = f y.1 := by
  sorry

omit [Fintype V] in
/-- A nonempty prescription on at most three vertices is an actual path of
at most two edges; girth five rules out the cycle constructor. -/
lemma exists_short_prescribed_path (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (hne : ∃ x, x ∈ I.precolor.vertices) :
    ∃ a t, ∃ p : G.Walk a t, ∃ hp : p.IsPath, ∃ hn : p.support.toFinset.card ≤ 6,
      I.precolor = .path p hp hn ∧ p.length ≤ 2 := by
  sorry

/-- Split through prescribed separator vertices, keeping the root in one
piece. The other piece uses the main induction and the original singleton
colours; the auxiliary fan hypothesis is invoked only on the smaller root piece. -/
theorem anchoredFan_extension_of_prescribed_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ rootStar I b, f x ∈ I.lists x)
    (hp : ∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (hbS : b ∈ S) (hbT : b ∉ T)
    (ha : ∃ a ∈ S, a ∈ I.precolor.vertices ∧ G.Adj b a)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ I.precolor.vertices)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (QS : BoundaryPrecolor (G.induce S))
    (hSv : ∀ x : S, x ∈ QS.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hSe : ∀ x y : S, s(x, y) ∈ QS.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (QT : BoundaryPrecolor (G.induce T))
    (hTv : ∀ x : T, x ∈ QT.vertices ↔ x.1 ∈ I.precolor.vertices)
    (hTe : ∀ x y : T, s(x, y) ∈ QT.edges ↔ s(x.1, y.1) ∈ I.precolor.edges)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

/-- A spoke cut meeting the prescription is handled recursively on its two
exact prescribed branches. No original singleton is released in this case. -/
theorem anchoredFan_extension_of_prescribed_spoke_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (hxP : x ∈ I.precolor.vertices) (hbx : G.Adj b x)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanCutsContracts

section AnchoredFanSpokesContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- Keep the old prescription in the root piece and solve the other spoke
piece by the complete two-endpoint fan theorem. -/
theorem anchoredFan_extension_of_one_sided_spoke (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hPS : ∀ y ∈ I.precolor.vertices, y ∈ S)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

/-- Every short-neighbour spoke is cut, whether or not it meets or divides
the old prescription. Both original path branches keep their singleton colours. -/
theorem anchoredFan_extension_of_spoke_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b x : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hbx : G.Adj b x) (hxs : (I.lists x).card ≤ 2)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {b, x})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

/-- A cut along an original prescribed edge is also a strict anchored-fan
reduction. The root piece retains an actual prescribed neighbour of the root. -/
theorem anchoredFan_extension_of_prescribed_edge_cut (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (r s : V) (hrs : G.Adj r s) (hrP : r ∈ I.precolor.vertices) (hsP : s ∈ I.precolor.vertices)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {r, s})
    (hedges : ∀ {y z}, G.Adj y z → (y ∈ S ∧ z ∈ S) ∨ (y ∈ T ∧ z ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanSpokesContracts

section AnchoredFanCutvertexContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- All cutvertices of the anchored fan are reduced. Prescribed cutvertices
keep exact old singleton colours, and unprescribed attachments use the complete
previous root-fan theorem on a genuinely smaller empty-prescription piece. -/
theorem anchoredFan_extension_of_cutvertex (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanCutvertexContracts

section AnchoredFanBaseContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance

/-- A prescribed path of at most two edges, attached at its endpoint, plus
one further short neighbour of the root is a native induced path of at most
five vertices. The girth and old short-edge conditions supply chordlessness. -/
theorem rootStar_extension_of_attached_short_path (I : BoundaryInstance G C)
    {a t : V} (p : G.Walk a t) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ p.support)
    (b : V) (hbP : b ∉ I.precolor.vertices) (hba : G.Adj b a)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hproper : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (x : V) (hbx : G.Adj b x) (hxa : x ≠ a)
    (hbound : ∀ y, G.Adj b y → (I.lists y).card ≤ 2 → y = a ∨ y = x)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanBaseContracts

section AnchoredFanBoundaryContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A cycle vertex has no third distinct neighbour in its cycle graph. -/
lemma cyclicSubgraph_third_neighbour {k : ℕ} {c : ZMod k → V} (hc : IsCycleMap G c)
    (i : ZMod k) {r s b : V} (hr : (cyclicSubgraph G c).Adj (c i) r)
    (hs : (cyclicSubgraph G c).Adj (c i) s) (hb : (cyclicSubgraph G c).Adj (c i) b)
    (hrs : r ≠ s) : b = r ∨ b = s := by
  sorry

/-- A vertex outside a short path cannot attach at its middle if all three
incident edges belong to the same facial cycle graph. -/
lemma short_facial_path_attachment_is_endpoint {k : ℕ} {c : ZMod k → V}
    (hc : IsCycleMap G c) {z w a b : V} (p : G.Walk z w) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (ha : a ∈ p.support) (hb : b ∉ p.support)
    (hba : (cyclicSubgraph G c).Adj b a)
    (hedges : ∀ x y, s(x,y) ∈ p.edges → (cyclicSubgraph G c).Adj x y)
    (harange : a ∈ Set.range c) : a = z ∨ a = w := by
  sorry

namespace BoundaryInstance
variable [Fintype V]

/-- Both kinds of relevant chords in an anchored fan have complete strict
cuts: root-to-short-neighbour spokes and edges of the old prescription. -/
lemma anchoredFan_adj_consecutive_of_strict_induction (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (hbad : ¬ RootStarExtension I b f)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) (i j : ZMod k)
    (hkind : (c i = b ∧ (I.lists (c j)).card ≤ 2) ∨
      (c i ∈ I.precolor.vertices ∧ c j ∈ I.precolor.vertices))
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  sorry

/-- With all relevant chords removed by strict cuts, the old prescription
and root fan form a bounded native path. This closes the normalized face step. -/
theorem anchoredFan_extension_of_facial_boundary (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ Set.range c) (hcb : c 0 = b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanBoundaryContracts

section AnchoredFanExtensionContracts
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance

/-- Fix the root fan while retaining up to three original prescribed vertices
adjacent to the root. A complete separate strong induction closes the auxiliary
problem; the main boundary-extension induction is used only below `N`. -/
theorem anchoredFan_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hPcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (hN : Nat.card V < N) : RootStarExtension I b f := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanExtensionContracts

section AnchoredFanChoiceContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- An external vertex has at most one neighbour on a native path of at most
two edges. Splitting at one neighbour reuses the checked endpoint lemma. -/
lemma external_short_path_neighbour_unique (hg : 5 ≤ G.egirth) {z w a b y : V}
    (p : G.Walk z w) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (ha : a ∈ p.support) (hb : b ∉ p.support) (hba : G.Adj b a)
    (hy : y ∈ p.support) (hby : G.Adj b y) : y = a := by
  sorry

namespace BoundaryInstance

/-- An allowed root colour avoiding its prescribed neighbours extends to all
old short neighbours, respecting their original singleton lists. -/
lemma exists_rootStar_colours_avoiding_precolor (I : BoundaryInstance G C)
    (b : V) (t : C) (ht : t ∈ I.lists b)
    (havoid : ∀ x ∈ I.precolor.vertices, G.Adj b x → I.prescribed x ≠ t) :
    ∃ f : V → C, f b = t ∧ (∀ x ∈ rootStar I b, f x ∈ I.lists x) ∧
      (∀ x ∈ rootStar I b, ∀ y ∈ rootStar I b, G.Adj x y → f x ≠ f y) := by
  sorry

end BoundaryInstance
end Thomassen

end AnchoredFanChoiceContracts

section CentralChordCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A mixed cut with at most three prescribed vertices in one piece is closed
by the complete anchored-fan theorem. The other piece supplies the actual
separator colour; all old prescribed colours are retained on both sides. -/
theorem colourable_of_mixed_two_edge_branch_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (_ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    {d : V} (q : G.Walk a d) (hq : q.length ≤ 2)
    (hcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every mixed edge cut is closed: a path on at most six vertices has a
branch of at most two edges at the prescribed separator vertex. -/
theorem colourable_of_mixed_prescription_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen

end CentralChordCutContracts

section BoundaryChordReductionContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- Every facial-boundary chord is closed for an arbitrary six-vertex native
prescribed path, including all three formerly open central branch splits. -/
theorem colourable_of_path_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- Every chord of the actual facial boundary is a complete strict-induction
case, for every permitted original prescription. No placement or short-neighbour
capture hypothesis is supplied. -/
theorem colourable_of_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

/-- In a smallest counterexample every edge between facial-boundary vertices
is an edge of that actual boundary cycle. -/
lemma boundary_adj_consecutive_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hi : OnOuterFace I.embedding I.outer (c i))
    (hj : OnOuterFace I.embedding I.outer (c j)) (hadj : G.Adj (c i) (c j)) :
    j = i + 1 ∨ i = j + 1 := by
  sorry

/-- The normalized native facial boundary of a smallest counterexample is
chordless in the whole graph, with the original boundary vertices and corners. -/
theorem minimal_counterexample_has_chordless_native_face_cycle (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.IsChordless ∧
        p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  sorry

end BoundaryInstance
end Thomassen

end BoundaryChordReductionContracts
