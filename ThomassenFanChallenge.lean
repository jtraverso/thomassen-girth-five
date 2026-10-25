/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AugmentedPathColouring
public import Thomassen.FaceOrbitCycle
public import Thomassen.InteriorCutReduction
public import Thomassen.EdgeCutReduction
public import Thomassen.FacialSixReduction

/-! Independent contracts for complete cutvertex normalization and its auxiliary
root-star induction. None of the nine new proof modules is imported. The main
boundary-extension induction is required only at strictly smaller cardinalities.
The unconditional main theorem is not asserted. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section BoundaryChordCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V}
def prefixCycleVertex (c : ZMod k → V) (j : ℕ) : ZMod (j + 1) → V :=
  fun i => c (i.val : ZMod k)

omit [NeZero k] in
lemma prefixCycleVertex_zero (j : ℕ) : prefixCycleVertex c j 0 = c 0 := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_last (j : ℕ) : prefixCycleVertex c j (-1) = c (j : ZMod k) := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_injective (hc : IsCycleMap G c) (j : ℕ) (hj : j < k) :
    Function.Injective (prefixCycleVertex c j) := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_next (j : ℕ) (hj : 1 ≤ j) (i : ZMod (j + 1))
    (hi : i.val < j) : prefixCycleVertex c j (i + 1) = c ((i.val : ZMod k) + 1) := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_prev (j : ℕ) (i : ZMod (j + 1)) (hi : 0 < i.val) :
    prefixCycleVertex c j (i - 1) = c ((i.val : ZMod k) - 1) := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_isCycleMap (hc : IsCycleMap G c) (j : ℕ)
    (hj : 2 ≤ j) (hjk : j < k) (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    IsCycleMap G (prefixCycleVertex c j) := by
  sorry

omit [NeZero k] in
lemma prefixCycleVertex_isFacialArc (M : PlaneMap G) (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) (j : ℕ) (hj : 2 ≤ j) (hjk : j < k)
    (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    IsFacialCycleArc M (prefixCycleVertex_isCycleMap hc j hj hjk hchord) := by
  sorry

variable [instFT : Fintype V]
include instFT
omit [NeZero k] in
theorem full_face_chord_separation (M : PlaneMap G) (hc : IsCycleMap G c) (_hk : 3 ≤ k)
    (hface : IsFacialCycleAlong M hc Set.univ) (hG : G.Preconnected)
    (j : ℕ) (hj : 2 ≤ j) (hjk : j + 2 ≤ k) (hchord : G.Adj (c (j : ZMod k)) (c 0)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {c 0, c (j : ZMod k)} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 →
          OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M (toDart cyclicSubgraph_le (cycleForward hc 0)) x.1 →
          OnOuterFace (inducedPlaneMap M T) o x) := by
  sorry

end Thomassen
end BoundaryChordCutContracts

section CutSidePairContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {w : V} {S : Set V}
lemma cut_side_pair_properties (hw : w ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S)) :
    S ∪ insert w Sᶜ = Set.univ ∧ S ∩ insert w Sᶜ = {w} ∧
    (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ insert w Sᶜ ∧ y ∈ insert w Sᶜ)) ∧
    (∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ insert w Sᶜ ↔ y ∈ insert w Sᶜ)) := by
  sorry

lemma exists_cut_side_containing (w v : V)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, w ∈ S ∧ v ∈ S ∧ (∃ a ∈ S, a ≠ w) ∧ (∃ b, b ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S) := by
  sorry

end Thomassen
end CutSidePairContracts

section RootStarContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
def rootStar (I : BoundaryInstance G C) (v : V) : Set V :=
  {x | x = v ∨ G.Adj v x ∧ (I.lists x).card ≤ 2}

def RootStarExtension (I : BoundaryInstance G C) (v : V) (f : V → C) : Prop :=
  ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ ∀ x ∈ rootStar I v, c x = f x

namespace BoundaryInstance
lemma exists_rootStar_colours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (t : C) (ht : t ∈ I.lists v) :
    ∃ f : V → C, f v = t ∧ (∀ x ∈ rootStar I v, f x ∈ I.lists x) ∧
      (∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y) := by
  sorry

theorem rootStar_extension_of_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hqlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ rootStar I v)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : RootStarExtension I v f := by
  sorry

variable [instFin : Finite V]
include instFin
theorem rootStar_extension_of_two_neighbours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (l r : V) (hl : G.Adj v l) (hr : G.Adj v r) (hlr : l ≠ r)
    (hbound : ∀ z, G.Adj v z → (I.lists z).card ≤ 2 → z = l ∨ z = r)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) : RootStarExtension I v f := by
  sorry

end BoundaryInstance
end Thomassen
end RootStarContracts

section RootStarCutsContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT
namespace BoundaryInstance
lemma induceUnprecolored_on_old_face (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (hP : ∀ x ∈ S, x ∉ I.precolor.vertices)
    (x : S) (hx : OnOuterFace I.embedding I.outer x.1) :
    OnOuterFace (I.induceUnprecolored S hconn hP).embedding
      (I.induceUnprecolored S hconn hP).outer x := by
  sorry

omit [Fintype V] in
lemma rootStar_extension_of_induced_colourings (I : BoundaryInstance G C) (v : V) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (S T : Set V) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x : S, cS x ∈ I.lists x.1) (hcT : ∀ x : T, cT x ∈ I.lists x.1)
    (hstarS : ∀ x : S, x.1 ∈ rootStar I v → cS x = f x.1)
    (hstarT : ∀ x : T, x.1 ∈ rootStar I v → cT x = f x.1)
    (hagree : ∀ x (hx : x ∈ S) (hy : x ∈ T), cS ⟨x, hx⟩ = cT ⟨x, hy⟩) :
    RootStarExtension I v f := by
  sorry

theorem rootStar_extension_of_star_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (hvS : v ∈ S) (hvT : v ∈ T)
    (hcover : S ∪ T = Set.univ)
    (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I v)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  sorry

lemma exists_empty_cut_instance_with_root (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (T : Set V) [Nontrivial T] (hconn : (G.induce T).Preconnected) (w : T)
    (hboundary : OnOuterFace I.embedding I.outer w.1 ∨ ∀ x : T, 3 ≤ (I.lists x.1).card) :
    ∃ J : BoundaryInstance (G.induce T) C, J.precolor = .empty ∧
      (∀ x : T, J.lists x = I.lists x.1) ∧ OnOuterFace J.embedding J.outer w := by
  sorry

theorem rootStar_extension_of_root_side_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (hvS : v ∈ S) (hstarS : ∀ x ∈ rootStar I v, x ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  sorry

theorem rootStar_extension_of_cutvertex (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (v : V) (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I v f := by
  sorry

end BoundaryInstance
end Thomassen
end RootStarCutsContracts

section RootStarFanContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT
namespace BoundaryInstance
theorem rootStar_extension_of_facial_chord (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hv : OnOuterFace I.embedding I.outer (c 0)) (f : V → C)
    (hf : ∀ x ∈ rootStar I (c 0), f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I (c 0), ∀ y ∈ rootStar I (c 0), G.Adj x y → f x ≠ f y)
    (j : ℕ) (hj : 2 ≤ j) (hjk : j + 2 ≤ k) (hchord : G.Adj (c (j : ZMod k)) (c 0))
    (hshort : (I.lists (c (j : ZMod k))).card ≤ 2)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I (c 0) f := by
  sorry

theorem rootStar_extension_of_facial_boundary (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c)
    (hv : OnOuterFace I.embedding I.outer (c 0)) (f : V → C)
    (hf : ∀ x ∈ rootStar I (c 0), f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I (c 0), ∀ y ∈ rootStar I (c 0), G.Adj x y → f x ≠ f y)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hroot : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (w : W), OnOuterFace J.embedding J.outer w → ∀ g : W → C,
      (∀ x ∈ rootStar J w, g x ∈ J.lists x) →
      (∀ x ∈ rootStar J w, ∀ y ∈ rootStar J w, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → RootStarExtension J w g) : RootStarExtension I (c 0) f := by
  sorry

end BoundaryInstance
end Thomassen
end RootStarFanContracts

section RootStarExtensionContracts
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance
theorem rootStar_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected) (v : V)
    (hv : OnOuterFace I.embedding I.outer v) (f : V → C)
    (hf : ∀ x ∈ rootStar I v, f x ∈ I.lists x)
    (hproper : ∀ x ∈ rootStar I v, ∀ y ∈ rootStar I v, G.Adj x y → f x ≠ f y)
    (hN : Nat.card V < N) : RootStarExtension I v f := by
  sorry

end BoundaryInstance
end Thomassen
end RootStarExtensionContracts

section BoundaryCutReductionContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
lemma BoundaryPrecolor.cut_side_dichotomy_avoiding (P : BoundaryPrecolor G) {w : V}
    (hw : w ∉ P.vertices) (S : Set V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S)) :
    (∀ x ∈ P.vertices, x ∈ S) ∨ (∀ x ∈ P.vertices, x ∉ S) := by
  sorry

namespace BoundaryInstance
variable [instFT : Fintype V]
include instFT
theorem colourable_of_unprescribed_boundary_cut_piece (I : BoundaryInstance G C)
    (hG : G.Preconnected) (w : V) (hwface : OnOuterFace I.embedding I.outer w)
    (S : Set V) (hwS : w ∈ S) (hleft : ∃ a ∈ S, a ≠ w) (hright : ∃ b, b ∉ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S))
    (hNoP : ∀ x ∈ S, x ∉ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_unprescribed_boundary_cutvertex (I : BoundaryInstance G C)
    (hG : G.Preconnected) (w : V) (hw : w ∉ I.precolor.vertices)
    (hwface : OnOuterFace I.embedding I.outer w)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_cutvertex (I : BoundaryInstance G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

lemma delete_preconnected_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected := by
  sorry

lemma colourable_of_card_le_two (I : BoundaryInstance G C) (hcard : Nat.card V ≤ 2)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem minimal_counterexample_has_native_face_cycle (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    G.Preconnected ∧ 3 ≤ Nat.card V ∧ (∀ w, (G.induce ({w} : Set V)ᶜ).Preconnected) ∧
      ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength I.embedding I.outer ∧
        (∀ x, x ∈ p.support ↔ OnOuterFace I.embedding I.outer x) ∧
        IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = I.outer := by
  sorry

end BoundaryInstance
end Thomassen
end BoundaryCutReductionContracts

section FacialChordNormalizationContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {k : ℕ} [NeZero k] {c : ZMod k → V} [instFT : Fintype V]
include instFT
theorem full_face_chord_separation_at (M : PlaneMap G) (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong M hc Set.univ) (hG : G.Preconnected)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {c i, c j} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected := by
  sorry

namespace BoundaryInstance
variable {C : Type v}
theorem colourable_of_prescribed_boundary_chord (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hG : G.Preconnected) (i j : ZMod k) (hadj : G.Adj (c i) (c j))
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∈ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

lemma prescribed_adj_consecutive_of_minimal_counterexample (I : BoundaryInstance G C)
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hG : G.Preconnected) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∈ I.precolor.vertices)
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  sorry

end BoundaryInstance
end Thomassen
end FacialChordNormalizationContracts

section PrescribedCycleNormalizationContracts
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}
lemma cyclicSubgraph_adj_at_iff {k : ℕ} {c : ZMod k → V} (hc : IsCycleMap G c)
    (i : ZMod k) (y : V) :
    (cyclicSubgraph G c).Adj (c i) y ↔ y = c (i + 1) ∨ y = c (i - 1) := by
  sorry

lemma cycle_range_eq_of_cycle_edges {k l : ℕ} [NeZero k] [NeZero l]
    {c : ZMod k → V} {d : ZMod l → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d)
    (hl : 3 ≤ l) (hsub : Set.range d ⊆ Set.range c)
    (hedges : ∀ i : ZMod l, (cyclicSubgraph G c).Adj (d i) (d (i + 1))) :
    Set.range d = Set.range c := by
  sorry

namespace BoundaryInstance
variable {C : Type v} [instFT : Fintype V]
include instFT
theorem colourable_of_prescribed_cycle (I : BoundaryInstance G C)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hbound : p.support.toFinset.card ≤ 6)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
end PrescribedCycleNormalizationContracts
