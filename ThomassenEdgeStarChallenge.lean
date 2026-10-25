/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.RootStarExtension
public import Thomassen.FacialChordNormalization
public import Thomassen.PrescribedCycleNormalization

/-! Independent contracts for two-endpoint fan extension and boundary chord cuts.
None of the eleven new proof modules is imported. The auxiliary fan induction
uses the main induction only below its explicit strict cardinality bound.
Mixed chords splitting the prescribed path and the main theorem remain open. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v

section EdgeStarContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
def edgeStar (I : BoundaryInstance G C) (a b : V) : Set V := rootStar I a ∪ rootStar I b

def EdgeStarExtension (I : BoundaryInstance G C) (a b : V) (f : V → C) : Prop :=
  ∃ c : G.Coloring C, (∀ x, c x ∈ I.lists x) ∧ ∀ x ∈ edgeStar I a b, c x = f x

namespace BoundaryInstance
theorem edgeStar_extension_of_path (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    {s t : V} (q : G.Walk s t) (hq : q.IsPath) (hqlen : q.length ≤ 5) (hch : q.IsChordless)
    (hexact : ∀ x, x ∈ q.support ↔ x ∈ edgeStar I a b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) [Finite V] : EdgeStarExtension I a b f := by
  sorry

variable [instFin : Finite V]
include instFin
theorem edgeStar_extension_of_two_neighbours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (l r : V) (hab : G.Adj a b) (hal : G.Adj a l) (hbr : G.Adj b r)
    (hlb : l ≠ b) (hra : r ≠ a) (hlr : l ≠ r)
    (hboundA : ∀ z, G.Adj a z → (I.lists z).card ≤ 2 → z = b ∨ z = l)
    (hboundB : ∀ z, G.Adj b z → (I.lists z).card ≤ 2 → z = a ∨ z = r)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarContracts

section EdgeStarCutsContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT
namespace BoundaryInstance
omit [Fintype V] in
lemma edgeStar_extension_of_induced_colourings (I : BoundaryInstance G C) (a b : V) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (S T : Set V) (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (cS : (G.induce S).Coloring C) (cT : (G.induce T).Coloring C)
    (hcS : ∀ x : S, cS x ∈ I.lists x.1) (hcT : ∀ x : T, cT x ∈ I.lists x.1)
    (hstarS : ∀ x : S, x.1 ∈ edgeStar I a b → cS x = f x.1)
    (hstarT : ∀ x : T, x.1 ∈ edgeStar I a b → cT x = f x.1)
    (hagree : ∀ x (hx : x ∈ S) (hy : x ∈ T), cS ⟨x, hx⟩ = cT ⟨x, hy⟩) :
    EdgeStarExtension I a b f := by
  sorry

lemma edgeStar_colouring_on_smaller_induced (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S : Set V) [Nontrivial S] (haS : a ∈ S) (hbS : b ∈ S)
    (hconn : (G.induce S).Preconnected) (hSsmall : Nat.card S < Nat.card V)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ edgeStar I a b → c x = f x.1 := by
  sorry

theorem edgeStar_extension_of_edge_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (haS : a ∈ S) (hbS : b ∈ S) (haT : a ∈ T) (hbT : b ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ edgeStar I a b)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

theorem edgeStar_extension_of_root_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (haS : a ∈ S) (hbS : b ∈ S) (r : V) (hr : OnOuterFace I.embedding I.outer r)
    (hrT : r ∈ T) (hrootSub : ∀ x ∈ rootStar I r, x ∈ edgeStar I a b)
    (hcover : S ∪ T = Set.univ) (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I r)
    (hstarT : ∀ x ∈ T, x ∈ edgeStar I a b → x ∈ rootStar I r)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

theorem edgeStar_extension_of_separate_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (haS : a ∈ S) (hbS : b ∈ S) (hstarS : ∀ x ∈ edgeStar I a b, x ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSconn : (G.induce S).Preconnected) (hTconn : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarCutsContracts

section EdgeStarCutvertexContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
lemma exists_cut_side_containing_edge (w a b : V) (hab : G.Adj a b)
    (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected) :
    ∃ S : Set V, w ∈ S ∧ a ∈ S ∧ b ∈ S ∧ (∃ x ∈ S, x ≠ w) ∧ (∃ y, y ∉ S) ∧
      ∀ {x y}, G.Adj x y → x ≠ w → y ≠ w → (x ∈ S ↔ y ∈ S) := by
  sorry

lemma edgeStar_other_side_subset_rootStar (I : BoundaryInstance G C) (a b r : V)
    (S T : Set V) (har : a = r ∨ a ∉ T) (hbr : b = r ∨ b ∉ T)
    (hinter : ∀ x ∈ S ∩ T, x ∈ rootStar I r)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) :
    ∀ x ∈ T, x ∈ edgeStar I a b → x ∈ rootStar I r := by
  sorry

namespace BoundaryInstance
variable [instFT : Fintype V]
include instFT
theorem edgeStar_extension_of_cutvertex (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarCutvertexContracts

section EdgeStarSpokeContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT
namespace BoundaryInstance
theorem edgeStar_extension_of_spoke_cut (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (r x : V) (hr : r = a ∨ r = b) (hrx : G.Adj r x)
    (hx : x = a ∨ x = b ∨ (I.lists x).card ≤ 2)
    (S T : Set V) (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {r, x})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarSpokeContracts

section EdgeStarBoundaryContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT
namespace BoundaryInstance
lemma edgeStar_adj_consecutive_of_strict_induction (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (hbad : ¬ EdgeStarExtension I a b f)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) (i j : ZMod k) (hiroot : c i = a ∨ c i = b)
    (hjroot : c j = a ∨ c j = b ∨ (I.lists (c j)).card ≤ 2)
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  sorry

theorem edgeStar_extension_of_facial_boundary (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (hG : G.Preconnected) (a b : V) (hab : G.Adj a b) (ha : OnOuterFace I.embedding I.outer a)
    (hb : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ x, OnOuterFace I.embedding I.outer x → x ∈ Set.range c) (hca : c 0 = a)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hedge : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      J.precolor = .empty → H.Preconnected → ∀ (a b : W), H.Adj a b →
      OnOuterFace J.embedding J.outer a → OnOuterFace J.embedding J.outer b → ∀ g : W → C,
      (∀ x ∈ edgeStar J a b, g x ∈ J.lists x) →
      (∀ x ∈ edgeStar J a b, ∀ y ∈ edgeStar J a b, H.Adj x y → g x ≠ g y) →
      Nat.card W < Nat.card V → EdgeStarExtension J a b g) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarBoundaryContracts

section EdgeStarExtensionContracts
namespace Thomassen
open Classical
variable {C : Type v}
namespace BoundaryInstance
theorem edgeStar_extension_of_smaller (N : ℕ)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    {V : Type u} [Finite V] {G : SimpleGraph V} (I : BoundaryInstance G C)
    (hP : I.precolor = .empty) (hG : G.Preconnected) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (f : V → C) (hf : ∀ x ∈ edgeStar I a b, f x ∈ I.lists x)
    (hproper : ∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y)
    (hN : Nat.card V < N) : EdgeStarExtension I a b f := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarExtensionContracts

section EdgeStarChoiceContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace BoundaryInstance
lemma exists_edgeStar_colours (I : BoundaryInstance G C) (hP : I.precolor = .empty)
    (a b : V) (hab : G.Adj a b) (ta tb : C) (hta : ta ∈ I.lists a) (htb : tb ∈ I.lists b)
    (htab : ta ≠ tb) :
    ∃ f : V → C, f a = ta ∧ f b = tb ∧ (∀ x ∈ edgeStar I a b, f x ∈ I.lists x) ∧
      (∀ x ∈ edgeStar I a b, ∀ y ∈ edgeStar I a b, G.Adj x y → f x ≠ f y) := by
  sorry

end BoundaryInstance
end Thomassen
end EdgeStarChoiceContracts

section ReleasedEdgeContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT
namespace BoundaryInstance
lemma exists_empty_induced_releasing_edge (I : BoundaryInstance G C) (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) (a b : V) (haS : a ∈ S) (hbS : b ∈ S)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b)
    (F : Finset C) (hF : 3 ≤ F.card) :
    ∃ J : BoundaryInstance (G.induce S) C, J.precolor = .empty ∧
      (∀ x : S, x.1 ≠ a → x.1 ≠ b → J.lists x = I.lists x.1) ∧
      (∀ x : S, I.lists x.1 ⊆ J.lists x) ∧
      OnOuterFace J.embedding J.outer ⟨a, haS⟩ ∧ OnOuterFace J.embedding J.outer ⟨b, hbS⟩ := by
  sorry

end BoundaryInstance
end Thomassen
end ReleasedEdgeContracts

section UnprescribedEdgeCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable [instFT : Fintype V]
include instFT
namespace BoundaryInstance
theorem colourable_of_edge_cut_with_one_sided_prescription (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hPcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x = a ∨ x = b)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
end UnprescribedEdgeCutContracts

section UnprescribedBoundaryChordContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
lemma walk_side_of_avoids_two_cut {a b : V} {S : Set V}
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    {s t : V} (p : G.Walk s t) (ha : a ∉ p.support) (hb : b ∉ p.support) :
    ∀ x ∈ p.support, x ∈ S ↔ s ∈ S := by
  sorry

lemma BoundaryPrecolor.edge_cut_dichotomy_avoiding (P : BoundaryPrecolor G) (a b : V)
    (ha : a ∉ P.vertices) (hb : b ∉ P.vertices) (S : Set V)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S)) :
    (∀ x ∈ P.vertices, x ∈ S) ∨ (∀ x ∈ P.vertices, x ∉ S) := by
  sorry

namespace BoundaryInstance
variable [instFT : Fintype V]
include instFT
theorem colourable_of_unprescribed_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∉ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_unprescribed_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∉ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

lemma boundary_chord_exactly_one_prescribed_end (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j)) :
    (c i ∈ I.precolor.vertices ∧ c j ∉ I.precolor.vertices) ∨
      (c i ∉ I.precolor.vertices ∧ c j ∈ I.precolor.vertices) := by
  sorry

end BoundaryInstance
end Thomassen
end UnprescribedBoundaryChordContracts

section EndpointChordCutContracts
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
lemma path_side_dichotomy_avoiding_other_separator {a b t : V} {S : Set V} (haS : a ∈ S)
    (hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S))
    (p : G.Walk a t) (hp : p.IsPath) (hb : b ∉ p.support) :
    (∀ x ∈ p.support, x ∈ S) ∨ (∀ x ∈ p.support, x ∈ S ↔ x = a) := by
  sorry

namespace BoundaryInstance
variable [instFT : Fintype V]
include instFT
theorem colourable_of_path_endpoint_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b t : V} (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (hbP : b ∉ I.precolor.vertices) (p : G.Walk a t) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

theorem colourable_of_path_endpoint_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hjP : c j ∉ I.precolor.vertices) {t : V} (p : G.Walk (c i) t) (hp : p.IsPath)
    (hP : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry

end BoundaryInstance
end Thomassen
end EndpointChordCutContracts
