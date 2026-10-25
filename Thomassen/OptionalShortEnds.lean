/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorFacePathCut

/-! Optional endpoint short neighbours on separators of at most two edges. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- One additional short neighbour suffices for a separator of at most two
edges. No short-list hypothesis is needed at the other endpoint. -/
theorem colourable_of_two_path_one_short_end (I : BoundaryInstance G C)
    (S T : Set V) {a b x : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqlen : q.length ≤ 2) (hxa : G.Adj x a) (hxq : x ∉ q.support)
    (hxS : x ∈ S) (hxs : (I.lists x).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTc : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x → OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z → 3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → (I.lists z).card ≤ 2 → ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let r := Walk.cons hxa q
  have hr : r.IsPath := Walk.IsPath.mk' (List.nodup_cons.2 ⟨hxq, hq.support_nodup⟩)
  have hlen : r.length ≤ 3 := by simp only [r, Walk.length_cons]; omega
  apply I.colourable_of_augmented_short_path_cut S T q hq hqpos r hr (by omega)
    (short_path_isChordless I.girth r hr hlen)
    (fun _ hz => List.mem_cons_of_mem _ hz) ?_ ?_ ?_ hcover hinter hedges hTc hP oS ?_ hInterior ?_ hSsmall hTsmall hsmall
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hxS
    · have h : z ∈ S ∩ T := by rwa [hinter]
      exact h.1
  · intro z hz hzq
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hxs
    · exact (hzq hz).elim
  · intro z hz hzq
    have hzx : z = x := (List.mem_cons.1 hz).resolve_right hzq
    subst z
    exact ⟨a, q.start_mem_support, short_path_endpoint_neighbour_unique I.girth q hq hqlen hxq hxa⟩
  · intro z hz
    exact hface z ((List.mem_cons.1 hz).elim (fun h => Or.inr h) Or.inl)
  · intro z hzS hzr hzs w hw
    have hzq : z ∉ q.support := fun h => hzr (List.mem_cons_of_mem _ h)
    have hzx : z ≠ x := fun h => hzr (by simp only [r, Walk.support_cons, List.mem_cons]; exact Or.inl h)
    exact hCapture z hzS hzq hzx hzs w hw

/-- Every combination of zero, one or two endpoint short neighbours is
handled. Neighbours whose original list is longer are left unprescribed. -/
theorem colourable_of_two_path_optional_short_ends (I : BoundaryInstance G C)
    (S T : Set V) {a b x y : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqlen : q.length ≤ 2)
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxq : x ∉ q.support) (hyq : y ∉ q.support)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTc : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x ∨ z.1 = y → OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z → 3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hxs : (I.lists x).card ≤ 2 <;> by_cases hys : (I.lists y).card ≤ 2
  · exact I.colourable_of_short_path_with_two_short_ends S T q hq hqpos hqlen hxa hby hxq hyq hxS hyS hxs hys
      hcover hinter hedges hTc hP oS hface hInterior hCapture hSsmall hTsmall hsmall
  · apply I.colourable_of_two_path_one_short_end S T q hq hqpos hqlen hxa hxq hxS hxs hcover hinter hedges hTc hP oS
      (fun z hz => hface z (hz.imp_right Or.inl)) hInterior ?_ hSsmall hTsmall hsmall
    intro z hzS hzq hzx hzs w hw
    exact hCapture z hzS hzq hzx (fun h => hys (h ▸ hzs)) hzs w hw
  · apply I.colourable_of_two_path_one_short_end S T q.reverse hq.reverse
      (by simpa only [Walk.length_reverse] using hqpos) (by simpa only [Walk.length_reverse] using hqlen)
      hby.symm (by simpa only [Walk.support_reverse, List.mem_reverse] using hyq) hyS hys
      hcover (by simpa only [Walk.support_reverse, List.mem_reverse] using hinter) hedges hTc hP oS ?_ hInterior ?_ hSsmall hTsmall hsmall
    · intro z hz
      apply hface z
      simpa only [Walk.support_reverse, List.mem_reverse] using hz.imp_right Or.inr
    · intro z hzS hzq hzy hzs w hw
      have hzq' : z ∉ q.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hzq
      have hw' : w ∈ q.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hw
      exact hCapture z hzS hzq' (fun h => hxs (h ▸ hzs)) hzy hzs w hw'
  · apply I.colourable_of_short_path_without_short_neighbours S T q hq hqpos (by omega) hcover hinter hedges hTc hP oS
      (fun z hz => hface z (Or.inl hz)) hInterior ?_ hSsmall hTsmall hsmall
    intro z hzS hzq hzs w hw
    exact hCapture z hzS hzq (fun h => hxs (h ▸ hzs)) (fun h => hys (h ▸ hzs)) hzs w hw

end Thomassen.BoundaryInstance
