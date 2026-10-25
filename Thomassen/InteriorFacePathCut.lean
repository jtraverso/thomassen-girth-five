/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FacialPathSplice

/-! Strict actual cuts for a short path closing an original facial arc. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Every vertex of the actual full face cycle lies on its original selected
face. This transports the face-permutation orbit, not just the vertex range. -/
lemma native_facial_cycle_vertices_on_outer (M : PlaneMap G) (outer : G.Dart)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) :
    ∀ x ∈ p.support, OnOuterFace M outer x := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hArc : IsFacialCycleArc M (walk_isCycleMap p hp) := fun i _ _ => hface i (Set.mem_univ _)
  intro x hx
  have hxrange : x ∈ Set.range (walkCycleVertices p) := by rw [walkCycleVertices_range p hp]; exact hx
  obtain ⟨d, hd, hdx⟩ := cycle_arc_vertices_on_outer M (walk_isCycleMap p hp) hlen hArc x hxrange
  exact ⟨d, hroot.trans hd, hdx⟩

/-- An interior closing path meets the original facial cycle only at its
specified two endpoints. No disjointness witness is supplied separately. -/
lemma closing_path_intersection_of_interior (M : PlaneMap G) (outer : G.Dart)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n := by
  intro x hxq hxp
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hxq
  by_cases hi0 : i = 0
  · right
    simpa only [hi0, Walk.getVert_zero] using hix.symm
  · by_cases hil : i = q.length
    · left
      simpa only [hil, Walk.getVert_length] using hix.symm
    · have hf := native_facial_cycle_vertices_on_outer M outer p hp hface hroot x hxp
      exact (hInner i (by omega) (by omega) (hix ▸ hf)).elim

variable [Fintype V]

/-- An original facial prefix closed by a one/two/three-edge interior path
has an actual strict induced cut. All spliced corners, face roots, nonempty
complement witnesses and path-support identifications are proved internally. -/
theorem interior_face_path_cut (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ q.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∀ x, x ∈ (p.take n).support ∨ x ∈ q.support → x ∈ S) ∧
      (∀ x, OnOuterFace M outer x → x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2) → x ∈ T) ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ (p.take n).support ∨ x.1 ∈ q.support) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) := by
  have hmeet := closing_path_intersection_of_interior M outer p hp hface hroot n q hInner
  let r := spliceFacePath p n q
  let hr := spliceFacePath_isCycle p hp n q hq hn (by omega) hmeet
  have hArc := spliceFacePath_isFacialAlong M p hp hface n q hq hn (by omega) hqpos hmeet
  have hrroot : SameCycle M.facePerm outer (walkArcRoot r hr) := by
    rw [spliceFacePath_root p hp n q hq hn (by omega) hmeet]
    exact hroot
  have houtside : ∃ x, OnOuterFace M outer x ∧ x ∉ r.support := by
    exact ⟨p.getVert (n + 1), native_facial_cycle_vertices_on_outer M outer p hp hface hroot _ (p.getVert_mem_support _),
      spliceFacePath_misses_next_vertex p hp n q hn hnp hmeet⟩
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc, hSC, hkeep, hSface, hTface⟩ :=
    native_short_arc_path_cut M outer hg hconn r hr n q.length hn hqpos hqshort
      (spliceFacePath_length p n q (by omega)) hArc hrroot houtside
  have hdrop := spliceFacePath_drop_support p n q (by omega : n ≤ p.length)
  have hrverts : ∀ x, x ∈ r.support ↔ x ∈ (p.take n).support ∨ x ∈ q.support := fun _ => Walk.mem_support_append_iff (p.take n) q
  refine ⟨S, T, hSsmall, hTsmall, hcover, ?_, hedges, hSc, hTc, ?_, ?_, ?_, ?_⟩
  · rw [hinter]
    ext x
    exact hdrop x
  · intro x hx
    exact hSC x ((hrverts x).2 hx)
  · intro x hx hxArc
    apply hkeep x hx
    rwa [spliceFacePath_arc p n q hn (by omega)]
  · obtain ⟨o, ho⟩ := hSface
    exact ⟨o, fun x => (ho x).trans (hrverts x.1)⟩
  · obtain ⟨N, o, ho⟩ := hTface
    refine ⟨N, o, ?_⟩
    intro x hx
    apply ho x
    exact hx.imp_right (fun h => (hdrop x.1).2 h)

end Thomassen
