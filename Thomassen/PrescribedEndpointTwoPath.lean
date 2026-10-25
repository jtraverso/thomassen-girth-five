/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorThreePathReduction

/-! Interior two-paths at an endpoint of the original prescribed path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A smallest counterexample has no interior two-edge path from a prescribed
endpoint to a distinct boundary vertex outside the open prescribed path. This
also covers the other prescribed endpoint. One old arc is proved prescription-
free from the exact orientation of the original path. -/
theorem no_interior_two_path_from_prescribed_endpoint_to_noninternal_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hya : y ≠ a)
    (hyInternal : ∀ k, 0 < k → k < r.length → r.getVert k ≠ y)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hc := walk_isCycleMap p hp
  have hrange : ∀ z, OnOuterFace I.embedding I.outer z → z ∈ Set.range (walkCycleVertices p) := by
    intro z hz
    rw [walkCycleVertices_range p hp]
    exact hExact z hz
  obtain ⟨j, hj⟩ := hrange y hy
  let n := j.val
  have hnk : n < p.length := ZMod.val_lt j
  have hny : p.getVert n = y := hj
  have hxpn : G.Adj x (p.getVert n) := by rwa [hny]
  have hn0 : n ≠ 0 := by
    intro hn
    have hay : a = y := by simpa only [hn, Walk.getVert_zero] using hny
    exact hya hay.symm
  have hn1 : n ≠ 1 := by
    intro hn
    have h1 : G.Adj x (p.getVert 1) := by simpa only [hn] using hxpn
    exact neighbors_nonadjacent I.girth hxa h1 (by
      simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length))
  have hnlast : n ≠ p.length - 1 := by
    intro hn
    have hna : G.Adj (p.getVert n) a := by
      rw [hn]
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length), Walk.getVert_length] using
        p.adj_getVert_succ (by omega : p.length - 1 < p.length)
    exact neighbors_nonadjacent I.girth hxa hxpn hna.symm
  have hn : 2 ≤ n := by omega
  have hnp : n + 2 ≤ p.length := by omega
  obtain ⟨i, e, he, horder⟩ := I.prescribed_path_follows_facial_cycle hc hlen hface hrange hG hbad hsmall r hr hP
  have hzero : walkCycleVertices p 0 = a := by simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hstart : a = walkCycleVertices p i := by simpa only [Walk.getVert_zero, Nat.cast_zero, zero_mul, add_zero] using horder 0 (Nat.zero_le _)
  have hi0 : i = 0 := hc.inj (hstart.symm.trans hzero.symm)
  subst i
  have hrorder : ∀ k ≤ r.length, r.getVert k = walkCycleVertices p ((k : ZMod p.length) * e) := by
    simpa only [zero_add] using horder
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  rcases he with rfl | rfl
  · have hrlen : r.length ≤ n := by
      by_contra h
      have hnlt : n < r.length := by omega
      have hnle : n ≤ r.length := by omega
      have hry : r.getVert n = y := by
        rw [hrorder n hnle, mul_one, walkCycleVertices_nat_le p (by omega)]
        exact hny
      exact hyInternal n (by omega) hnlt hry
    obtain ⟨q, hq, hqlen, hqo, hqface, hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot n hnk
    have hqa : q.getVert (p.length - n) = a := by
      rw [hqo (p.length - n) (by omega), Nat.add_sub_of_le (by omega : n ≤ p.length), ZMod.natCast_self]
      exact hzero
    have hqch := I.native_face_cycle_chordless_of_minimal_counterexample hG q hq hqface hqroot hbad hsmall
    have hPfree : ∀ z ∈ I.precolor.vertices, z ∉ cycleInterval (walkCycleVertices q) 1 (p.length - n - 2) := by
      intro z hzP hzArc
      obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.1 ((hP z).1 hzP)
      obtain ⟨l, hl, hlz⟩ := hzArc
      have hlz' : walkCycleVertices p ((n + (1 + l) : ℕ) : ZMod p.length) = z := by
        rwa [walkCycleVertices_nat_le q (by omega : 1 + l ≤ q.length), hqo (1 + l) (by omega)] at hlz
      have heq : walkCycleVertices p (k : ZMod p.length) = walkCycleVertices p ((n + (1 + l) : ℕ) : ZMod p.length) := by
        calc
          _ = r.getVert k := by simpa only [mul_one] using (hrorder k hk).symm
          _ = z := hkz
          _ = _ := hlz'.symm
      have hval := congrArg ZMod.val (hc.inj heq)
      rw [ZMod.val_natCast_of_lt (by omega : k < p.length), ZMod.val_natCast_of_lt (by omega : n + (1 + l) < p.length)] at hval
      omega
    exact hbad (I.colourable_of_interior_two_path_free_arc hG q hq hqch hqface hqroot (p.length - n) (by omega) (by omega)
      x hx hxpn (by rwa [hqa]) hPfree hsmall)
  · have hrlen : n + r.length ≤ p.length := by
      by_contra h
      have hnlt : p.length - n < r.length := by omega
      have hnle : p.length - n ≤ r.length := by omega
      have hry : r.getVert (p.length - n) = y := by
        rw [hrorder (p.length - n) hnle, mul_neg_one, Nat.cast_sub (by omega : n ≤ p.length), ZMod.natCast_self,
          zero_sub, neg_neg, walkCycleVertices_nat_le p (by omega)]
        exact hny
      exact hyInternal (p.length - n) (by omega) hnlt hry
    have hPfree : ∀ z ∈ I.precolor.vertices, z ∉ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
      intro z hzP hzArc
      obtain ⟨k, hkz, hk⟩ := Walk.mem_support_iff_exists_getVert.1 ((hP z).1 hzP)
      obtain ⟨l, hl, hlz⟩ := hzArc
      have heq : walkCycleVertices p (-(k : ZMod p.length)) = walkCycleVertices p ((1 + l : ℕ) : ZMod p.length) := by
        calc
          _ = r.getVert k := by simpa only [mul_neg_one] using (hrorder k hk).symm
          _ = z := hkz
          _ = _ := hlz.symm
      have hzmod : ((k + (1 + l) : ℕ) : ZMod p.length) = 0 := by
        push_cast
        have he := hc.inj heq
        push_cast at he
        linear_combination -he
      have hdvd : p.length ∣ k + (1 + l) := (ZMod.natCast_eq_zero_iff _ _).1 hzmod
      have hbound := Nat.le_of_dvd (by omega : 0 < k + (1 + l)) hdvd
      omega
    exact hbad (I.colourable_of_interior_two_path_free_arc hG p hp hch hface hroot n hn hnp x hx hxa hxpn hPfree hsmall)


/-- In particular the endpoint cannot have an interior two-path to an
unprescribed boundary vertex. -/
theorem no_interior_two_path_from_prescribed_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hy : OnOuterFace I.embedding I.outer y) (hyP : y ∉ I.precolor.vertices)
    (hxa : G.Adj x a) (hxy : G.Adj x y) : False := by
  apply I.no_interior_two_path_from_prescribed_endpoint_to_noninternal_boundary hG p hp hface hroot hExact r hr hP hbad hsmall x y hx hy
    (fun h => hyP (h ▸ (hP a).2 r.start_mem_support)) ?_ hxa hxy
  intro k _ _ he
  exact hyP ((hP y).2 (he ▸ r.getVert_mem_support k))

/-- The remaining interior common-neighbour obstruction at a prescribed
endpoint can reach only native positions three or four of the prescription.
The other endpoint was excluded above, and girth excludes positions one/two. -/
lemma interior_endpoint_shared_neighbour_indices (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x)
    (hyP : y ∈ I.precolor.vertices) (hya : y ≠ a) (hxa : G.Adj x a) (hxy : G.Adj x y) :
    ∃ k : ℕ, (k = 3 ∨ k = 4) ∧ k < r.length ∧ r.getVert k = y := by
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hex : ∃ k : ℕ, 0 < k ∧ k < r.length ∧ r.getVert k = y := by
    by_contra h
    push Not at h
    exact I.no_interior_two_path_from_prescribed_endpoint_to_noninternal_boundary hG p hp hface hroot hExact r hr hPv hbad hsmall
      x y hx (I.on_outer y hyP) hya h hxa hxy
  obtain ⟨k, hkpos, hklt, hky⟩ := hex
  have hrlen : r.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup, Walk.length_support] at hn
    omega
  have hxR : x ∉ r.support := fun h => hx (I.on_outer x ((hPv x).2 h))
  have hk3 : 3 ≤ k := by
    by_contra h
    have hkle : k ≤ 2 := by omega
    have hqLen : (r.take k).length ≤ 2 := by
      rw [Walk.take_length, Nat.min_eq_left (by omega : k ≤ r.length)]
      exact hkle
    have hyq : y ∈ (r.take k).support := by simpa only [hky] using (r.take k).end_mem_support
    have hxq : x ∉ (r.take k).support := fun h => hxR ((Walk.isSubwalk_take r k).support_subset h)
    exact hya (short_path_endpoint_neighbour_unique I.girth (r.take k) (hr.take k) hqLen hxq hxa y hyq hxy)
  exact ⟨k, by omega, hklt, hky⟩

end Thomassen.BoundaryInstance
