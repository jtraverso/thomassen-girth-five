/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundaryChordReduction

/-! Actual native cycles obtained by closing an original face arc with a path. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- Follow the original face for `n` edges, then return along the supplied
path. The original walk and closing path retain their actual vertex types. -/
def spliceFacePath (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a) : G.Walk a a :=
  (p.take n).append q

lemma spliceFacePath_length (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) : (spliceFacePath p n q).length = n + q.length := by
  simp only [spliceFacePath, Walk.length_append, Walk.take_length, Nat.min_eq_left hn]

lemma spliceFacePath_getVert_prefix (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) {i : ℕ} (hi : i ≤ n) :
    (spliceFacePath p n q).getVert i = p.getVert i := by
  simp only [spliceFacePath, Walk.getVert_append', Walk.take_length, Nat.min_eq_left hn,
    ite_eq_left hi, Walk.take_getVert, Nat.min_eq_right hi]

/-- Internal disjointness from the original face makes the spliced walk an
actual simple cycle. The original arc is nontrivial and is strictly shorter
than the original facial cycle. -/
lemma spliceFacePath_isCycle (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    (spliceFacePath p n q).IsCycle := by
  have hl := hp.isPath_take hnp
  have hnotL : a ∉ (p.take n).support.tail := by
    have h := hl.support_nodup
    rw [← (p.take n).cons_tail_support] at h
    exact (List.nodup_cons.1 h).1
  have hnotR : p.getVert n ∉ q.support.tail := by
    have h := hq.support_nodup
    rw [← q.cons_tail_support] at h
    exact (List.nodup_cons.1 h).1
  apply hl.isCycle_append hq ?_ (Or.inl (by rw [Walk.take_length, Nat.min_eq_left (by omega : n ≤ p.length)]; omega))
  intro x hxL hxR
  have hxq := List.mem_of_mem_tail hxR
  have hxp : x ∈ p.support := (Walk.isSubwalk_take p n).support_subset (List.mem_of_mem_tail hxL)
  rcases hmeet x hxq hxp with rfl | h
  · exact hnotL hxL
  · exact hnotR (h ▸ hxR)

/-- The native returning suffix has precisely the original separator path's
vertices. This avoids identifying walks whose endpoint proof terms differ. -/
lemma spliceFacePath_drop_support (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : n ≤ p.length) :
    ∀ x, x ∈ ((spliceFacePath p n q).drop n).support ↔ x ∈ q.support := by
  intro x
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    apply Walk.mem_support_iff_exists_getVert.2
    refine ⟨i, ?_, ?_⟩
    · rw [Walk.drop_getVert, spliceFacePath, Walk.getVert_append, Walk.take_length,
        Nat.min_eq_left hn, ite_eq_right (by omega : ¬ (n + i < n)), Nat.add_sub_cancel_left] at hix
      exact hix
    · rw [Walk.drop_length, spliceFacePath_length p n q hn, Nat.add_sub_cancel_left] at hi
      exact hi
  · intro hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    apply Walk.mem_support_iff_exists_getVert.2
    refine ⟨i, ?_, ?_⟩
    · rw [Walk.drop_getVert, spliceFacePath, Walk.getVert_append, Walk.take_length,
        Nat.min_eq_left hn, ite_eq_right (by omega : ¬ (n + i < n)), Nat.add_sub_cancel_left]
      exact hix
    · rw [Walk.drop_length, spliceFacePath_length p n q hn, Nat.add_sub_cancel_left]
      exact hi

/-- On the original arc the new indexed cycle still has the original native
vertices, without a cyclic index cast changing the vertex. -/
lemma spliceFacePath_cycleVertex_prefix (p : G.Walk a a) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hn : n ≤ p.length) {i : ℕ} (hi : i ≤ n) :
    walkCycleVertices (spliceFacePath p n q) (i : ZMod (spliceFacePath p n q).length) = p.getVert i := by
  rw [walkCycleVertices_nat_le _ (by rw [spliceFacePath_length p n q hn]; omega)]
  exact spliceFacePath_getVert_prefix p n q hn hi

/-- The arc that is removed by the separator is exactly the original face
arc; the closing path changes none of its vertices. -/
lemma spliceFacePath_arc (p : G.Walk a a) (n : ℕ) (q : G.Walk (p.getVert n) a)
    (hn : 2 ≤ n) (hnp : n ≤ p.length) :
    cycleInterval (walkCycleVertices (spliceFacePath p n q)) 1 (n - 2) =
      cycleInterval (walkCycleVertices p) 1 (n - 2) := by
  ext x
  simp only [cycleInterval, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨i, hi, hix⟩ <;> refine ⟨i, hi, ?_⟩
  · rw [spliceFacePath_cycleVertex_prefix p n q hnp (by omega)] at hix
    rwa [walkCycleVertices_nat_le p (by omega)]
  · rw [spliceFacePath_cycleVertex_prefix p n q hnp (by omega)]
    rwa [walkCycleVertices_nat_le p (by omega)] at hix

/-- A vertex of the complementary old face arc remains outside the spliced
cycle. Both cut pieces will consequently have strictly fewer vertices. -/
lemma spliceFacePath_misses_next_vertex (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    p.getVert (n + 1) ∉ (spliceFacePath p n q).support := by
  intro hx
  change p.getVert (n + 1) ∈ ((p.take n).append q).support at hx
  rw [Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · obtain ⟨j, hjx, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    rw [Walk.take_length, Nat.min_eq_left (by omega : n ≤ p.length)] at hj
    rw [Walk.take_getVert, Nat.min_eq_right hj] at hjx
    have he := hp.getVert_injOn' (show j ∈ {i | i ≤ p.length - 1} from by change j ≤ p.length - 1; omega)
      (show n + 1 ∈ {i | i ≤ p.length - 1} from by change n + 1 ≤ p.length - 1; omega) hjx
    omega
  · rcases hmeet _ hx (p.getVert_mem_support (n + 1)) with h | h
    · have h' : p.getVert (n + 1) = p.getVert 0 := by simpa only [Walk.getVert_zero] using h
      have he := hp.getVert_injOn' (show n + 1 ∈ {i | i ≤ p.length - 1} from by change n + 1 ≤ p.length - 1; omega)
        (show 0 ∈ {i | i ≤ p.length - 1} from Nat.zero_le _) h'
      omega
    · have he := hp.getVert_injOn' (show n + 1 ∈ {i | i ≤ p.length - 1} from by change n + 1 ≤ p.length - 1; omega)
        (show n ∈ {i | i ≤ p.length - 1} from by change n ≤ p.length - 1; omega) h
      omega


/-- All old corners inside the retained face prefix are unchanged by the
closing path. The new and old actual darts, not only the vertices, coincide. -/
theorem spliceFacePath_isFacialAlong (M : PlaneMap G) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hqpos : 0 < q.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    IsFacialCycleAlong M (walk_isCycleMap (spliceFacePath p n q) (spliceFacePath_isCycle p hp n q hq hn hnp hmeet))
      (cycleInterval (walkCycleVertices (spliceFacePath p n q)) 1 (n - 2)) := by
  let r := spliceFacePath p n q
  let hr := spliceFacePath_isCycle p hp n q hq hn hnp hmeet
  have hlen : r.length = n + q.length := spliceFacePath_length p n q (by omega)
  have hrlen : 1 < r.length := by omega
  have hplen := hp.three_le_length
  let : NeZero r.length := ⟨by omega⟩
  let : NeZero p.length := ⟨by omega⟩
  have hd : ∀ i : ZMod r.length, i.val < n →
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap r hr) i) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) (i.val : ZMod p.length)) := by
    intro i hi
    apply (Dart.ext_iff _ _).2
    apply Prod.ext
    · change r.getVert i.val = p.getVert (i.val : ZMod p.length).val
      rw [ZMod.val_natCast_of_lt (by omega : i.val < p.length)]
      exact spliceFacePath_getVert_prefix p n q (by omega) (by omega)
    · change walkCycleVertices r (i + 1) = walkCycleVertices p ((i.val : ZMod p.length) + 1)
      rw [walkCycleVertices_next r hrlen, walkCycleVertices_next p (by omega),
        ZMod.val_natCast_of_lt (by omega : i.val < p.length)]
      exact spliceFacePath_getVert_prefix p n q (by omega) (by omega)
  intro i hiArc
  obtain ⟨j, hj, hji⟩ := hiArc
  have heq : (((1 + j : ℕ) : ZMod r.length)) = i := (walk_isCycleMap r hr).inj hji
  have hival : i.val = 1 + j := by
    rw [← heq, ZMod.val_natCast_of_lt (by omega : 1 + j < r.length)]
  have hipos : 0 < i.val := by omega
  have hin : i.val < n := by omega
  have hiprev : (i - 1).val = i.val - 1 := by
    have he : (((i.val - 1 : ℕ) : ZMod r.length)) = i - 1 := by
      rw [Nat.cast_sub hipos, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [← he, ZMod.val_natCast_of_lt (by have := ZMod.val_lt i; omega)]
  rw [hd i hin, hd (i - 1) (by omega), hiprev, Nat.cast_sub hipos, Nat.cast_one]
  exact hface (i.val : ZMod p.length) (Set.mem_univ _)

/-- The spliced cycle begins at precisely the same old dart as the original
face cycle. Its relation to the selected face is therefore inherited exactly. -/
lemma spliceFacePath_root (p : G.Walk a a) (hp : p.IsCycle) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath) (hn : 2 ≤ n) (hnp : n < p.length)
    (hmeet : ∀ x ∈ q.support, x ∈ p.support → x = a ∨ x = p.getVert n) :
    walkArcRoot (spliceFacePath p n q) (spliceFacePath_isCycle p hp n q hq hn hnp hmeet) = walkArcRoot p hp := by
  have hlen : 1 < (spliceFacePath p n q).length := by rw [spliceFacePath_length p n q (by omega)]; omega
  apply (Dart.ext_iff _ _).2
  apply Prod.ext
  · change walkCycleVertices (spliceFacePath p n q) 0 = walkCycleVertices p 0
    simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  · change walkCycleVertices (spliceFacePath p n q) (0 + 1) = walkCycleVertices p (0 + 1)
    rw [walkCycleVertices_next _ hlen, walkCycleVertices_next p (by have := hp.three_le_length; omega), ZMod.val_zero, ZMod.val_zero]
    exact spliceFacePath_getVert_prefix p n q (by omega) (by omega)

end Thomassen
