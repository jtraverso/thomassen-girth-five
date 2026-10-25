/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleSeparation
public import Thomassen.Girth

/-! Native walks as indexed cycles, with exact vertex and edge sets. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

def walkCycleVertices (p : G.Walk a a) : ZMod p.length → V := fun i => p.getVert i.val

lemma walkCycleVertices_next (p : G.Walk a a) (hp : 1 < p.length) (i : ZMod p.length) :
    walkCycleVertices p (i + 1) = p.getVert (i.val + 1) := by
  let : NeZero p.length := ⟨by omega⟩
  have hi := ZMod.val_lt i
  let : Fact (1 < p.length) := ⟨hp⟩
  have hone : (1 : ZMod p.length).val = 1 := ZMod.val_one p.length
  change p.getVert (i + 1).val = _
  rw [ZMod.val_add, hone]
  by_cases hlt : i.val + 1 < p.length
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : i.val + 1 = p.length := by omega
    rw [heq, Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]

lemma walk_isCycleMap (p : G.Walk a a) (hp : p.IsCycle) :
    IsCycleMap G (walkCycleVertices p) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply ZMod.val_injective p.length
    exact hp.getVert_injOn' (by have := ZMod.val_lt i; simp only [Set.mem_ofPred_eq]; omega)
      (by have := ZMod.val_lt j; simp only [Set.mem_ofPred_eq]; omega) hij
  · intro i
    rw [walkCycleVertices_next p (by omega)]
    exact p.adj_getVert_succ (ZMod.val_lt i)

lemma walkCycleVertices_range (p : G.Walk a a) (hp : p.IsCycle) :
    Set.range (walkCycleVertices p) = {x | x ∈ p.support} := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact p.getVert_mem_support _
  · intro hx
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    by_cases hlt : n < p.length
    · exact ⟨n, by simpa only [walkCycleVertices, ZMod.val_natCast_of_lt hlt] using hn⟩
    · have heq : n = p.length := by omega
      refine ⟨0, ?_⟩
      simpa only [walkCycleVertices, ZMod.val_zero, heq, Walk.getVert_length,
        Walk.getVert_zero] using hn

lemma walkCycleVertices_edges (p : G.Walk a a) (hp : p.IsCycle) (x y : V) :
    (cyclicSubgraph G (walkCycleVertices p)).Adj x y ↔ s(x, y) ∈ p.edges := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  constructor
  · rintro ⟨_, i, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · apply (p.mk_mem_edges_iff_exists).2
      refine ⟨i.val, ZMod.val_lt i, ?_⟩
      rw [hx, hy, walkCycleVertices_next p (by omega)]
      rfl
    · apply (p.mk_mem_edges_iff_exists).2
      refine ⟨i.val, ZMod.val_lt i, ?_⟩
      rw [hx, hy, walkCycleVertices_next p (by omega)]
      exact Sym2.eq_swap
  · intro h
    refine ⟨p.adj_of_mem_edges h, ?_⟩
    obtain ⟨n, hnl, hn⟩ := (p.mk_mem_edges_iff_exists).1 h
    have hfirst : walkCycleVertices p (n : ZMod p.length) = p.getVert n := by
      simp only [walkCycleVertices, ZMod.val_natCast_of_lt hnl]
    have hnext : walkCycleVertices p ((n : ZMod p.length) + 1) = p.getVert (n + 1) := by
      rw [walkCycleVertices_next p (by omega), ZMod.val_natCast_of_lt hnl]
    refine ⟨n, ?_⟩
    rcases Sym2.eq_iff.1 hn with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨hx.symm.trans hfirst.symm, hy.symm.trans hnext.symm⟩
    · exact Or.inr ⟨hy.symm.trans hnext.symm, hx.symm.trans hfirst.symm⟩

lemma cycle_support_card_eq_length (p : G.Walk a a) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  classical
  have ha : a ∈ p.support.tail := p.end_mem_tail_support hp.not_nil
  have hs : p.support.toFinset = p.support.tail.toFinset := by
    calc
      p.support.toFinset = (a :: p.support.tail).toFinset := congrArg List.toFinset p.cons_tail_support.symm
      _ = p.support.tail.toFinset := by simp only [List.toFinset_cons,
          Finset.insert_eq_of_mem (List.mem_toFinset.2 ha)]
  rw [hs, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail,
    Walk.length_support, Nat.add_sub_cancel]

variable {k : ℕ} {c : ZMod k → V}

lemma zmod_two_ne_zero_of_three_le (hk : 3 ≤ k) : (2 : ZMod k) ≠ 0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff 2 k).1 hz
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma cycle_no_chord_two (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c) (i : ZMod k) :
    ¬ G.Adj (c i) (c (i + 2)) := by
  have h2 : G.Adj (c (i + 1)) (c (i + 2)) := by
    simpa only [show i + 1 + 1 = i + 2 by ring] using hc.adj (i + 1)
  exact neighbors_nonadjacent hg (hc.adj i).symm h2

lemma cycle_no_chord_three (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (i : ZMod k) : ¬ G.Adj (c i) (c (i + 3)) := by
  intro hch
  have h2 : G.Adj (c (i + 1)) (c (i + 2)) := by
    simpa only [show i + 1 + 1 = i + 2 by ring] using hc.adj (i + 1)
  have h3 : G.Adj (c (i + 2)) (c (i + 3)) := by
    simpa only [show i + 2 + 1 = i + 3 by ring] using hc.adj (i + 2)
  have hne : c i ≠ c (i + 2) := by
    intro h
    have hi := hc.inj h
    apply zmod_two_ne_zero_of_three_le hk
    linear_combination -hi
  have heq := hc.inj (common_neighbor_unique hg hne (hc.adj i) h2.symm hch h3)
  apply zmod_two_ne_zero_of_three_le hk
  linear_combination -heq

/-- Every cycle of length at most six in girth at least five is chordless. -/
lemma short_cycle_isChordless [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hsmall : k ≤ 6) : IsChordless G c := by
  intro i j hxy
  let n := (j - i).val
  have hn : n < k := ZMod.val_lt _
  have hij : j = i + (n : ZMod k) := by simp [n]
  by_cases hshort : n ≤ 3
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · have hji : j = i := by simpa only [h0, Nat.cast_zero, add_zero] using hij
      exact (hxy.ne (congrArg c hji.symm)).elim
    · exact Or.inl (by simpa only [h1, Nat.cast_one] using hij)
    · exact (cycle_no_chord_two hg hc i (by simpa only [hij, h2, Nat.cast_ofNat] using hxy)).elim
    · exact (cycle_no_chord_three hg hc hk i
        (by simpa only [hij, h3, Nat.cast_ofNat] using hxy)).elim
  · have hm : 1 ≤ k - n ∧ k - n ≤ 2 := by omega
    have hji : i = j + ((k - n : ℕ) : ZMod k) := by
      rw [hij, add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hn.le, ZMod.natCast_self, add_zero]
    have hcases : k - n = 1 ∨ k - n = 2 := by omega
    rcases hcases with h1 | h2
    · exact Or.inr (by simpa only [h1, Nat.cast_one] using hji)
    · exact (cycle_no_chord_two hg hc j
        (by simpa only [hji, h2, Nat.cast_ofNat] using hxy.symm)).elim

/-- The concrete two-side separation needed for a native prescribed cycle of
at most six vertices. Girth supplies chordlessness, so no geometric separation
or chordlessness assumption is left to the caller. -/
theorem short_native_cycle_separation [Fintype V] (M : PlaneMap G)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hsmall : p.support.toFinset.card ≤ 6) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ p.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ p.support) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hbound : p.length ≤ 6 := by rwa [cycle_support_card_eq_length p hp] at hsmall
  have hc := walk_isCycleMap p hp
  have hch := short_cycle_isChordless hg hc hlen hbound
  simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using
    chordless_cycle_separation M hc hlen hch hconn

variable [Fintype V]

/-- Both open face regions of the native cycle contain a vertex. -/
def NativeCycleSeparates (M : PlaneMap G) (p : G.Walk a a) (hp : p.IsCycle) : Prop :=
  (∃ x, inSubface M cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) 0) x) ∧
    (∃ x, inSubface M cyclicSubgraph_le (cycleBackward (walk_isCycleMap p hp) 0) x)

/-- An oriented proper cut: the first side contains the original face, both
induced vertex types are strictly smaller, and the common selected boundary is
the native cycle. Separation is supplied by two actual nonempty face regions. -/
theorem short_native_cycle_proper_cut (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (hconn : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hsmall : p.support.toFinset.card ≤ 6) (hsep : NativeCycleSeparates M p hp) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      (∀ x, OnOuterFace M outer x → x ∈ S) ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ p.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support) ∧
      (∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ p.support) := by
  have hk := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let hc := walk_isCycleMap p hp
  have hbound : p.length ≤ 6 := by rwa [cycle_support_card_eq_length p hp] at hsmall
  have hch := short_cycle_isChordless hg hc hk hbound
  let left := cycleForward hc 0
  let right := cycleBackward hc 0
  let S := subfaceSide M cyclicSubgraph_le left
  let T := subfaceSide M cyclicSubgraph_le right
  have hne := cycle_faces_distinct (restrictMap M cyclicSubgraph_le) hc hk
  have hcover : S ∪ T = Set.univ := cycle_sides_cover M hc hk hconn
  have hinter : S ∩ T = {x | x ∈ p.support} := by
    simpa only [walkCycleVertices_range p hp] using cycle_sides_inter M hc hk
  have hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T) :=
    fun {_ _} h => cycle_sides_no_crossing M hc hk hconn h
  have hSconn : (G.induce S).Connected :=
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le left)
  have hTconn : (G.induce T).Connected :=
    (connSet_iff_induce_connected _ _).1 (subfaceSide_connSet M cyclicSubgraph_le right)
  have hSface : ∃ o : (G.induce S).Dart, ∀ x : S,
      OnOuterFace (inducedPlaneMap M S) o x ↔ x.1 ∈ p.support := by
    refine ⟨induceDartEquiv G S (toDart (cyclicSubgraph_le_side M hc hk left) right), ?_⟩
    intro x
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using
      cycle_side_outer_iff M hc hk hch left right hne x
  have hTface : ∃ o : (G.induce T).Dart, ∀ x : T,
      OnOuterFace (inducedPlaneMap M T) o x ↔ x.1 ∈ p.support := by
    refine ⟨induceDartEquiv G T (toDart (cyclicSubgraph_le_side M hc hk right) left), ?_⟩
    intro x
    simpa only [walkCycleVertices_range p hp, Set.mem_ofPred_eq] using
      cycle_side_outer_iff M hc hk hch right left (fun h => hne h.symm) x
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hsep
  have hxT : x ∉ T := fun hxT =>
    hx.1 ((subfaceVertices_subset M cyclicSubgraph_le left)
      ((two_face_sides_inter M cyclicSubgraph_le (cyclicSubgraph_connected hc)
        left right hne) ▸ (show x ∈ S ∩ T from ⟨Or.inr hx, hxT⟩)).1)
  have hyS : y ∉ S := fun hyS =>
    hy.1 ((subfaceVertices_subset M cyclicSubgraph_le right)
      ((two_face_sides_inter M cyclicSubgraph_le (cyclicSubgraph_connected hc)
        left right hne) ▸ (show y ∈ S ∩ T from ⟨hyS, Or.inr hy⟩)).2)
  have hSsmall := card_induced_vertices_lt S hyS
  have hTsmall := card_induced_vertices_lt T hxT
  rcases cycle_original_face_one_side M hc hk hconn outer with houter | houter
  · exact ⟨S, T, hSsmall, hTsmall, houter, hcover, hinter, hedges, hSconn, hTconn, hSface, hTface⟩
  · exact ⟨T, S, hTsmall, hSsmall, houter, Set.union_comm S T ▸ hcover,
      Set.inter_comm S T ▸ hinter, fun {_ _} h => (hedges h).symm,
      hTconn, hSconn, hTface, hSface⟩

end Thomassen
