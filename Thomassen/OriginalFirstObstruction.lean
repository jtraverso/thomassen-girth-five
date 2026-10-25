/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalSecondFiveFace

/-! Resolve the first endpoint obstruction in original proof step (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- In the first residual two-path q₁-q₃-q₄, q₄ must be an old short vertex.
If it were newly exposed, the actual second five-cycle would force degree two
at the interior three-list vertex q₂, contradicting strict original induction. -/
theorem first_residual_obstruction_endpoint_old (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (q₁ q₂ q₃ q₄ : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)})
    (hq₁ : q₁.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₂ : q₂.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₄ : q₄.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₂new : q₂.1 ∉ I.short) (hq₂inner : ¬ OnOuterFace I.embedding I.outer q₂.1)
    (h2q : G.Adj (p.getVert 2) q₁.1) (h12 : G.Adj q₁.1 q₂.1) (h2a : G.Adj q₂.1 a)
    (h13 : G.Adj q₁.1 q₃.1) (h34 : G.Adj q₃.1 q₄.1) (h14 : q₁ ≠ q₄)
    (hUnique : ∀ r s : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)},
      r.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} →
      s.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} → G.Adj r.1 s.1 →
      (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁))
    (hMiddle : ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) : q₄.1 ∈ I.short := by
  by_contra hq₄new
  let D : Finset V := {a,p.getVert 1,p.getVert 2}
  let Q : Set V := (↑D : Set V)ᶜ
  have hne (q : Q) : q.1 ≠ a ∧ q.1 ≠ p.getVert 1 ∧ q.1 ≠ p.getVert 2 := by
    have hqD : q.1 ∉ D := q.2
    simpa only [D,Finset.mem_insert,Finset.mem_singleton,not_or] using hqD
  have h14' : q₁.1 ≠ q₄.1 := fun h => h14 (Subtype.ext h)
  have hq₃out : q₃.1 ∉ exposedShortSet G I.short D := by
    intro hq₃
    have h32 : q₃=q₂ := by
      rcases hUnique q₁ q₃ hq₁ hq₃ h13 with h | h
      · exact h.2
      · exact (h12.ne (congrArg Subtype.val h.1)).elim
    rcases hUnique q₂ q₄ hq₂ hq₄ (h32 ▸ h34) with h | h
    · exact (h12.ne (congrArg Subtype.val h.1).symm).elim
    · exact h14 h.2.symm
  have h4a : G.Adj q₄.1 a := by
    obtain ⟨t,ht,h4t⟩ := hq₄.2.resolve_left hq₄new
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht
    · subst t; exact h4t
    · subst t
      rcases hMiddle q₄.1 h4t.symm with h | h
      · exact ((hne q₄).1 h).elim
      · exact ((hne q₄).2.2 h).elim
    · subst t
      have he := common_neighbor_unique I.girth h14' h2q.symm h4t h13 h34.symm
      exact ((hne q₃).2.2 he.symm).elim
  have h23 : q₂.1 ≠ q₃.1 := fun h => hq₃out (h ▸ hq₂)
  have h24 : q₂.1 ≠ q₄.1 := by
    intro h
    exact neighbors_nonadjacent I.girth h12 h13 (by simpa only [h] using h34.symm)
  let r : G.Walk a a := .cons h2a.symm (.cons h12.symm (.cons h13 (.cons h34 (.cons h4a .nil))))
  have hr : r.IsCycle := by
    simp [r,Walk.cons_isCycle_iff,Walk.isPath_def,(hne q₁).1,(hne q₂).1,(hne q₃).1,(hne q₄).1,
      h12.ne,h13.ne,h34.ne,h14',h23,h24,Ne.symm]
  have hrl : r.length=5 := rfl
  let : NeZero r.length := ⟨by omega⟩
  have hr1 : walkCycleVertices r 1 = q₂.1 := by
    simpa only [Nat.cast_one,r,Walk.getVert_cons_succ,Walk.getVert_zero] using walkCycleVertices_nat_le r (i := 1) (by omega)
  have hr2 : walkCycleVertices r 2 = q₁.1 := by
    simpa only [Nat.cast_ofNat,r,Walk.getVert_cons_succ,Walk.getVert_zero] using walkCycleVertices_nat_le r (i := 2) (by omega)
  have hrr : walkArcRoot r hr = (⟨(a,q₂.1),h2a.symm⟩ : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    refine Prod.ext ?_ ?_
    · change walkCycleVertices r 0=a
      simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    · change walkCycleVertices r (0+1)=q₂.1
      simpa only [zero_add] using hr1
  have hrnext : toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap r hr) 1) =
      (⟨(q₂.1,q₁.1),h12.symm⟩ : G.Dart) := by
    apply (Dart.ext_iff _ _).2
    exact Prod.ext hr1 (by change walkCycleVertices r (1+1)=q₁.1; simpa only [show (1:ZMod r.length)+1=2 by norm_num] using hr2)
  have hd1 : (walkArcRoot p hp).symm.fst = p.getVert 1 := by
    change walkCycleVertices p (0+1) = p.getVert 1
    simpa only [zero_add,Nat.cast_one] using walkCycleVertices_nat_le p (i := 1)
      (by have := hp.three_le_length; omega)
  have hdout : (walkArcRoot p hp).symm.fst ∉ r.support := by
    rw [hd1]
    intro h
    simp only [r,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h | h | h
    · exact (p.adj_getVert_succ (by have := hp.three_le_length; omega : 0<p.length)).ne
        (by simpa only [Walk.getVert_zero,zero_add] using h.symm)
    · exact (hne q₂).2.1 h.symm
    · exact (hne q₁).2.1 h.symm
    · exact (hne q₃).2.1 h.symm
    · exact (hne q₄).2.1 h.symm
    · exact (p.adj_getVert_succ (by have := hp.three_le_length; omega : 0<p.length)).ne
        (by simpa only [Walk.getVert_zero,zero_add] using h.symm)
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hq1ne : q₁.1 ≠ p.getVert 1 := (hne q₁).2.1
  obtain ⟨hc0,hc1⟩ := I.three_path_inner_face_corners_allow_boundary hG p hp hch hface hroot
    (five_le_egirth_iff.1 I.girth _ p hp) q₁.1 q₂.1 hq1ne hq₂inner h2q h12 h2a hbad hsmall
  have hprev : I.embedding.facePerm (walkArcRoot p hp).symm=walkArcRoot r hr := hc0.trans hrr.symm
  have hcorner : I.embedding.facePerm (walkArcRoot r hr) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap r hr) 1) := by
    rw [hrr,hrnext]
    exact hc1
  have hNeighbours := I.short_cycle_single_corner_neighbours hbad hsmall r hr (by omega)
    (walkArcRoot p hp).symm hdout hprev hcorner
  change ∀ z, G.Adj q₂.1 z → z=a ∨ z=q₁.1 at hNeighbours
  have hUpper : (Finset.univ.filter (G.Adj q₂.1)).card ≤ 2 := by
    apply (Finset.card_le_card (s := Finset.univ.filter (G.Adj q₂.1)) (t := {a,q₁.1}) ?_).trans Finset.card_le_two
    intro z hz
    rcases hNeighbours z (Finset.mem_filter.1 hz).2 with h | h <;> simp [h]
  have hLower := I.list_card_le_degree_of_minimal_counterexample hbad hsmall q₂.1
    (fun h => hq₂inner (h.symm ▸ I.a_outer)) (fun h => hq₂inner (h.symm ▸ I.b_outer))
  have hThree := I.list_three q₂.1 hq₂new
  omega

/-- Once the first obstruction ends at an old short vertex, the first
three vertices of that obstruction are forced onto the next three positions
of the original facial cycle. The exceptional endpoint at position two has
only its two facial neighbours. -/
theorem first_residual_obstruction_boundary_chain (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hxA : p.getVert 2 ∈ I.short)
    (q₁ q₂ q₃ q₄ : V) (hq₄ : q₄ ∈ I.short)
    (hq₂inner : ¬ OnOuterFace I.embedding I.outer q₂)
    (h2q : G.Adj (p.getVert 2) q₁) (h12 : G.Adj q₁ q₂) (h2a : G.Adj q₂ a)
    (h13 : G.Adj q₁ q₃) (h34 : G.Adj q₃ q₄)
    (h1ne : q₁ ≠ p.getVert 1) (h3ne : q₃ ≠ p.getVert 2)
    (h4ne : q₄ ≠ p.getVert 2) (h14 : q₁ ≠ q₄) :
    q₁ = p.getVert 3 ∧ q₃ = p.getVert 4 ∧ q₄ = p.getVert 5 ∧
      (∀ z, G.Adj (p.getVert 2) z → z = p.getVert 1 ∨ z = q₁) := by
  have hq₁face : OnOuterFace I.embedding I.outer q₁ := by
    by_contra hq₁inner
    by_cases hq₃face : OnOuterFace I.embedding I.outer q₃
    · exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall
        (p.getVert 2) q₃ q₁ hxA hq₃face h3ne.symm hq₁inner h2q.symm h13
    · exact I.no_interior_three_path_of_minimal_counterexample hbad hsmall
        (p.getVert 2) q₄ q₁ q₃ hxA hq₄ h4ne.symm hq₁inner hq₃face h2q h13 h34
  have hq₃face : OnOuterFace I.embedding I.outer q₃ := by
    by_contra hq₃inner
    exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall q₄ q₁ q₃
      hq₄ hq₁face h14.symm hq₃inner h34 h13.symm
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  obtain ⟨h1,hdegree,_⟩ := I.boundary_three_path_first_vertex hG p hp hch hface hroot hlen
    q₁ q₂ hq₁face h1ne hq₂inner h2q h12 h2a hbad hsmall
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have h3 : q₃ = p.getVert 4 := by
    exact (chordless_native_cycle_vertex_neighbours p hp hch 3 (by omega) (by omega)
      ((hverts q₃).2 hq₃face) (h1 ▸ h13)).resolve_left h3ne
  have h4 : q₄ = p.getVert 5 := by
    exact (chordless_native_cycle_vertex_neighbours p hp hch 4 (by omega) (by omega)
      ((hverts q₄).2 (I.on_outer q₄ hq₄)) (h3 ▸ h34)).resolve_left
      (fun h => h14 (h1.trans h.symm))
  exact ⟨h1,h3,h4,hdegree⟩

end Thomassen.OriginalBoundaryInstance
