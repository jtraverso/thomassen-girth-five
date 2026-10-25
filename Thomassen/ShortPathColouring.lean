/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.NativeArcPathCut
public import Thomassen.ConnectedInstance
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

/-! Strict list-extension induction on short path cuts with full private lists. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Every simple path of at most three edges is induced in girth at least five. -/
lemma short_path_isChordless (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 3) : q.IsChordless := by
  apply Walk.isChordless_iff_forall_mem_edges.2
  intro x y hx hy hxy
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
  obtain ⟨j, hjy, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hy
  subst x
  subst y
  have hnear : ∀ i j : ℕ, i ≤ q.length → j ≤ q.length → i ≤ j →
      G.Adj (q.getVert i) (q.getVert j) → s(q.getVert i, q.getVert j) ∈ q.edges := by
    intro i j hi hj hij hxy
    rcases (by omega : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3) with h | h | h | h
    · exact (hxy.ne (congrArg q.getVert h.symm)).elim
    · apply q.mk_mem_edges_iff_exists.2
      exact ⟨i, by omega, by rw [h]⟩
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h02 : G.Adj (q.getVert i) (q.getVert (i + 2)) := by rwa [h] at hxy
      exact (neighbors_nonadjacent hg h01 h02 (by simpa only [Nat.add_assoc] using h12)).elim
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h23 := q.adj_getVert_succ (by omega : i + 2 < q.length)
      have hne : q.getVert i ≠ q.getVert (i + 2) := fun heq => by
        have hidx := hp.getVert_injOn hi (by change i + 2 ≤ q.length; omega) heq
        omega
      have h03 : G.Adj (q.getVert i) (q.getVert (i + 3)) := by rwa [h] at hxy
      have heq := common_neighbor_unique hg hne h01
        (by simpa only [Nat.add_assoc] using h12.symm) h03
        (by simpa only [Nat.add_assoc] using h23)
      have hidx := hp.getVert_injOn (by change i + 1 ≤ q.length; omega)
        (by change i + 3 ≤ q.length; omega) heq
      omega
  rcases le_total i j with h | h
  · exact hnear i j hi hj h hxy
  · simpa only [Sym2.eq_swap] using hnear j i hj hi h hxy.symm

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- Colour the prescription side first and prescribe its separator path on the
other side. Old short lists may remain if they have no neighbour on that path.
Every list condition is verified before invoking strict induction. -/
theorem colourable_of_short_path_without_short_neighbours (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hInterior : ∀ x : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS x → 3 ≤ (I.lists x.1).card)
    (hNoShort : ∀ x ∈ S, x ∉ q.support → (I.lists x).card ≤ 2 →
      ∀ y ∈ q.support, ¬ G.Adj x y)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hpath : ∀ x ∈ q.support, x ∈ S ∧ x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h
  have hab : a ≠ b := fun h => by
    have hn := (hq.nil_iff_eq).2 h
    have hz := hn.length_eq_zero
    omega
  let : Nontrivial T := ⟨⟨⟨a, (hpath a q.start_mem_support).2⟩,
    ⟨b, (hpath b q.end_mem_support).2⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTconn.preconnected hP) hTsmall
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    simpa only [induceConnected, inducePrecolor] using hcT
  let f : V → C := fun x => if hx : x ∈ T then cT ⟨x, hx⟩ else I.prescribed x
  have hfT : ∀ x : T, f x.1 = cT x := by intro x; simp only [f, dite_eq_left x.2]
  have hqbound : q.support.toFinset.card ≤ 6 := by
    calc
      _ ≤ q.support.length := List.toFinset_card_le q.support
      _ = q.length + 1 := q.length_support
      _ ≤ 6 := by omega
  let P : BoundaryPrecolor G := .path q hq hqbound
  have hPS : ∀ x ∈ P.vertices, x ∈ S := fun x hx => (hpath x (List.mem_toFinset.1 hx)).1
  let Q := P.induce S hPS
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ q.support := by
    intro x
    simpa only [P, BoundaryPrecolor.vertices, List.mem_toFinset] using
      BoundaryPrecolor.mem_vertices_induce P S hPS x
  let L : S → Finset C := fun x => if x.1 ∈ q.support then {f x.1} else I.lists x.1
  have hNotP : ∀ x ∈ S, x ∉ q.support → x ∉ I.precolor.vertices := by
    intro x hxS hxq hxP
    have h : x ∈ S ∩ T := ⟨hxS, hP x hxP⟩
    rw [hinter] at h
    exact hxq h
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := oS
    precolor := Q
    lists := L
    prescribed := fun x => f x.1
    on_outer := fun x hx => hface x ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      have hx := (hpath x.1 ((hQv x).1 hends.1)).2
      have hy := (hpath y.1 ((hQv y).1 hends.2)).2
      simpa only [f, dite_eq_left hx, dite_eq_left hy] using
        cT.valid (show (G.induce T).Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩ from Q.adj_of_mem_edges he)
    boundary_lists := by
      intro x _ hx
      have hnot : x.1 ∉ q.support := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hnot]
      exact I.outside_precolor_list_ge_two (hNotP x.1 x.2 hnot)
    interior_lists := by
      intro x hx
      have hnot : x.1 ∉ q.support := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hnot] using hInterior x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x.1 ∈ q.support <;> by_cases hyQ : y.1 ∈ q.support
      · apply (BoundaryPrecolor.mem_edges_induce P S hPS x y).2
        exact List.mem_toFinset.2 ((short_path_isChordless I.girth q hq hqshort).mem_edges hxQ hyQ hxy)
      · have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyQ] using hy
        exact (hNoShort y.1 y.2 hyQ hyOld x.1 hxQ hxy.symm).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxQ] using hx
        exact (hNoShort x.1 x.2 hxQ hxOld y.1 hyQ hxy).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxQ] using hx
        have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyQ] using hy
        exact (hNotP x.1 x.2 hxQ
          (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)).1).elim }
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) J hSsmall
  change ∀ x : S, cS x ∈ L x at hcS
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by
    intro x
    by_cases hx : x.1 ∈ q.support
    · have heq : cS x = f x.1 := Finset.mem_singleton.1
        (by simpa only [L, ite_eq_left hx] using hcS x)
      rw [heq, hfT ⟨x.1, (hpath x.1 hx).2⟩]
      exact hT ⟨x.1, (hpath x.1 hx).2⟩
    · simpa only [L, ite_eq_right hx] using hcS x
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have hxq : x ∈ q.support := by
      have h : x ∈ S ∩ T := ⟨hx, hy⟩
      rwa [hinter] at h
    have heq : cS ⟨x, hx⟩ = f x := Finset.mem_singleton.1
      (by simpa only [L, ite_eq_left hxq] using hcS ⟨x, hx⟩)
    exact heq.trans (hfT ⟨x, hy⟩)

/-- The private three-list case follows from the general short-neighbour cut. -/
theorem colourable_of_three_list_short_path_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (hprivate : ∀ x ∈ S, x ∉ q.support → 3 ≤ (I.lists x).card)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_short_path_without_short_neighbours S T q hq hqpos hqshort
    hcover hinter hedges hTconn hP oS hface ?_ ?_ hSsmall hTsmall hsmall
  · intro x hx
    exact hprivate x.1 x.2 (fun h => hx (hface x h))
  · intro x hxS hxq hxShort y hy
    have h := hprivate x hxS hxq
    omega

/-- The short-path induction case allowing old two-lists on the trimmed arc,
provided they avoid the separator and the old prescription lies outside the arc.
Its induced faces and all other instance conditions follow from the actual cut. -/
theorem colourable_of_short_path_with_independent_short_arc (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hNoShortArc : ∀ x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), (I.lists x).card ≤ 2 →
      ∀ y ∈ (p.drop n).support, ¬ G.Adj x y)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, _, hTconn,
    _, hkeep, ⟨oS, hSface⟩, _⟩ :=
    native_short_arc_path_cut I.embedding I.outer I.girth hconn p hp n m hn hm hm3 hlen hArc hroot houtside
  have hP : ∀ x ∈ I.precolor.vertices, x ∈ T :=
    fun x hx => hkeep x (I.on_outer x hx) (hPoutside x hx)
  have hOldCycle : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → x.1 ∈ p.support := by
    intro x hxFace
    by_cases hxA : x.1 ∈ cycleInterval (walkCycleVertices p) 1 (n - 2)
    · have hxC := cycleInterval_subset 1 (n - 2) hxA
      rwa [walkCycleVertices_range p hp] at hxC
    · have hxT := hkeep x.1 hxFace hxA
      have h : x.1 ∈ S ∩ T := ⟨x.2, hxT⟩
      rw [hinter] at h
      exact (Walk.isSubwalk_drop p n).support_subset h
  apply I.colourable_of_short_path_without_short_neighbours S T (p.drop n) (hp.isPath_drop (by omega))
    (by rw [Walk.drop_length, hlen]; omega) (by rw [Walk.drop_length, hlen]; omega)
    hcover hinter hedges hTconn hP oS ?_ ?_ ?_ hSsmall hTsmall hsmall
  · intro x hx
    exact (hSface x).2 ((Walk.isSubwalk_drop p n).support_subset hx)
  · intro x hx
    apply I.interior_lists
    intro hxOld
    exact hx ((hSface x).2 (hOldCycle x hxOld))
  · intro x hxS hxq hxShort y hy
    have hxA : x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
      by_cases hxFace : OnOuterFace I.embedding I.outer x
      · by_contra hxA
        have hxT := hkeep x hxFace hxA
        have h : x ∈ S ∩ T := ⟨hxS, hxT⟩
        rw [hinter] at h
        exact hxq h
      · have h := I.interior_lists x hxFace
        omega
    exact hNoShortArc x hxA hxShort y hy

/-- If the whole trimmed arc has three-lists, the short-neighbour condition
holds automatically. -/
theorem colourable_of_short_path_with_three_list_arc (I : BoundaryInstance G C)
    (hconn : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hm3 : m ≤ 3) (hlen : p.length = n + m)
    (hArc : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp)
      (cycleInterval (walkCycleVertices p) 1 (n - 2)))
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (houtside : ∃ x, OnOuterFace I.embedding I.outer x ∧ x ∉ p.support)
    (hArcThree : ∀ x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2), 3 ≤ (I.lists x).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  apply I.colourable_of_short_path_with_independent_short_arc hconn p hp n m hn hm hm3 hlen
    hArc hroot houtside ?_ ?_ hsmall
  · intro x hxP hxA
    have h := hArcThree x hxA
    simp only [I.singleton x hxP, Finset.card_singleton] at h
    omega
  · intro x hxA hxShort y hy
    have h := hArcThree x hxA
    omega

end BoundaryInstance
end Thomassen
