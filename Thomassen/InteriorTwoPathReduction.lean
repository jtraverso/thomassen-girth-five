/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorTwoPathSelection

/-! Complete two-edge interior-path reduction on a prescription-free facial arc. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A two-edge interior path cutting off an old facial arc free of the
prescription is a complete induction case. The first interior incidence selects
the cut, and chordlessness captures every remaining short neighbour. Neither
minimality, spliced corner equations nor a capture hypothesis is supplied. -/
theorem colourable_of_interior_two_path_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n))
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨j, hj, hjn, hzj, hmin⟩ := first_interior_two_path_neighbour I.embedding I.outer I.girth p hp hface hroot n hn hnp z hz hza hzn
  have hf : ∀ t, OnOuterFace I.embedding I.outer (p.getVert t) := fun t =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support t)
  have hinj : ∀ s t : ℕ, s ≤ j → t ≤ j → s ≠ t → p.getVert s ≠ p.getVert t := by
    intro s t hs ht hst heq
    exact hst (hp.getVert_injOn' (show s ∈ {i | i ≤ p.length - 1} from by change s ≤ p.length - 1; omega)
      (show t ∈ {i | i ≤ p.length - 1} from by change t ≤ p.length - 1; omega) heq)
  have hja : p.getVert j ≠ a := by simpa only [Walk.getVert_zero] using hinj j 0 le_rfl (by omega) (by omega)
  let q : G.Walk (p.getVert j) a := .cons hzj.symm (.cons hza .nil)
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons,
      List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨hzj.ne.symm, hja⟩, hza.ne⟩
  have hqlen : q.length = 2 := rfl
  have hInner : ∀ t, 0 < t → t < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert t) := by
    intro t ht htl
    have ht1 : t = 1 := by omega
    subst t
    exact hz
  obtain ⟨S, T, hSs, hTs, hcover, hinter, hedges, hSc, hTc, hSC, hkeep, ⟨oS, hSface⟩, _⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG p hp hface hroot j q hq (by omega) (by omega)
      (by omega) (by omega) hInner
  let x := p.getVert (j - 1)
  let y := p.getVert 1
  have hpre : ∀ t, t ≤ j → p.getVert t ∈ (p.take j).support := by
    intro t ht
    have h := (p.take j).getVert_mem_support t
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using h
  have hxq : x ∉ q.support := by
    have hxj : x ≠ p.getVert j := hinj (j - 1) j (by omega) le_rfl (by omega)
    have hxz : x ≠ z := fun h => hz (h ▸ hf (j - 1))
    have hxa : x ≠ a := by simpa only [Walk.getVert_zero] using hinj (j - 1) 0 (by omega) (by omega) (by omega)
    simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] using ⟨hxj, hxz, hxa⟩
  have hyq : y ∉ q.support := by
    have hyj : y ≠ p.getVert j := hinj 1 j (by omega) le_rfl (by omega)
    have hyz : y ≠ z := fun h => hz (h ▸ hf 1)
    have hya : y ≠ a := by simpa only [Walk.getVert_zero] using hinj 1 0 (by omega) (by omega) (by omega)
    simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] using ⟨hyj, hyz, hya⟩
  have hxa : G.Adj x (p.getVert j) := by
    have h := p.adj_getVert_succ (by omega : j - 1 < p.length)
    simpa only [x, Nat.sub_add_cancel (by omega : 1 ≤ j)] using h
  have hay : G.Adj a y := by
    simpa only [y, Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hArcSub : cycleInterval (walkCycleVertices p) 1 (j - 2) ⊆ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := hs
    exact ⟨t, by omega, hts⟩
  have hPT : ∀ s ∈ I.precolor.vertices, s ∈ T := fun s hs => hkeep s (I.on_outer s hs)
    (fun h => hPoutside s hs (hArcSub h))
  have hOld : ∀ s : S, OnOuterFace I.embedding I.outer s.1 → s.1 ∈ (p.take j).support ∨ s.1 ∈ q.support := by
    intro s hs
    by_cases hsA : s.1 ∈ cycleInterval (walkCycleVertices p) 1 (j - 2)
    · obtain ⟨t, ht, hts⟩ := hsA
      have hts' : p.getVert (1 + t) = s.1 := by
        rwa [walkCycleVertices_nat_le p (by omega : 1 + t ≤ p.length)] at hts
      exact Or.inl (hts' ▸ hpre (1 + t) (by omega))
    · have hst : s.1 ∈ S ∩ T := ⟨s.2, hkeep s.1 hs hsA⟩
      rw [hinter] at hst
      exact Or.inr hst
  apply I.colourable_of_two_path_optional_short_ends S T q hq (by omega) (by omega) hxa hay hxq hyq
    (hSC x (Or.inl (hpre (j - 1) (by omega)))) (hSC y (Or.inl (hpre 1 (by omega))))
    hcover hinter hedges hTc hPT oS ?_ ?_ ?_ hSs hTs hsmall
  · intro s hs
    apply (hSface s).2
    rcases hs with hs | hs | hs
    · exact Or.inr hs
    · exact Or.inl (hs ▸ hpre (j - 1) (by omega))
    · exact Or.inl (hs ▸ hpre 1 (by omega))
  · intro s hs
    apply I.interior_lists
    intro hsOld
    exact hs ((hSface s).2 (hOld s hsOld))
  · intro s hsS hsq hsx hsy hss t ht hst
    have hsface : OnOuterFace I.embedding I.outer s := by
      by_contra h
      have h3 := I.interior_lists s h
      omega
    have hsArc : s ∈ cycleInterval (walkCycleVertices p) 1 (j - 2) := by
      by_contra h
      have hsST : s ∈ S ∩ T := ⟨hsS, hkeep s hsface h⟩
      rw [hinter] at hsST
      exact hsq hsST
    obtain ⟨k, hk, hks⟩ := hsArc
    have hks' : p.getVert (1 + k) = s := by rwa [walkCycleVertices_nat_le p (by omega : 1 + k ≤ p.length)] at hks
    have ht' : t = p.getVert j ∨ t = z ∨ t = a := by
      simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using ht
    rcases ht' with htj | htz | hta
    · have ha := chordless_cycle_prefix_adjacent_indices p hp hch (1 + k) j (by omega) (by omega)
        (by rw [hks']; simpa only [htj] using hst)
      have hkval : 1 + k = j - 1 := by omega
      exact hsx (by rw [← hks', hkval])
    · exact hmin (1 + k) (by omega) (by omega) (by rw [hks']; simpa only [htz] using hst.symm)
    · have ha := chordless_cycle_prefix_adjacent_indices p hp hch (1 + k) 0 (by omega) (by omega)
        (by simpa only [hks', Walk.getVert_zero, hta] using hst)
      have hkval : 1 + k = 1 := by omega
      exact hsy (by rw [← hks', hkval])

/-- Any remaining interior two-edge path must cut through the prescription
on the chosen facial arc. The entire prescription-free case is closed. -/
lemma interior_two_path_arc_meets_prescription_of_minimal_counterexample (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (z : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n)) :
    ∃ x ∈ I.precolor.vertices, x ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
  by_contra h
  push Not at h
  exact hbad (I.colourable_of_interior_two_path_free_arc hG p hp hch hface hroot n hn hnp z hz hza hzn h hsmall)

end Thomassen.BoundaryInstance
