/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InteriorTwoPathSubarc

/-! Prescription-free three-edge interior paths with a short endpoint. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A three-edge interior path cutting off a prescription-free facial arc is
closed when its initial boundary endpoint has a short list. Two-path reductions
exclude interior incidences; the actual boundary captures the only possible
additional short endpoint neighbour. No capture hypothesis is supplied. -/
theorem colourable_of_interior_three_path_free_arc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists a).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hf : ∀ t, OnOuterFace I.embedding I.outer (p.getVert t) := fun t =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support t)
  have hinj : ∀ s t : ℕ, s ≤ n → t ≤ n → s ≠ t → p.getVert s ≠ p.getVert t := by
    intro s t hs ht hst heq
    exact hst (hp.getVert_injOn' (show s ∈ {i | i ≤ p.length - 1} from by change s ≤ p.length - 1; omega)
      (show t ∈ {i | i ≤ p.length - 1} from by change t ≤ p.length - 1; omega) heq)
  have hna : p.getVert n ≠ a := by simpa only [Walk.getVert_zero] using hinj n 0 le_rfl (by omega) (by omega)
  have hnu : p.getVert n ≠ u := fun h => hu (h ▸ hf n)
  have hva : v ≠ a := fun h => hv (by simpa only [Walk.getVert_zero, ← h] using hf 0)
  let q : G.Walk (p.getVert n) a := .cons hvn.symm (.cons huv.symm (.cons hua .nil))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, or_false, not_or, and_true, not_false_eq_true]
    exact ⟨⟨hvn.ne.symm, hnu, hna⟩, ⟨⟨huv.ne.symm, hva⟩, hua.ne⟩⟩
  have hqlen : q.length = 3 := rfl
  have hInner : ∀ t, 0 < t → t < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert t) := by
    intro t ht htl
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
    · exact hv
    · exact hu
  obtain ⟨S, T, hSs, hTs, hcover, hinter, hedges, _, hTc, hSC, hkeep, ⟨oS, hSface⟩, _⟩ :=
    interior_face_path_cut I.embedding I.outer I.girth hG p hp hface hroot n q hq hn hnp
      (by omega) (by omega) hInner
  let x := p.getVert (n - 1)
  have hpre : ∀ t, t ≤ n → p.getVert t ∈ (p.take n).support := by
    intro t ht
    have h := (p.take n).getVert_mem_support t
    simpa only [Walk.take_getVert, Nat.min_eq_right ht] using h
  have hxq : x ∉ q.support := by
    have hxn : x ≠ p.getVert n := hinj (n - 1) n (by omega) le_rfl (by omega)
    have hxv : x ≠ v := fun h => hv (h ▸ hf (n - 1))
    have hxu : x ≠ u := fun h => hu (h ▸ hf (n - 1))
    have hxa : x ≠ a := by simpa only [Walk.getVert_zero] using hinj (n - 1) 0 (by omega) (by omega) (by omega)
    simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] using
      ⟨hxn, hxv, hxu, hxa⟩
  have hxn : G.Adj x (p.getVert n) := by
    have h := p.adj_getVert_succ (by omega : n - 1 < p.length)
    simpa only [x, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hPT : ∀ s ∈ I.precolor.vertices, s ∈ T := fun s hs => hkeep s (I.on_outer s hs) (hPoutside s hs)
  have hOld : ∀ s : S, OnOuterFace I.embedding I.outer s.1 → s.1 ∈ (p.take n).support ∨ s.1 ∈ q.support := by
    intro s hs
    by_cases hsA : s.1 ∈ cycleInterval (walkCycleVertices p) 1 (n - 2)
    · obtain ⟨t, ht, hts⟩ := hsA
      have hts' : p.getVert (1 + t) = s.1 := by
        rwa [walkCycleVertices_nat_le p (by omega : 1 + t ≤ p.length)] at hts
      exact Or.inl (hts' ▸ hpre (1 + t) (by omega))
    · have hst : s.1 ∈ S ∩ T := ⟨s.2, hkeep s.1 hs hsA⟩
      rw [hinter] at hst
      exact Or.inr hst
  have hfaceS : ∀ s : S, s.1 ∈ q.support ∨ s.1 = x → OnOuterFace (inducedPlaneMap I.embedding S) oS s := by
    intro s hs
    apply (hSface s).2
    exact hs.elim Or.inr (fun h => Or.inl (h ▸ hpre (n - 1) (by omega)))
  have hInterior : ∀ s : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS s → 3 ≤ (I.lists s.1).card := by
    intro s hs
    apply I.interior_lists
    intro hsOld
    exact hs ((hSface s).2 (hOld s hsOld))
  have hCapture : ∀ s ∈ S, s ∉ q.support → s ≠ x → (I.lists s).card ≤ 2 → ∀ t ∈ q.support, ¬ G.Adj s t := by
    intro s hsS hsq hsx hss t ht hst
    have hsface : OnOuterFace I.embedding I.outer s := by
      by_contra h
      have h3 := I.interior_lists s h
      omega
    have hsArc : s ∈ cycleInterval (walkCycleVertices p) 1 (n - 2) := by
      by_contra h
      have hsST : s ∈ S ∩ T := ⟨hsS, hkeep s hsface h⟩
      rw [hinter] at hsST
      exact hsq hsST
    obtain ⟨k, hk, hks⟩ := hsArc
    have hks' : p.getVert (1 + k) = s := by rwa [walkCycleVertices_nat_le p (by omega : 1 + k ≤ p.length)] at hks
    have ht' : t = p.getVert n ∨ t = v ∨ t = u ∨ t = a := by
      simpa only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] using ht
    rcases ht' with htn | htv | htu | hta
    · have ha := chordless_cycle_prefix_adjacent_indices p hp hch (1 + k) n (by omega) (by omega)
        (by rw [hks']; simpa only [htn] using hst)
      have hkval : 1 + k = n - 1 := by omega
      exact hsx (by rw [← hks', hkval])
    · have he := I.interior_neighbours_unique_on_free_arc hG p hp hface hroot hbad hsmall n hnp hPoutside v hv
        (1 + k) n (by omega) le_rfl (by rw [hks']; simpa only [htv] using hst.symm) hvn
      omega
    · have he := I.interior_neighbours_unique_on_free_arc hG p hp hface hroot hbad hsmall n hnp hPoutside u hu
        (1 + k) 0 (by omega) (by omega) (by rw [hks']; simpa only [htu] using hst.symm)
        (by simpa only [Walk.getVert_zero] using hua)
      omega
    · have hsa : G.Adj s a := by simpa only [hta] using hst
      have hsP := (I.precolor.endpoints_of_mem_edges (I.short_edges hsa hss hashort)).1
      exact hPoutside s hsP ⟨k, hk, hks⟩
  by_cases hxs : (I.lists x).card ≤ 2
  · exact hbad (I.colourable_of_short_path_with_one_short_end S T q hq (by omega) (by omega) hxn hxq
      (hSC x (Or.inl (hpre (n - 1) (by omega)))) hxs hashort hcover hinter hedges hTc hPT oS hfaceS hInterior hCapture hSs hTs hsmall)
  · apply hbad
    apply I.colourable_of_short_path_without_short_neighbours S T q hq (by omega) (by omega)
      hcover hinter hedges hTc hPT oS (fun s hs => hfaceS s (Or.inl hs)) hInterior ?_ hSs hTs hsmall
    intro s hsS hsq hss t ht
    exact hCapture s hsS hsq (fun h => hxs (h ▸ hss)) hss t ht

/-- The completed short-endpoint three-path case works on every specified
old facial subarc, with exact transport of its prescription-free condition. -/
theorem colourable_of_interior_three_path_free_subarc (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u (p.getVert s)) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists (p.getVert s)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨q, hq, hqlen, horder, hqface, hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot s (by omega)
  have hqn : q.getVert (n - s) = p.getVert n := by
    rw [horder (n - s) (by omega), Nat.add_sub_of_le (by omega : s ≤ n)]
    exact walkCycleVertices_nat_le p (by omega)
  have hPq : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices q) 1 (n - s - 2) := by
    intro x hx
    rw [rebased_native_cycleInterval p q s (n - s - 2) hqlen horder (by omega)]
    exact hPoutside x hx
  exact I.colourable_of_interior_three_path_free_arc hG q hq hqface hqroot (n - s) (by omega) (by omega)
    u v hu hv hua huv (by rwa [hqn]) hashort hPq hsmall

end Thomassen.BoundaryInstance
