/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFinalShortSets

/-! Choose the actual final-cut side retaining the fixed edge and old exception. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} [Fintype V]

/-- The two final paths share their interior and their far endpoint. One of
the two actual cuts keeps the old exceptional vertices and the fixed edge on
the first side. The second side has an actual face containing its old outer
vertices and separator. Both applications of induction are strictly smaller. -/
theorem final_cut_choice (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (n : ℕ) (hn : 5 ≤ n) (hnp : n+2 ≤ p.length)
    (q₀ : G.Walk (p.getVert n) a) (hq₀ : q₀.IsPath)
    (q₃ : G.Walk (p.getVert n) (p.getVert 3)) (hq₃ : q₃.IsPath)
    (hl₀ : 0 < q₀.length) (hb₀ : q₀.length ≤ 3)
    (hl₃ : 0 < q₃.length) (hb₃ : q₃.length ≤ 3)
    (hi₀ : ∀ j, 0 < j → j < q₀.length → ¬ OnOuterFace M outer (q₀.getVert j))
    (hi₃ : ∀ j, 0 < j → j < q₃.length → ¬ OnOuterFace M outer (q₃.getVert j))
    (H : Set V) (hs₀ : {x | x ∈ q₀.support} = {a} ∪ H)
    (hs₃ : {x | x ∈ q₃.support} = {p.getVert 3} ∪ H)
    (hH : ∀ x ∈ H, OnOuterFace M outer x → x=p.getVert n)
    (u v : V) (hu : OnOuterFace M outer u) (hv : OnOuterFace M outer v) (huv : G.Adj u v) :
    ∃ S T : Set V, ∃ s : V, (s=a ∨ s=p.getVert 3) ∧
      Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {s} ∪ H ∧
      (∀ {x y}, G.Adj x y → (x∈S ∧ y∈S) ∨ (x∈T ∧ y∈T)) ∧
      (G.induce S).Preconnected ∧ u∈S ∧ v∈S ∧
      p.getVert 1 ∉ T ∧ p.getVert 2 ∉ T ∧
      ∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ {s} ∪ H → OnOuterFace N o x := by
  have hlen : 5 ≤ p.length := by omega
  let : NeZero p.length := ⟨by omega⟩
  have houter := native_facial_cycle_vertices_on_outer M outer p hp hface hroot
  have hEqIndex : ∀ i j, i < p.length → j < p.length → p.getVert i=p.getVert j → i=j := by
    intro i j hi hj he
    exact hp.getVert_injOn' (show i ≤ p.length-1 by omega) (show j ≤ p.length-1 by omega) he
  have hgetS : ∀ k, k ≤ n → p.getVert k ∈ (p.take n).support := by
    intro k hk
    have h := (p.take n).getVert_mem_support k
    rwa [Walk.take_getVert,Nat.min_eq_right hk] at h
  have h0not (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 2) : p.getVert k ∉ {a} ∪ H := by
    intro h
    rcases h with h | h
    · have he : p.getVert k=p.getVert 0 := by simpa only [Set.mem_singleton_iff,Walk.getVert_zero] using h
      have := hEqIndex k 0 (by omega) (by omega) he
      omega
    · have he := hH _ h (houter _ (p.getVert_mem_support k))
      have := hEqIndex k n (by omega) (by omega) he
      omega
  obtain ⟨S₀,T₀,hS₀,hT₀,hcover₀,hinter₀,hedges₀,hSc₀,hTc₀,hkeepS₀,_,_,⟨N₀,o₀,hface₀⟩⟩ :=
    interior_face_path_cut M outer hg hG p hp hface hroot n q₀ hq₀ (by omega) hnp hl₀ hb₀ hi₀
  have hT₀omit (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 2) : p.getVert k ∉ T₀ := by
    intro hkT
    have hmem : p.getVert k ∈ S₀ ∩ T₀ := ⟨hkeepS₀ _ (Or.inl (hgetS k (by omega))),hkT⟩
    rw [hinter₀,hs₀] at hmem
    exact h0not k hk hmem
  rcases hedges₀ huv with hfixed | hfixed
  · refine ⟨S₀,T₀,a,Or.inl rfl,hS₀,hT₀,hcover₀,?_,hedges₀,hSc₀.preconnected,
      hfixed.1,hfixed.2,hT₀omit 1 (by omega),hT₀omit 2 (by omega),N₀,o₀,?_⟩
    · exact hinter₀.trans hs₀
    · intro x hx
      exact hface₀ x (hx.imp_right (fun h => by change x.1 ∈ {y | y∈q₀.support}; rw [hs₀]; exact h))
  · obtain ⟨r,hr,hrl,horder,hrface,hrroot⟩ :=
      exists_rebased_native_face_cycle M outer p hp hface hroot 3 (by omega)
    have hrn : r.getVert (n-3)=p.getVert n := by
      rw [horder (n-3) (by omega),show 3+(n-3)=n by omega,walkCycleVertices_nat_le p (by omega)]
    let q := q₃.copy hrn.symm rfl
    have hq : q.IsPath := (Walk.isPath_copy _ _ _).2 hq₃
    have hqs : {x | x∈q.support} = {p.getVert 3} ∪ H := by
      simpa only [q,Walk.support_copy] using hs₃
    have hArc : ∀ x, x∈cycleInterval (walkCycleVertices r) 1 (n-3-2) →
        ∃ i, 4 ≤ i ∧ i < n ∧ p.getVert i=x := by
      intro x hx
      obtain ⟨j,hj,hjx⟩ := hx
      have hjx' : p.getVert (4+j)=x := by
        rw [walkCycleVertices_nat_le r (by omega),horder (1+j) (by omega),
          walkCycleVertices_nat_le p (by omega)] at hjx
        simpa only [show 3+(1+j)=4+j by omega] using hjx
      exact ⟨4+j,by omega,by omega,hjx'⟩
    have hArcNotSep : ∀ x, x∈cycleInterval (walkCycleVertices r) 1 (n-3-2) → x∉{a} ∪ H := by
      intro x hx
      obtain ⟨i,hi,hin,hix⟩ := hArc x hx
      intro hsep
      rcases hsep with hxa | hxH
      · have he : p.getVert i=p.getVert 0 := by simpa only [Walk.getVert_zero] using hix.trans (Set.mem_singleton_iff.1 hxa)
        have := hEqIndex i 0 (by omega) (by omega) he
        omega
      · have he := hH x hxH (hix ▸ houter _ (p.getVert_mem_support i))
        have := hEqIndex i n (by omega) (by omega) (hix.trans he)
        omega
    have hfixedFree : ∀ x, x∈T₀ → x∉cycleInterval (walkCycleVertices r) 1 (n-3-2) := by
      intro x hxT hxArc
      obtain ⟨i,_,hin,hix⟩ := hArc x hxArc
      have hxS : x∈S₀ := hkeepS₀ x (Or.inl (hix ▸ hgetS i (by omega)))
      have hmem : x∈S₀∩T₀ := ⟨hxS,hxT⟩
      rw [hinter₀,hs₀] at hmem
      exact hArcNotSep x hxArc hmem
    obtain ⟨S₃,T₃,hS₃,hT₃,hcover₃,hinter₃,hedges₃,hSc₃,hTc₃,_,hkeepT₃,⟨o₃,hfaceS₃⟩,_⟩ :=
      interior_face_path_cut M outer hg hG r hr hrface hrroot (n-3) q hq (by omega) (by omega)
        (by simpa only [q,Walk.length_copy] using hl₃) (by simpa only [q,Walk.length_copy] using hb₃)
        (by simpa only [q,Walk.length_copy,Walk.getVert_copy] using hi₃)
    have hS₃omit (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 2) : p.getVert k ∉ S₃ := by
      intro hkS
      have hkArc : p.getVert k ∉ cycleInterval (walkCycleVertices r) 1 (n-3-2) := by
        intro hkArc
        obtain ⟨i,hi,hin,hik⟩ := hArc _ hkArc
        have := hEqIndex i k (by omega) (by omega) hik
        omega
      have hkT := hkeepT₃ _ (houter _ (p.getVert_mem_support k)) hkArc
      have hmem : p.getVert k ∈ S₃ ∩ T₃ := ⟨hkS,hkT⟩
      rw [hinter₃,hqs] at hmem
      rcases hmem with hmem | hmem
      · have he := hEqIndex k 3 (by omega) (by omega) (Set.mem_singleton_iff.1 hmem)
        omega
      · exact h0not k hk (Or.inr hmem)
    refine ⟨T₃,S₃,p.getVert 3,Or.inr rfl,hT₃,hS₃,?_,?_,?_,hTc₃.preconnected,
      hkeepT₃ u hu (hfixedFree u hfixed.1),hkeepT₃ v hv (hfixedFree v hfixed.2),
      hS₃omit 1 (by omega),hS₃omit 2 (by omega),inducedPlaneMap M S₃,o₃,?_⟩
    · rwa [Set.union_comm]
    · rw [Set.inter_comm,hinter₃,hqs]
    · intro x y hxy
      exact (hedges₃ hxy).symm
    · intro x hx
      apply (hfaceS₃ x).2
      rcases hx with hx | hx
      · by_cases hxArc : x.1 ∈ cycleInterval (walkCycleVertices r) 1 (n-3-2)
        · left
          obtain ⟨j,hj,hjx⟩ := hxArc
          rw [walkCycleVertices_nat_le r (by omega)] at hjx
          have hmem := (r.take (n-3)).getVert_mem_support (1+j)
          rwa [Walk.take_getVert,Nat.min_eq_right (by omega),hjx] at hmem
        · right
          have hxT := hkeepT₃ x.1 hx hxArc
          have hmem : x.1∈S₃∩T₃ := ⟨x.2,hxT⟩
          rwa [hinter₃] at hmem
      · right
        change x.1∈{y | y∈q.support}
        rwa [hqs]

end Thomassen
