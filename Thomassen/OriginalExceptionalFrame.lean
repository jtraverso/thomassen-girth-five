/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFinalCut

/-! Close the exceptional-edge case in the native frame of original step (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The original exceptional-edge case in its actual oriented native
frame. The residual endpoint obstructions and final cut are all proved here
under strict induction on the original invariant. -/
theorem framed_exception_contradiction (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htcard : (I.lists (p.getVert (p.length-1))).card=2)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) : False := by
  obtain ⟨q₁,q₂,q₅,q₆,h1,hq₁new,hq₂inner,hq₆old,hq₅out,h2q,h12,h2a,h25,h56,h26,_,_,h5A⟩ :=
    I.triple_residual_final_path hbad hsmall p hp hch hface hroot hyA hxA htcard hedge hNoX
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  let : NeZero p.length := ⟨by omega⟩
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hne (q : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)}) :
      q.1 ≠ a ∧ q.1 ≠ p.getVert 1 ∧ q.1 ≠ p.getVert 2 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using q.2
  have h4not : p.getVert 4 ∉ I.short := by
    intro h4A
    have h45 : G.Adj (p.getVert 4) (p.getVert 5) := p.adj_getVert_succ (by omega)
    rcases hedge _ h4A _ h5A h45 with h | h
    · have := hp.getVert_injOn' (show 4 ≤ p.length-1 by omega) (show 2 ≤ p.length-1 by omega) h.1
      omega
    · have := hp.getVert_injOn' (show 4 ≤ p.length-1 by omega) (show 1 ≤ p.length-1 by omega) h.1
      omega
  have h32 : G.Adj (p.getVert 3) q₂.1 := by simpa only [h1] using h12
  have h5ne3 : q₅.1 ≠ p.getVert 3 := by
    intro h
    exact hq₅out ⟨q₅.2,Or.inr ⟨p.getVert 2,by simp,h.symm ▸ (h1 ▸ h2q.symm)⟩⟩
  have h5ne4 : q₅.1 ≠ p.getVert 4 := by
    intro h
    exact neighbors_nonadjacent I.girth h32 (p.adj_getVert_succ (by omega : 3<p.length))
      (by simpa only [h] using h25)
  have h5a : ¬ G.Adj a q₅.1 := fun h => hq₅out ⟨q₅.2,Or.inr ⟨a,by simp,h.symm⟩⟩
  have h6ne3 : q₆.1 ≠ p.getVert 3 := fun h => hq₁new ((h.trans h1.symm) ▸ hq₆old)
  have h6ne4 : q₆.1 ≠ p.getVert 4 := fun h => h4not (h ▸ hq₆old)
  have h6a : ¬ G.Adj a q₆.1 := by
    intro h
    have he := common_neighbor_unique I.girth (fun he => h26 (Subtype.ext he)) h2a h.symm h25 h56.symm
    exact (hne q₅).1 he.symm
  have hindex : ∀ t, OnOuterFace I.embedding I.outer t →
      (∀ k, k ≤ 4 → t ≠ p.getVert k) → ¬ G.Adj a t →
      ∃ n, 5 ≤ n ∧ n+2 ≤ p.length ∧ p.getVert n=t := by
    intro t ht hInit hno
    obtain ⟨i,hi⟩ := (walkCycleVertices_range p hp).symm ▸
      (show t∈{z | z∈p.support} from (hverts t).2 ht)
    change p.getVert i.val=t at hi
    have hil := ZMod.val_lt i
    have hin : 5 ≤ i.val := by
      by_contra hn
      exact hInit i.val (by omega) hi.symm
    have hilast : i.val+1 ≠ p.length := by
      intro he
      have hadj := p.adj_getVert_succ hil
      rw [he,Walk.getVert_length,hi] at hadj
      exact hno hadj.symm
    exact ⟨i.val,hin,by omega,hi⟩
  have hStartAway : ∀ s, s=a ∨ s=p.getVert 3 → s≠q₂.1 ∧ s≠q₅.1 := by
    intro s hs
    rcases hs with rfl | rfl
    · exact ⟨h2a.ne.symm,(hne q₅).1.symm⟩
    · exact ⟨h32.ne,h5ne3.symm⟩
  by_cases hq₅face : OnOuterFace I.embedding I.outer q₅.1
  · have hInit : ∀ k, k ≤ 4 → q₅.1 ≠ p.getVert k := by
      intro k hk
      have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · simpa only [Walk.getVert_zero] using (hne q₅).1
      · exact (hne q₅).2.1
      · exact (hne q₅).2.2
      · exact h5ne3
      · exact h5ne4
    obtain ⟨n,hn,hnp,hnv⟩ := hindex q₅.1 hq₅face hInit h5a
    have hn2 : G.Adj (p.getVert n) q₂.1 := by simpa only [hnv] using h25.symm
    let q₀ : G.Walk (p.getVert n) a := .cons hn2 (.cons h2a .nil)
    let q₃ : G.Walk (p.getVert n) (p.getVert 3) := .cons hn2 (.cons h32.symm .nil)
    have hq₀ : q₀.IsPath := by simp [q₀,Walk.isPath_def,hnv,(hne q₅).1,h25.ne,h2a.ne,Ne.symm]
    have hq₃ : q₃.IsPath := by simp [q₃,Walk.isPath_def,hnv,h5ne3,h25.ne,h32.ne,Ne.symm]
    have hi₀ : ∀ j, 0 < j → j < q₀.length → ¬ OnOuterFace I.embedding I.outer (q₀.getVert j) := by
      intro j hj hjl
      have hj1 : j=1 := by change j<2 at hjl; omega
      subst j
      exact hq₂inner
    have hi₃ : ∀ j, 0 < j → j < q₃.length → ¬ OnOuterFace I.embedding I.outer (q₃.getVert j) := by
      intro j hj hjl
      have hj1 : j=1 := by change j<2 at hjl; omega
      subst j
      exact hq₂inner
    let H : Set V := {q₂.1,q₅.1}
    have hs₀ : {x | x∈q₀.support} = {a}∪H := by ext x; simp [q₀,H,hnv]; tauto
    have hs₃ : {x | x∈q₃.support} = {p.getVert 3}∪H := by ext x; simp [q₃,H,hnv]; tauto
    have hH : ∀ x∈H, OnOuterFace I.embedding I.outer x → x=p.getVert n := by
      intro x hx hxf
      rcases hx with hx | hx
      · exact (hq₂inner (hx ▸ hxf)).elim
      · exact (Set.mem_singleton_iff.1 hx).trans hnv.symm
    exact hbad (I.extends_of_final_cut_paths hbad hsmall p hp hch hface hroot hedge h4not n hn hnp
      q₀ hq₀ q₃ hq₃ (by change 0<2; omega) (by change 2≤3; omega)
      (by change 0<2; omega) (by change 2≤3; omega) hi₀ hi₃ H hs₀ hs₃ hH
      ∅ q₂.1 q₅.1 h25 (by simp only [Set.empty_union,H]) (by simp) (by simp) (by simp)
      hStartAway ⟨h2a.symm,h32⟩)
  · have hInit : ∀ k, k ≤ 4 → q₆.1 ≠ p.getVert k := by
      intro k hk
      have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · simpa only [Walk.getVert_zero] using (hne q₆).1
      · exact (hne q₆).2.1
      · exact (hne q₆).2.2
      · exact h6ne3
      · exact h6ne4
    obtain ⟨n,hn,hnp,hnv⟩ := hindex q₆.1 (I.on_outer q₆.1 hq₆old) hInit h6a
    have hn5 : G.Adj (p.getVert n) q₅.1 := by simpa only [hnv] using h56.symm
    have h6ne2 : q₆.1 ≠ q₂.1 := fun h => h26 (Subtype.ext h.symm)
    let q₀ : G.Walk (p.getVert n) a := .cons hn5 (.cons h25.symm (.cons h2a .nil))
    let q₃ : G.Walk (p.getVert n) (p.getVert 3) := .cons hn5 (.cons h25.symm (.cons h32.symm .nil))
    have hq₀ : q₀.IsPath := by simp [q₀,Walk.isPath_def,hnv,(hne q₆).1,(hne q₅).1,h56.ne,h25.ne,h2a.ne,h6ne2,Ne.symm]
    have hq₃ : q₃.IsPath := by simp [q₃,Walk.isPath_def,hnv,h6ne3,h5ne3,h56.ne,h25.ne,h32.ne,h6ne2,Ne.symm]
    have hi₀ : ∀ j, 0 < j → j < q₀.length → ¬ OnOuterFace I.embedding I.outer (q₀.getVert j) := by
      intro j hj hjl
      have hj12 : j=1 ∨ j=2 := by change j<3 at hjl; omega
      rcases hj12 with rfl | rfl
      · exact hq₅face
      · exact hq₂inner
    have hi₃ : ∀ j, 0 < j → j < q₃.length → ¬ OnOuterFace I.embedding I.outer (q₃.getVert j) := by
      intro j hj hjl
      have hj12 : j=1 ∨ j=2 := by change j<3 at hjl; omega
      rcases hj12 with rfl | rfl
      · exact hq₅face
      · exact hq₂inner
    let H : Set V := {q₆.1,q₂.1,q₅.1}
    have hs₀ : {x | x∈q₀.support} = {a}∪H := by ext x; simp [q₀,H,hnv]; tauto
    have hs₃ : {x | x∈q₃.support} = {p.getVert 3}∪H := by ext x; simp [q₃,H,hnv]; tauto
    have hH : ∀ x∈H, OnOuterFace I.embedding I.outer x → x=p.getVert n := by
      intro x hx hxf
      rcases hx with hx | hx | hx
      · exact hx.trans hnv.symm
      · exact (hq₂inner (hx ▸ hxf)).elim
      · exact (hq₅face ((Set.mem_singleton_iff.1 hx) ▸ hxf)).elim
    have hKaway : ∀ x∈({q₆.1} : Set V), x≠q₂.1 ∧ x≠q₅.1 := by
      intro x hx
      have hx' : x=q₆.1 := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨h6ne2,h56.ne.symm⟩
    have hKattach : ∀ x∈({q₆.1} : Set V), ∃ y, (y=q₂.1 ∨ y=q₅.1) ∧ G.Adj x y := by
      intro x hx
      have hx' : x=q₆.1 := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q₅.1,Or.inr rfl,h56.symm⟩
    exact hbad (I.extends_of_final_cut_paths hbad hsmall p hp hch hface hroot hedge h4not n hn hnp
      q₀ hq₀ q₃ hq₃ (by change 0<3; omega) (by change 3≤3; omega)
      (by change 0<3; omega) (by change 3≤3; omega) hi₀ hi₃ H hs₀ hs₃ hH
      {q₆.1} q₂.1 q₅.1 h25 (by ext x; simp only [H,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_union]) (by intro x hx; exact (Set.mem_singleton_iff.1 hx) ▸ hq₆old)
      hKaway hKattach hStartAway ⟨h2a.symm,h32⟩)

end Thomassen.OriginalBoundaryInstance
