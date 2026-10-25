/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFinalCutGeometry

/-! Restore all separator colours in the final cut of original source (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The source-(10) final cut, with an old-short far endpoint when the path
has three edges. Both possible starts are originally outer vertices, and the
actual cut chooses the side retaining the prescribed edge. All new short-set
and colour-restoration conditions are derived, rather than supplied. -/
theorem extends_of_final_cut_paths (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r=p.getVert 2 ∧ s=p.getVert 1) ∨ (r=p.getVert 1 ∧ s=p.getVert 2))
    (h4 : p.getVert 4 ∉ I.short)
    (n : ℕ) (hn : 5 ≤ n) (hnp : n+2 ≤ p.length)
    (q₀ : G.Walk (p.getVert n) a) (hq₀ : q₀.IsPath)
    (q₃ : G.Walk (p.getVert n) (p.getVert 3)) (hq₃ : q₃.IsPath)
    (hl₀ : 0 < q₀.length) (hb₀ : q₀.length ≤ 3)
    (hl₃ : 0 < q₃.length) (hb₃ : q₃.length ≤ 3)
    (hi₀ : ∀ j, 0 < j → j < q₀.length → ¬ OnOuterFace I.embedding I.outer (q₀.getVert j))
    (hi₃ : ∀ j, 0 < j → j < q₃.length → ¬ OnOuterFace I.embedding I.outer (q₃.getVert j))
    (H : Set V) (hs₀ : {x | x ∈ q₀.support} = {a} ∪ H)
    (hs₃ : {x | x ∈ q₃.support} = {p.getVert 3} ∪ H)
    (hH : ∀ x ∈ H, OnOuterFace I.embedding I.outer x → x=p.getVert n)
    (K : Set V) (v w : V) (hvw : G.Adj v w) (hHK : H=K ∪ {v,w})
    (hK : K ⊆ I.short) (hKaway : ∀ x∈K, x≠v ∧ x≠w)
    (hKattach : ∀ x∈K, ∃ y, (y=v ∨ y=w) ∧ G.Adj x y)
    (hStartAway : ∀ s, s=a ∨ s=p.getVert 3 → s≠v ∧ s≠w)
    (hStartAdj : G.Adj a v ∧ G.Adj (p.getVert 3) v) : I.Extends := by
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  obtain ⟨S,T,s,hs,hS,hT,hcover,hinter,hedges,hSc,haS,hbS,h1T,h2T,N,o,hTface⟩ :=
    final_cut_choice I.embedding I.outer I.girth hG p hp hface hroot n hn hnp q₀ hq₀ q₃ hq₃
      hl₀ hb₀ hl₃ hb₃ hi₀ hi₃ H hs₀ hs₃ hH I.a I.b I.a_outer I.b_outer I.edge
  let A : Set T := {x : T | x.1∈I.short ∨ x.1=s}
  have hAshape : OriginalShortSet (G.induce T) A := by
    rcases hs with hs | hs
    · simpa only [A,hs] using I.final_cut_predecessor_short_set hbad hsmall p hp hch hface hroot hedge T h1T h2T
    · simpa only [A,hs] using I.final_cut_next_short_set p hp hch hface hroot (by omega) h4 hedge T h1T h2T
  have hsep : S∩T=({s}∪K) ∪ {v,w} := by rw [hinter,hHK,Set.union_assoc]
  have hRaway : ∀ x∈({s}∪K : Set V), x≠v ∧ x≠w := by
    intro x hx
    rcases hx with hx | hx
    · exact Set.mem_singleton_iff.1 hx ▸ hStartAway s hs
    · exact hKaway x hx
  have hRattach : ∀ x∈({s}∪K : Set V), ∃ y, (y=v ∨ y=w) ∧ G.Adj x y := by
    intro x hx
    rcases hx with hx | hx
    · have hxs : x=s := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨v,Or.inl rfl,?_⟩
      exact hs.elim (fun h => h ▸ hStartAdj.1) (fun h => h ▸ hStartAdj.2)
    · exact hKattach x hx
  apply I.extends_of_released_leaf_edge_cut S T ({s}∪K) v w hvw hcover hsep hedges hSc haS hbS
    hRaway hRattach N o A hAshape (fun _ hx => Or.inl hx) ?_ ?_ ?_ ?_ hS hT hsmall
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inr (Set.mem_singleton_iff.1 hx)
    · exact Or.inl (hK hx)
  · intro x hx
    apply hTface x
    rcases hx with hx | hx
    · exact Or.inl (I.on_outer x.1 hx)
    · exact Or.inr (Or.inl (Set.mem_singleton_iff.2 hx))
  · intro hvT
    exact hTface ⟨v,hvT⟩ (Or.inr (Or.inr (hHK ▸ Or.inr (Or.inl rfl))))
  · intro hwT
    exact hTface ⟨w,hwT⟩ (Or.inr (Or.inr (hHK ▸ Or.inr (Or.inr rfl))))

end Thomassen.OriginalBoundaryInstance
