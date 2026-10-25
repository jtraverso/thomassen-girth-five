/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalFirstObstruction

/-! Resolve the second endpoint obstruction in original proof step (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

omit [Fintype V] in
/-- The second residual two-path q₂-q₅-q₆ must also end at an old
short vertex. The degree-two conclusions at the two deleted exceptional
vertices and girth five exclude every newly exposed endpoint. -/
theorem second_residual_obstruction_endpoint_old (I : OriginalBoundaryInstance G C)
    {a : V} (p : G.Walk a a)
    (q₁ q₂ q₅ q₆ : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)})
    (hq₁ : q₁.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₂ : q₂.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₆ : q₆.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (h12 : G.Adj q₁.1 q₂.1) (h2a : G.Adj q₂.1 a)
    (h25 : G.Adj q₂.1 q₅.1) (h56 : G.Adj q₅.1 q₆.1) (h26 : q₂ ≠ q₆)
    (hUnique : ∀ r s : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)},
      r.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} →
      s.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} → G.Adj r.1 s.1 →
      (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁))
    (hMiddle : ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2)
    (hNext : ∀ z, G.Adj (p.getVert 2) z → z=p.getVert 1 ∨ z=q₁.1) :
    q₆.1 ∈ I.short ∧ q₅.1 ∉ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} := by
  have hne (q : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)}) :
      q.1 ≠ a ∧ q.1 ≠ p.getVert 1 ∧ q.1 ≠ p.getVert 2 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using q.2
  have hq₅out : q₅.1 ∉ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2} := by
    intro hq₅
    have h51 : q₅=q₁ := by
      rcases hUnique q₂ q₅ hq₂ hq₅ h25 with h | h
      · exact (h12.ne (congrArg Subtype.val h.1).symm).elim
      · exact h.2
    rcases hUnique q₁ q₆ hq₁ hq₆ (h51 ▸ h56) with h | h
    · exact h26 h.2.symm
    · exact (h12.ne (congrArg Subtype.val h.1)).elim
  refine ⟨?_,hq₅out⟩
  by_contra hq₆new
  obtain ⟨t,ht,h6t⟩ := hq₆.2.resolve_left hq₆new
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with ht | ht | ht
  · subst t
    have he := common_neighbor_unique I.girth (fun h => h26 (Subtype.ext h))
      h2a h6t h25 h56.symm
    exact (hne q₅).1 he.symm
  · subst t
    rcases hMiddle q₆.1 h6t.symm with h | h
    · exact (hne q₆).1 h
    · exact (hne q₆).2.2 h
  · subst t
    rcases hNext q₆.1 h6t.symm with h | h
    · exact (hne q₆).2.1 h
    · exact neighbors_nonadjacent I.girth h12.symm h25 (h ▸ h56.symm)

/-- Both endpoint obstructions in the actual three-vertex deletion reduce
to the original step-(10) final-cut configuration. The remaining path ends
at an old short vertex, and the two deleted exceptional vertices have degree
two. No residual invalidity or endpoint-location premise is assumed. -/
theorem triple_residual_final_path (I : OriginalBoundaryInstance G C)
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
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) :
    let D : Finset V := {a,p.getVert 1,p.getVert 2}
    let Q : Set V := (↑D : Set V)ᶜ
    ∃ q₁ q₂ q₅ q₆ : Q,
      q₁.1 = p.getVert 3 ∧ q₁.1 ∉ I.short ∧
      ¬ OnOuterFace I.embedding I.outer q₂.1 ∧
      q₆.1 ∈ I.short ∧ q₅.1 ∉ exposedShortSet G I.short D ∧
      G.Adj (p.getVert 2) q₁.1 ∧ G.Adj q₁.1 q₂.1 ∧ G.Adj q₂.1 a ∧
      G.Adj q₂.1 q₅.1 ∧ G.Adj q₅.1 q₆.1 ∧ q₂ ≠ q₆ ∧
      (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) ∧
      (∀ z, G.Adj (p.getVert 2) z → z=p.getVert 1 ∨ z=q₁.1) ∧
      p.getVert 5 ∈ I.short := by
  obtain ⟨q₁,q₂,hq₁,hq₂,h12,hq₁new,hq₂new,hq₂inner,h2q,h2a,hUnique,hMiddle,
      ⟨q₄,hq₄,h14,q₃,h13,h34⟩,⟨q₆,hq₆,h26,q₅,h25,h56⟩⟩ :=
    I.triple_residual_edge_and_endpoint_obstructions hbad hsmall p hp hch hface hroot
      hyA hxA htcard hedge hNoX
  have hUnique' := fun r s hr hs hrs => hUnique r hr s hs hrs
  have hq₄old := I.first_residual_obstruction_endpoint_old hbad hsmall p hp hch hface hroot
    q₁ q₂ q₃ q₄ hq₁ hq₂ hq₄ hq₂new hq₂inner h2q h12 h2a h13 h34 h14 hUnique' hMiddle
  have hne (q : {q : V // q ∉ ({a,p.getVert 1,p.getVert 2} : Finset V)}) :
      q.1 ≠ a ∧ q.1 ≠ p.getVert 1 ∧ q.1 ≠ p.getVert 2 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using q.2
  obtain ⟨h1,_,h4,hNext⟩ := I.first_residual_obstruction_boundary_chain hbad hsmall
    p hp hch hface hroot hxA q₁.1 q₂.1 q₃.1 q₄.1 hq₄old hq₂inner h2q h12 h2a h13 h34
    (hne q₁).2.1 (hne q₃).2.2 (hne q₄).2.2 (fun h => h14 (Subtype.ext h))
  obtain ⟨hq₆old,hq₅out⟩ := I.second_residual_obstruction_endpoint_old p q₁ q₂ q₅ q₆ hq₁ hq₂ hq₆
    h12 h2a h25 h56 h26 hUnique' hMiddle hNext
  exact ⟨q₁,q₂,q₅,q₆,h1,hq₁new,hq₂inner,hq₆old,hq₅out,h2q,h12,h2a,h25,h56,h26,
    hMiddle,hNext,h4 ▸ hq₄old⟩

end Thomassen.OriginalBoundaryInstance
