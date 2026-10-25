/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalExceptionalFrame

/-! Close strong induction for the full original exceptional-edge invariant. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
namespace OriginalBoundaryInstance

/-- Reversing the plane map retains exactly the original extension problem. -/
def mirror (I : OriginalBoundaryInstance G C) : OriginalBoundaryInstance G C := {
  I with
  embedding := mirrorPlaneMap I.embedding
  outer := I.outer.symm
  on_outer := fun x hx => (mirror_onOuterFace_iff I.embedding I.outer x).2 (I.on_outer x hx)
  a_outer := (mirror_onOuterFace_iff I.embedding I.outer I.a).2 I.a_outer
  b_outer := (mirror_onOuterFace_iff I.embedding I.outer I.b).2 I.b_outer }

theorem mirror_extends_iff (I : OriginalBoundaryInstance G C) :
    I.mirror.Extends ↔ I.Extends := Iff.rfl

variable [Fintype V]

/-- Every native representative of the selected face is chordless in a
minimal original counterexample, including rebased and mirrored frames. -/
theorem native_face_cycle_chordless (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp)) : p.IsChordless := by
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hf := native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot
  apply Walk.isChordless_iff_forall_mem_edges.2
  intro x y hx hy hxy
  obtain ⟨i,hi⟩ := (walkCycleVertices_range p hp).symm ▸ (show x∈{z | z∈p.support} from hx)
  obtain ⟨j,hj⟩ := (walkCycleVertices_range p hp).symm ▸ (show y∈{z | z∈p.support} from hy)
  have hcon : j=i+1 ∨ i=j+1 := by
    by_contra hn
    push Not at hn
    exact hbad (I.extends_of_boundary_chord (walk_isCycleMap p hp) hlen hface hG
      (fun i => hf _ (p.getVert_mem_support i.val)) i j (by rwa [hi,hj]) hn.1 hn.2 hsmall)
  apply (walkCycleVertices_edges p hp x y).1
  rw [← hi,← hj]
  apply (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) i _).2
  exact hcon.elim (fun h => Or.inl (congrArg (walkCycleVertices p) h))
    (fun h => Or.inr (congrArg (walkCycleVertices p) (by linear_combination -h)))

/-- Source (9) and the complete source-(10) contradiction apply to every
actual native frame placing the distinguished endpoint at position two. -/
theorem contradiction_of_framed_short_edge (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (hTwo : ∀ z∈I.short, (I.lists z).card=2)
    (x y : V) (hx : x∈I.short) (hy : y∈I.short)
    (hedge : ∀ r∈I.short, ∀ s∈I.short, G.Adj r s → (r=x ∧ s=y) ∨ (r=y ∧ s=x))
    (hNo : ∀ z∈I.short, ∀ p : G.Walk x z, p.IsPath → p.length=2 → False)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hqx : p.getVert 2=x) (hqy : p.getVert 1=y) : False := by
  have hch := I.native_face_cycle_chordless hbad hsmall p hp hface hroot
  have hxA : p.getVert 2∈I.short := by simpa only [hqx] using hx
  have hyA : p.getVert 1∈I.short := by simpa only [hqy] using hy
  have hedge' : ∀ r∈I.short, ∀ s∈I.short, G.Adj r s →
      (r=p.getVert 2 ∧ s=p.getVert 1) ∨ (r=p.getVert 1 ∧ s=p.getVert 2) := by
    simpa only [hqx,hqy] using hedge
  have hNo' : ∀ z∈I.short, ∀ q : G.Walk (p.getVert 2) z, q.IsPath → q.length=2 → False := by
    intro z hz q hq hql
    exact hNo z hz (q.copy hqx rfl) ((Walk.isPath_copy _ _ _).2 hq)
      (by simpa only [Walk.length_copy] using hql)
  have ht := I.predecessor_mem_short_of_minimal_counterexample hbad hsmall p hp hch hface hroot
    hyA hxA hedge' hNo'
  exact I.framed_exception_contradiction hbad hsmall p hp hch hface hroot hyA hxA (hTwo _ ht) hedge' hNo'

/-- Orient and rebase any actual exceptional edge, preserving its
original distinguished endpoint and all prescribed colours. -/
theorem contradiction_of_short_edge (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (hTwo : ∀ z∈I.short, (I.lists z).card=2)
    (x y : V) (hx : x∈I.short) (hy : y∈I.short) (hxy : G.Adj x y)
    (hedge : ∀ r∈I.short, ∀ s∈I.short, G.Adj r s → (r=x ∧ s=y) ∨ (r=y ∧ s=x))
    (hNo : ∀ z∈I.short, ∀ p : G.Walk x z, p.IsPath → p.length=2 → False) : False := by
  obtain ⟨p,hp,hlen,hface,hroot,hverts⟩ := I.exists_native_face_cycle_at hbad hsmall x (I.on_outer x hx)
  have hch := I.native_face_cycle_chordless hbad hsmall p hp hface hroot
  let : NeZero p.length := ⟨by omega⟩
  rcases chordless_native_cycle_root_neighbours p hp hch ((hverts y).2 (I.on_outer y hy)) hxy with hy1 | hyLast
  · obtain ⟨q,hq,hql,hqo,hqface,hqroot⟩ :=
      exists_mirrored_native_face_cycle_at I.embedding I.outer p hp hface hroot 2 (by omega)
    have hq1 : q.getVert 1=y := by
      rw [hqo 1 (by omega),Nat.cast_ofNat,Nat.cast_one,show (2:ZMod p.length)-1=1 by ring]
      have he : walkCycleVertices p 1=p.getVert 1 := by
        simpa only [Nat.cast_one] using walkCycleVertices_nat_le p (i := 1) (by omega)
      exact he.trans hy1.symm
    have hq2 : q.getVert 2=x := by
      rw [hqo 2 (by omega),sub_self]
      simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    exact I.mirror.contradiction_of_framed_short_edge hbad hsmall hTwo x y hx hy hedge hNo
      q hq hqface hqroot hq2 hq1
  · obtain ⟨q,hq,hql,hqo,hqface,hqroot⟩ :=
      exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot (p.length-2) (by omega)
    have hq1 : q.getVert 1=y := by
      rw [hqo 1 (by omega),show p.length-2+1=p.length-1 by omega,walkCycleVertices_nat_le p (by omega)]
      exact hyLast.symm
    have hq2 : q.getVert 2=x := by
      rw [hqo 2 (by omega),show p.length-2+2=p.length by omega,ZMod.natCast_self]
      simp only [walkCycleVertices,ZMod.val_zero,Walk.getVert_zero]
    exact I.contradiction_of_framed_short_edge hbad hsmall hTwo x y hx hy hedge hNo
      q hq hqface hqroot hq2 hq1

/-- One complete original-invariant induction step. Pruning marks exactly
the actual two-lists; either the independent theorem already applies or the
proved exceptional-edge contradiction closes the remaining case. -/
theorem extends_of_smaller (I : OriginalBoundaryInstance G C)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  let J := I.pruneShort
  change J.Extends
  by_contra hbad
  rcases J.short_shape with hA | ⟨x,y,hx,hy,hxy,hedge,hNo⟩
  · exact hbad (J.extends_of_independent hA)
  · exact J.contradiction_of_short_edge hbad hsmall (fun _ hz => I.pruneShort_list_card hz)
      x y hx hy hxy hedge hNo

end OriginalBoundaryInstance

/-- Strong induction for the exact original selected-face invariant. -/
theorem original_instances_extend_at_card (C : Type v) (n : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (I : OriginalBoundaryInstance G C),
      Nat.card V=n → I.Extends := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V instFinite G I hcard
    let : Fintype V := Fintype.ofFinite V
    exact I.extends_of_smaller (by
      intro W instFiniteW H J hW
      exact ih (Nat.card W) (by omega) W H J rfl)

/-- Every finite original instance extends its given two allowed colours. -/
theorem original_boundary_extension (C : Type v) (V : Type u) [Finite V]
    (G : SimpleGraph V) (I : OriginalBoundaryInstance G C) : I.Extends :=
  original_instances_extend_at_card C (Nat.card V) V G I rfl

end Thomassen
