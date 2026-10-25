/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ExceptionalPairDeletion

/-! The predecessor assertion in original proof step (9). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Rebase the exceptional edge as positions 1,2, with the distinguished
endpoint at position 2. The predecessor of position 0 must be short in a
minimal counterexample. Otherwise deleting just the exceptional edge leaves
independent residual short vertices and all residual components extend. -/
theorem predecessor_mem_short_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) :
    p.getVert (p.length-1) ∈ I.short := by
  by_contra hprev
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  let x := p.getVert 2
  let y := p.getVert 1
  have hxy : G.Adj x y := (p.adj_getVert_succ (by omega : 1 < p.length)).symm
  have hNoY : ∀ z ∈ I.short, z ≠ x → z ≠ y → ∀ w, w ≠ x → w ≠ y → G.Adj y w → G.Adj w z → False := by
    intro z hz hzx hzy w hwx _hyw hyw hwz
    by_cases hwface : OnOuterFace I.embedding I.outer w
    · have hwverts := (hverts w).2 hwface
      rcases chordless_native_cycle_vertex_neighbours p hp hch 1 (by omega) (by omega) hwverts hyw with hw | hw
      · have hwa : w=a := by simpa only [Nat.sub_self,Walk.getVert_zero] using hw
        have hzverts := (hverts z).2 (I.on_outer z hz)
        rcases chordless_native_cycle_root_neighbours p hp hch hzverts (hwa ▸ hwz) with hz | hz
        · exact hzy hz
        · exact hprev (hz ▸ ‹z ∈ I.short›)
      · exact hwx hw
    · exact I.no_interior_two_path_of_minimal_counterexample hbad hsmall y z w hyA
        (I.on_outer z hz) hzy.symm hwface hyw.symm hwz
  obtain ⟨hxa,hxb,hya,hyb,hax,hbx,hay,hby,_⟩ := exceptional_counterexample_no_short_outer_bridge
    I.embedding I.outer hG I.girth I.short I.on_outer x y hxA hyA hxy hedge hNoX
    I.lists I.list_two I.list_three I.a I.b I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne hbad
  obtain ⟨ty,hty⟩ := Finset.card_pos.1 (show 0 < (I.lists y).card by have := I.list_two y; omega)
  obtain ⟨tx,htx,htxy⟩ := Finset.exists_mem_ne (s := I.lists x) (by have := I.list_two x; omega) ty
  let f : V → C := fun z => if z=y then ty else tx
  have hfy : f y = ty := ite_eq_left rfl
  have hfx : f x = tx := ite_eq_right hxy.ne
  let D : Finset V := {x,y}
  let A : Set V := {z | z ∉ D ∧ (z ∈ I.short ∨ G.Adj x z ∨ G.Adj y z)}
  have hne : ∀ z, z ∉ D → z ≠ x ∧ z ≠ y := by
    intro z hz
    simpa only [D,Finset.mem_insert,Finset.mem_singleton,not_or] using hz
  have hf : ∀ z ∈ D, f z ∈ I.lists z := by
    intro z hz
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [hfx]; exact htx
    · rw [hfy]; exact hty
  have hproper : ∀ z ∈ D, ∀ w ∈ D, G.Adj z w → f z ≠ f w := by
    intro z hz w hw hzw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hz hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    · exact (hzw.ne rfl).elim
    · rw [hfx,hfy]; exact htxy
    · rw [hfy,hfx]; exact htxy.symm
    · exact (hzw.ne rfl).elim
  have haD : I.a ∉ D := by simp [D,hxa.symm,hya.symm]
  have hbD : I.b ∉ D := by simp [D,hxb.symm,hyb.symm]
  have hshape : OriginalShortSet (G.induce (↑D : Set V)ᶜ) {z | z.1 ∈ A} := by
    left
    intro z hz w hw hzw
    exact exceptional_pair_short_vertices_independent I.girth I.short x y hxy hedge hNoX hNoY
      (hne z.1 hz.1).1 (hne z.1 hz.1).2 (hne w.1 hw.1).1 (hne w.1 hw.1).2 hz.2 hw.2 hzw
  have htwo : ∀ z, z ∉ D → 2 ≤ (residual G I.lists D f z).card := by
    intro z hz
    exact exceptional_pair_residual_card_ge_two I.girth I.short x y hxA hyA hxy hedge
      I.lists I.list_two I.list_three f (hne z hz).1 (hne z hz).2
  have hthree : ∀ z, z ∉ D → z ∉ A → 3 ≤ (residual G I.lists D f z).card := by
    intro z hzD hzA
    have hnold : z ∉ I.short := fun h => hzA ⟨hzD,Or.inl h⟩
    have hnx : ¬ G.Adj x z := fun h => hzA ⟨hzD,Or.inr (Or.inl h)⟩
    have hny : ¬ G.Adj y z := fun h => hzA ⟨hzD,Or.inr (Or.inr h)⟩
    have heq : residual G I.lists D f z = I.lists z := by
      apply residual_unchanged
      intro w hw hzw
      simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hnx hzw.symm
      · exact hny hzw.symm
    rw [heq]
    exact I.list_three z hnold
  have hta : I.ta ∈ residual G I.lists D f I.a := by
    apply (mem_residual_iff I.lists D f I.a I.ta).2
    refine ⟨I.ta_mem,?_⟩
    intro w hw haw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hax haw).elim
    · exact (hay haw).elim
  have htb : I.tb ∈ residual G I.lists D f I.b := by
    apply (mem_residual_iff I.lists D f I.b I.tb).2
    refine ⟨I.tb_mem,?_⟩
    intro w hw hbw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hbx hbw).elim
    · exact (hby hbw).elim
  have hDconn : ConnSet G (↑D : Set V) := by
    let r : G.Walk x y := .cons hxy .nil
    have heq : (↑D : Set V) = {z | z ∈ r.support} := by ext z; simp [D,r]
    rw [heq]
    exact walk_support_connSet r
  obtain ⟨q,hq,_,_,hqface,hqroot⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot 1 (by omega)
  apply hbad
  apply I.extends_of_connected_boundary_deletion hG q hq hqface hqroot D
    (by simp [D,y]) hDconn f hf hproper haD hbD A hshape ?_ htwo hthree hta htb hsmall
  intro z hz
  rcases hz.2 with hzold | hzx | hzy
  · exact Or.inl hzold
  · exact Or.inr ⟨x,by simp [D],hzx.symm⟩
  · exact Or.inr ⟨y,by simp [D],hzy.symm⟩

end Thomassen.OriginalBoundaryInstance
