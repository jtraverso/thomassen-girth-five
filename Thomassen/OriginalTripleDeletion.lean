/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalShortSetObstruction

/-! The actual coloured triple deletion starting original proof step (10). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.OriginalBoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Delete positions 0,1,2 with actual allowed proper colours, choosing the
first colour outside the predecessor's two-list. Every old short list is
preserved and every residual list has size at least two. Thus in a minimal
counterexample the exposed residual short set fails the original condition.
This is a proved invalidity conclusion, not an assumption of residual failure. -/
theorem triple_residual_short_set_not_original (I : OriginalBoundaryInstance G C)
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
    ¬ OriginalShortSet (G.induce (↑({a,p.getVert 1,p.getVert 2} : Finset V) : Set V)ᶜ)
      {z | z.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}} := by
  let D : Finset V := {a,p.getVert 1,p.getVert 2}
  change ¬ OriginalShortSet (G.induce (↑D : Set V)ᶜ) {z | z.1 ∈ exposedShortSet G I.short D}
  intro hshape
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  have hverts := native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have h01 : G.Adj a (p.getVert 1) := by
    simpa only [Walk.getVert_zero,zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
  have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega : 1 < p.length)
  have h0x : a ≠ p.getVert 2 := by
    intro he
    have hidx := hp.getVert_injOn' (show 0 ≤ p.length-1 from by omega)
      (show 2 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using he)
    omega
  have h0A : a ∉ I.short := by
    intro haA
    rcases hedge a haA (p.getVert 1) hyA h01 with h | h
    · exact h0x h.1
    · exact h01.ne h.1
  have h0three := I.list_three a h0A
  obtain ⟨c0,hc0,hc0t⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (I.lists (p.getVert (p.length-1))).card < (I.lists a).card by omega)
  obtain ⟨c1,hc1,hc10⟩ := Finset.exists_mem_ne (s := I.lists (p.getVert 1))
    (by have := I.list_two (p.getVert 1); omega) c0
  obtain ⟨c2,hc2,hc21⟩ := Finset.exists_mem_ne (s := I.lists (p.getVert 2))
    (by have := I.list_two (p.getVert 2); omega) c1
  let f : V → C := fun z => if z=a then c0 else if z=p.getVert 1 then c1 else c2
  have hf0 : f a=c0 := by simp [f]
  have hf1 : f (p.getVert 1)=c1 := by simp [f,h01.ne.symm]
  have hf2 : f (p.getVert 2)=c2 := by simp [f,h0x.symm,h12.ne.symm]
  have hne : ∀ z, z ∉ D → z ≠ a ∧ z ≠ p.getVert 1 ∧ z ≠ p.getVert 2 := by
    intro z hz
    simpa only [D,Finset.mem_insert,Finset.mem_singleton,not_or] using hz
  have hf : ∀ z ∈ D, f z ∈ I.lists z := by
    intro z hz
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rw [hf0]; exact hc0
    · rw [hf1]; exact hc1
    · rw [hf2]; exact hc2
  have hproper : ∀ z ∈ D, ∀ w ∈ D, G.Adj z w → f z ≠ f w := by
    intro z hz w hw hzw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hz hw
    rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact (hzw.ne rfl).elim
    · rw [hf0,hf1]; exact hc10.symm
    · exact (neighbors_nonadjacent I.girth h01.symm h12 hzw).elim
    · rw [hf1,hf0]; exact hc10
    · exact (hzw.ne rfl).elim
    · rw [hf1,hf2]; exact hc21.symm
    · exact (neighbors_nonadjacent I.girth h01.symm h12 hzw.symm).elim
    · rw [hf2,hf1]; exact hc21
    · exact (hzw.ne rfl).elim
  have hold : ∀ z, z ∉ D → z ∈ I.short → residual G I.lists D f z=I.lists z := by
    intro z hzD hzA
    ext c
    rw [mem_residual_iff]
    refine ⟨And.left,?_⟩
    intro hc
    refine ⟨hc,?_⟩
    intro w hw hzw he
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · subst w
      rw [hf0] at he
      rcases chordless_native_cycle_root_neighbours p hp hch ((hverts z).2 (I.on_outer z hzA)) hzw.symm with hz | hz
      · exact (hne z hzD).2.1 hz
      · exact hc0t (hz ▸ (he ▸ hc))
    · subst w
      rcases hedge z hzA (p.getVert 1) hyA hzw with h | h
      · exact (hne z hzD).2.2 h.1
      · exact (hne z hzD).2.1 h.1
    · subst w
      rcases hedge z hzA (p.getVert 2) hxA hzw with h | h
      · exact (hne z hzD).2.2 h.1
      · exact (hne z hzD).2.1 h.1
  have htwo : ∀ z, z ∉ D → 2 ≤ (residual G I.lists D f z).card := by
    intro z hz
    by_cases hzA : z ∈ I.short
    · rw [hold z hz hzA]; exact I.list_two z
    · exact residual_two_edge_path_card_ge_two I.girth h01 h12 h0x (hne z hz).2.1
        I.lists f (I.list_three z hzA)
  have hthree : ∀ z, z ∉ D → z ∉ exposedShortSet G I.short D →
      3 ≤ (residual G I.lists D f z).card := by
    intro z hzD hzA
    have hzold : z ∉ I.short := fun h => hzA ⟨hzD,Or.inl h⟩
    have heq : residual G I.lists D f z=I.lists z := residual_unchanged I.lists D f z
      (fun w hw hzw => hzA ⟨hzD,Or.inr ⟨w,hw,hzw⟩⟩)
    rw [heq]
    exact I.list_three z hzold
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  obtain ⟨hxa,hxb,hya,hyb,hax,hbx,hay,hby,_,_,_,hBr⟩ := exceptional_counterexample_no_short_outer_bridge
    I.embedding I.outer hG I.girth I.short I.on_outer (p.getVert 2) (p.getVert 1) hxA hyA h12.symm hedge hNoX
    I.lists I.list_two I.list_three I.a I.b I.edge I.a_outer I.b_outer
    I.ta I.tb I.ta_mem I.tb_mem I.colours_ne hbad
  have h0face : OnOuterFace I.embedding I.outer a := (hverts a).1 p.start_mem_support
  have hna0 : ¬ G.Adj I.a a := fun h => (hBr a h0face).2.2.1 ⟨h,h01⟩
  have hnb0 : ¬ G.Adj I.b a := fun h => (hBr a h0face).2.2.2 ⟨h,h01⟩
  have h0a : a ≠ I.a := fun h => hay (h ▸ h01)
  have h0b : a ≠ I.b := fun h => hby (h ▸ h01)
  have haD : I.a ∉ D := by simp [D,h0a.symm,hya.symm,hxa.symm]
  have hbD : I.b ∉ D := by simp [D,h0b.symm,hyb.symm,hxb.symm]
  have hta : I.ta ∈ residual G I.lists D f I.a := by
    apply (mem_residual_iff I.lists D f I.a I.ta).2
    refine ⟨I.ta_mem,?_⟩
    intro w hw haw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hna0 haw).elim
    · exact (hay haw).elim
    · exact (hax haw).elim
  have htb : I.tb ∈ residual G I.lists D f I.b := by
    apply (mem_residual_iff I.lists D f I.b I.tb).2
    refine ⟨I.tb_mem,?_⟩
    intro w hw hbw
    simp only [D,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hnb0 hbw).elim
    · exact (hby hbw).elim
    · exact (hbx hbw).elim
  have hDconn : ConnSet G (↑D : Set V) := by
    let r : G.Walk a (p.getVert 2) := .cons h01 (.cons h12 .nil)
    have heq : (↑D : Set V) = {z | z ∈ r.support} := by ext z; simp [D,r]
    rw [heq]
    exact walk_support_connSet r
  exact hbad (I.extends_of_connected_boundary_deletion hG p hp hface hroot D (by simp [D]) hDconn
    f hf hproper haD hbD (exposedShortSet G I.short D) hshape (fun _ hz => hz.2)
    htwo hthree hta htb hsmall)

/-- The full first residual obstruction in original step (10): one unique
new short edge, its interior second endpoint, degree two at the old middle
vertex, and a two-path obstruction from each of the two new endpoints. The
residual vertex type excludes the deleted vertices in all of these paths. -/
theorem triple_residual_edge_and_endpoint_obstructions (I : OriginalBoundaryInstance G C)
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
    let A : Set Q := {z | z.1 ∈ exposedShortSet G I.short D}
    ∃ q₁ q₂ : Q, q₁ ∈ A ∧ q₂ ∈ A ∧ (G.induce Q).Adj q₁ q₂ ∧
      q₁.1 ∉ I.short ∧ q₂.1 ∉ I.short ∧ ¬ OnOuterFace I.embedding I.outer q₂.1 ∧
      G.Adj (p.getVert 2) q₁.1 ∧ G.Adj q₂.1 a ∧
      (∀ r ∈ A, ∀ s ∈ A, (G.induce Q).Adj r s →
        (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁)) ∧
      (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) ∧
      (∃ z ∈ A, q₁ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₁ w ∧ (G.induce Q).Adj w z) ∧
      (∃ z ∈ A, q₂ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₂ w ∧ (G.induce Q).Adj w z) := by
  let D : Finset V := {a,p.getVert 1,p.getVert 2}
  let Q : Set V := (↑D : Set V)ᶜ
  let A : Set Q := {z | z.1 ∈ exposedShortSet G I.short D}
  have hnot : ¬ OriginalShortSet (G.induce Q) A := I.triple_residual_short_set_not_original
    hbad hsmall p hp hch hface hroot hyA hxA htcard hedge hNoX
  have htA : p.getVert (p.length-1) ∈ I.short :=
    I.mem_short_of_list_card_le_two (by omega)
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth _ p hp
  obtain ⟨hG,_⟩ := I.minimal_counterexample_has_chordless_native_face_cycle hbad hsmall
  have key : ∀ (q₁ q₂ : Q), q₁ ∈ A → q₂ ∈ A → (G.induce Q).Adj q₁ q₂ →
      G.Adj (p.getVert 2) q₁.1 → G.Adj q₂.1 a → ¬ OnOuterFace I.embedding I.outer q₂.1 →
      ∃ q₁ q₂ : Q, q₁ ∈ A ∧ q₂ ∈ A ∧ (G.induce Q).Adj q₁ q₂ ∧
        q₁.1 ∉ I.short ∧ q₂.1 ∉ I.short ∧ ¬ OnOuterFace I.embedding I.outer q₂.1 ∧
        G.Adj (p.getVert 2) q₁.1 ∧ G.Adj q₂.1 a ∧
        (∀ r ∈ A, ∀ s ∈ A, (G.induce Q).Adj r s →
          (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁)) ∧
        (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) ∧
        (∃ z ∈ A, q₁ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₁ w ∧ (G.induce Q).Adj w z) ∧
        (∃ z ∈ A, q₂ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₂ w ∧ (G.induce Q).Adj w z) := by
    intro q₁ q₂ hq₁ hq₂ hqq h2q hqa hq2inner
    obtain ⟨hq₁new,hq₂new,_⟩ := I.triple_short_edge_crossing hbad hsmall p hp hch hface hroot
      hyA hxA htA hedge hNoX hq₁ hq₂ hqq
    have hUnique : ∀ r ∈ A, ∀ s ∈ A, (G.induce Q).Adj r s →
        (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁) := by
      intro r hr s hs hrs
      rcases I.triple_short_edge_unique hbad hsmall p hp hch hface hroot hyA hxA htA hedge hNoX
          hq₁ hq₂ h2q hqq hqa r.1 hr s.1 hs hrs with h | h
      · exact Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩
      · exact Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩
    have hq1ne : q₁.1 ≠ p.getVert 1 := by
      intro h
      exact q₁.2 (by simp [D,h])
    have hMiddle : ∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2 := by
      by_cases hq1face : OnOuterFace I.embedding I.outer q₁.1
      · exact (I.boundary_three_path_first_vertex hG p hp hch hface hroot hlen q₁.1 q₂.1
          hq1face hq1ne hq2inner h2q hqq hqa hbad hsmall).2.2
      · exact I.middle_vertex_of_interior_three_path_neighbours hG p hp hface hroot (by omega)
          q₁.1 q₂.1 hq1face hq2inner h2q hqq hqa hbad hsmall
    obtain ⟨hO₁,hO₂⟩ := OriginalShortSet.endpoint_obstructions A hnot q₁ q₂ hq₁ hq₂ hqq hUnique
    exact ⟨q₁,q₂,hq₁,hq₂,hqq,hq₁new,hq₂new,hq2inner,h2q,hqa,hUnique,hMiddle,hO₁,hO₂⟩
  obtain ⟨u,hu,v,hv,huv⟩ := OriginalShortSet.exists_edge_of_not A hnot
  obtain ⟨_,_,h | h⟩ := I.triple_short_edge_crossing hbad hsmall p hp hch hface hroot
    hyA hxA htA hedge hNoX hu hv huv
  · exact key u v hu hv huv h.1 h.2.1.symm h.2.2
  · exact key v u hv hu huv.symm h.2.1 h.1.symm h.2.2

end Thomassen.OriginalBoundaryInstance
