/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalPinnedEndpoint
public import Thomassen.SmallColourCore

/-! The disjoint but adjacent-edge case of the original exceptional alternative. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- If the fixed edge and the exceptional two-list edge are joined by an edge,
their four vertices form an induced path. Its proper colours and independent
short pendant neighbours give a bounded connected prescription. -/
theorem original_theorem_2_1_exceptional_adjacent
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hbx : G.Adj b x) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  let p : G.Walk a y := .cons hab (.cons hbx (.cons hxy .nil))
  have hp : p.IsPath := by
    simp [p,Walk.isPath_def,hab.ne,hxy.ne,hxa,hxb,hya,hyb,Ne.symm]
  let B : Finset V := {a,b,x,y}
  have hBsup : ∀ z, z ∈ B ↔ z ∈ p.support := by simp [B,p]
  have hconn : ConnSet G (↑B : Set V) := by
    have heq : (↑B : Set V) = {z | z ∈ p.support} := Set.ext hBsup
    rw [heq]
    exact walk_support_connSet p
  obtain ⟨tx,htx,htxb⟩ := Finset.exists_mem_ne (s := L x) (by have := hLtwo x; omega) tb
  obtain ⟨ty,hty,htyx⟩ := Finset.exists_mem_ne (s := L y) (by have := hLtwo y; omega) tx
  let f : V → C := fun z => if z = a then ta else if z = b then tb else if z = x then tx else ty
  have hfa : f a = ta := by simp [f]
  have hfb : f b = tb := by simp [f,hab.ne.symm]
  have hfx : f x = tx := by simp [f,hxa,hxb]
  have hfy : f y = ty := by simp [f,hya,hyb,hxy.ne.symm]
  have hf : ∀ z ∈ B, f z ∈ L z := by
    intro z hz
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hfa]; exact hta
    · rw [hfb]; exact htb
    · rw [hfx]; exact htx
    · rw [hfy]; exact hty
  have hproper : ∀ z ∈ B, ∀ w ∈ B, G.Adj z w → f z ≠ f w := by
    have hch := short_path_isChordless hg p hp (by simp [p])
    have hstep : ∀ i, i < p.length → f (p.getVert i) ≠ f (p.getVert (i+1)) := by
      intro i hi
      have hil : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [p,Walk.length_cons,Walk.length_nil] at hi; omega
      rcases hil with rfl | rfl | rfl
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfa,hfb] using htab
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfb,hfx] using htxb.symm
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfx,hfy] using htyx.symm
    intro z hz w hw hzw
    obtain ⟨i,hi,he⟩ := p.mk_mem_edges_iff_exists.1
      (hch.mem_edges ((hBsup z).1 hz) ((hBsup w).1 hw) hzw)
    rcases Sym2.eq_iff.1 he with he | he
    · simpa only [he.1,he.2] using hstep i hi
    · simpa only [he.1,he.2] using (hstep i hi).symm
  have hshortA : ∀ z, (L z).card ≤ 2 → z ∈ A := by
    intro z hz
    by_contra hn
    have := hLthree z hn
    omega
  have hBface : ∀ z ∈ B, OnOuterFace M outer z := by
    intro z hz
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hAface _ hxA
    · exact hAface _ hyA
  have hshortedge : ∀ {z w}, G.Adj z w → (L z).card ≤ 2 → (L w).card ≤ 2 → z ∈ B ∧ w ∈ B := by
    intro z w hzw hz hw
    rcases hedge z (hshortA z hz) w (hshortA w hw) hzw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [B]
  have hunique : ∀ z, z ∉ B → (L z).card ≤ 2 → ∀ r ∈ B, ∀ s ∈ B,
      G.Adj z r → G.Adj z s → r = s := by
    have hne : ∀ z, z ∉ B → (L z).card ≤ 2 → ¬ G.Adj z x ∧ ¬ G.Adj z y := by
      intro z hz hzs
      constructor
      · intro hzx
        rcases hedge z (hshortA z hzs) x hxA hzx with h | h
        · exact hz (by simp [B,h.1])
        · exact hz (by simp [B,h.1])
      · intro hzy
        rcases hedge z (hshortA z hzs) y hyA hzy with h | h
        · exact hz (by simp [B,h.1])
        · exact hz (by simp [B,h.1])
    intro z hz hzs r hr s hs hzr hzs'
    have hrab : r = a ∨ r = b := by
      simp only [B,Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact ((hne z hz hzs).1 (h ▸ hzr)).elim
      · exact ((hne z hz hzs).2 (h ▸ hzr)).elim
    have hsab : s = a ∨ s = b := by
      simp only [B,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact ((hne z hz hzs).1 (h ▸ hzs')).elim
      · exact ((hne z hz hzs).2 (h ▸ hzs')).elim
    rcases hrab with rfl | rfl <;> rcases hsab with rfl | rfl
    · rfl
    · exact (neighbors_nonadjacent hg hzr hzs' hab).elim
    · exact (neighbors_nonadjacent hg hzs' hzr hab).elim
    · rfl
  obtain ⟨c,hc,hfixed⟩ := extend_small_colour_core M outer hg L hLtwo
    (fun z hz => hLthree z (fun h => hz (hAface z h))) B
    (by simpa only [B] using (Finset.card_le_four (a := a) (b := b) (c := x) (d := y)))
    hconn hBface hshortedge hunique f hf hproper
  exact ⟨c,hc,(hfixed a (by simp [B])).trans hfa,(hfixed b (by simp [B])).trans hfb⟩

end Thomassen
