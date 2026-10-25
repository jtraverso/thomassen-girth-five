/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalAdjacentException
public import Thomassen.ExceptionalListNormalization

/-! A two-edge outer bridge to the distinguished exceptional endpoint. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- All four orientations of a joining edge between the prescribed and
exceptional edges reduce to the proved induced four-vertex-path case. -/
theorem original_theorem_2_1_exceptional_joined
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
    (hjoin : G.Adj a x ∨ G.Adj b x ∨ G.Adj a y ∨ G.Adj b y) :
    ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb := by
  have hedge' : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = y ∧ s = x) ∨ (r = x ∧ s = y) := by
    intro r hr s hs hrs
    exact (hedge r hr s hs hrs).symm
  rcases hjoin with h | h | h | h
  · obtain ⟨c,hc,hcb,hca⟩ := original_theorem_2_1_exceptional_adjacent M outer hg A hAface
      x y hxA hyA hxy hedge L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm
      hxb hxa hyb hya h
    exact ⟨c,hc,hca,hcb⟩
  · exact original_theorem_2_1_exceptional_adjacent M outer hg A hAface
      x y hxA hyA hxy hedge L hLtwo hLthree a b hab ha hb ta tb hta htb htab
      hxa hxb hya hyb h
  · obtain ⟨c,hc,hcb,hca⟩ := original_theorem_2_1_exceptional_adjacent M outer hg A hAface
      y x hyA hxA hxy.symm hedge' L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm
      hyb hya hxb hxa h
    exact ⟨c,hc,hca,hcb⟩
  · exact original_theorem_2_1_exceptional_adjacent M outer hg A hAface
      y x hyA hxA hxy.symm hedge' L hLtwo hLthree a b hab ha hb ta tb hta htb htab
      hya hyb hxa hxb h

/-- The separated exceptional edge extends when the distinguished endpoint is
joined to an endpoint of the prescribed edge by a two-edge path on the same
face. The intermediate vertex is not assumed to have degree two. In fact, this
case needs no distinguished-endpoint two-path exclusion. -/
theorem original_theorem_2_1_exceptional_boundary_bridge
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ t ∈ A, OnOuterFace M outer t)
    (x y : V) (hxA : x ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ t, 2 ≤ (L t).card)
    (hLthree : ∀ t, t ∉ A → 3 ≤ (L t).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hay : ¬ G.Adj a y) (hby : ¬ G.Adj b y)
    (hax : ¬ G.Adj a x)
    (z : V) (hz : OnOuterFace M outer z) (hbz : G.Adj b z) (hzx : G.Adj z x) :
    ∃ c : G.Coloring C, (∀ t, c t ∈ L t) ∧ c a = ta ∧ c b = tb := by
  have hza : z ≠ a := fun h => hax (h ▸ hzx)
  let p : G.Walk a x := .cons hab (.cons hbz (.cons hzx .nil))
  have hp : p.IsPath := by
    simp [p,Walk.isPath_def,hab.ne,hbz.ne,hzx.ne,hxa,hxb,hza,Ne.symm]
  let B : Finset V := {a,b,z,x}
  have hBsup : ∀ t, t ∈ B ↔ t ∈ p.support := by simp [B,p]
  have hconn : ConnSet G (↑B : Set V) := by
    rw [show (↑B : Set V) = {t | t ∈ p.support} from Set.ext hBsup]
    exact walk_support_connSet p
  obtain ⟨tz,htz,htzb⟩ := Finset.exists_mem_ne (s := L z) (by have := hLtwo z; omega) tb
  obtain ⟨tx,htx,htxz⟩ := Finset.exists_mem_ne (s := L x) (by have := hLtwo x; omega) tz
  let f : V → C := fun t => if t = a then ta else if t = b then tb else if t = z then tz else tx
  have hfa : f a = ta := by simp [f]
  have hfb : f b = tb := by simp [f,hab.ne.symm]
  have hfz : f z = tz := by simp [f,hza,hbz.ne.symm]
  have hfx : f x = tx := by simp [f,hxa,hxb,hzx.ne.symm]
  have hf : ∀ t ∈ B, f t ∈ L t := by
    intro t ht
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [hfa]; exact hta
    · rw [hfb]; exact htb
    · rw [hfz]; exact htz
    · rw [hfx]; exact htx
  have hproper : ∀ r ∈ B, ∀ s ∈ B, G.Adj r s → f r ≠ f s := by
    have hch := short_path_isChordless hg p hp (by simp [p])
    have hstep : ∀ i, i < p.length → f (p.getVert i) ≠ f (p.getVert (i+1)) := by
      intro i hi
      have hil : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases hil with rfl | rfl | rfl
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfa,hfb] using htab
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfb,hfz] using htzb.symm
      · simpa only [p,Walk.getVert_zero,Walk.getVert_cons_succ,hfz,hfx] using htxz.symm
    intro r hr s hs hrs
    obtain ⟨i,hi,he⟩ := p.mk_mem_edges_iff_exists.1
      (hch.mem_edges ((hBsup r).1 hr) ((hBsup s).1 hs) hrs)
    rcases Sym2.eq_iff.1 he with he | he
    · simpa only [he.1,he.2] using hstep i hi
    · simpa only [he.1,he.2] using (hstep i hi).symm
  have hshortA : ∀ t, (L t).card ≤ 2 → t ∈ A := by
    intro t ht
    by_contra hn
    have := hLthree t hn
    omega
  have hcover : ∀ {r s}, G.Adj r s → (L r).card ≤ 2 → (L s).card ≤ 2 → r ∈ B ∨ s ∈ B := by
    intro r s hrs hr hs
    rcases hedge r (hshortA r hr) s (hshortA s hs) hrs with h | h
    · exact Or.inl (by simp [B,h.1])
    · exact Or.inr (by simp [B,h.2])
  have hunique : ∀ t, t ∉ B → (L t).card ≤ 2 → ∀ r ∈ B, ∀ s ∈ B,
      G.Adj t r → G.Adj t s → r = s := by
    intro t ht hts r hr s hs htr hts'
    have htx : t ≠ x := fun h => ht (by simp [B,h])
    by_cases hty : t = y
    · have htz' : ¬ G.Adj t z := by
        intro h
        exact neighbors_nonadjacent hg hxy hzx.symm (hty ▸ h)
      have hparent : ∀ r ∈ B, G.Adj t r → r = x := by
        intro r hr htr
        simp only [B,Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | hr
        · exact (hay (hty ▸ htr.symm)).elim
        · exact (hby (hty ▸ htr.symm)).elim
        · exact (htz' htr).elim
        · exact hr
      exact (hparent r hr htr).trans (hparent s hs hts').symm
    · have htx' : ¬ G.Adj t x := by
        intro h
        rcases hedge t (hshortA t hts) x hxA h with h | h
        · exact htx h.1
        · exact hty h.1
      have hparent : ∀ r ∈ B, G.Adj t r → r ∈ ({a,b,z} : Finset V) := by
        intro r hr htr
        simp only [B,Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with h | h | rfl | rfl
        · simp [h]
        · simp [h]
        · simp
        · exact (htx' htr).elim
      have htb : t ≠ b := fun h => ht (by simp [B,h])
      have hcard := neighbors_in_two_edge_path_card_le_one hg hab hbz hza.symm htb
      exact (Finset.card_le_one.1 hcard)
        r (Finset.mem_filter.2 ⟨hparent r hr htr,htr⟩)
        s (Finset.mem_filter.2 ⟨hparent s hs hts',hts'⟩)
  have hBface : ∀ t ∈ B, OnOuterFace M outer t := by
    intro t ht
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hz
    · exact hAface _ hxA
  obtain ⟨c,hc,hfixed⟩ := extend_small_colour_core_of_short_edges_covered M outer hg L hLtwo
    (fun t ht => hLthree t (fun h => ht (hAface t h))) B
    (by simpa only [B] using (Finset.card_le_four (a := a) (b := b) (c := z) (d := x)))
    hconn hBface hcover hunique f hf hproper
  exact ⟨c,hc,(hfixed a (by simp [B])).trans hfa,(hfixed b (by simp [B])).trans hfb⟩

/-- An uncoloured connected instance must have identical two-element lists
at two endpoints disjoint from, and with no edges to, the prescribed edge.
There is also no two-edge bridge to either exceptional endpoint whose middle
vertex lies on the selected face. This is a necessary condition on a possible
counterexample, not an existence assertion or the full Theorem 2.1. -/
theorem exceptional_counterexample_no_short_outer_bridge
    (M : PlaneMap G) (outer : G.Dart) (hG : G.Preconnected) (hg : 5 ≤ G.egirth)
    (A : Set V) (hAface : ∀ z ∈ A, OnOuterFace M outer z)
    (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNo : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card)
    (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace M outer a) (hb : OnOuterFace M outer b)
    (ta tb : C) (hta : ta ∈ L a) (htb : tb ∈ L b) (htab : ta ≠ tb)
    (hbad : ¬ ∃ c : G.Coloring C, (∀ z, c z ∈ L z) ∧ c a = ta ∧ c b = tb) :
    x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      ¬ G.Adj a x ∧ ¬ G.Adj b x ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y ∧
      (L x).card = 2 ∧ (L y).card = 2 ∧ L x = L y ∧
      (∀ z, OnOuterFace M outer z →
        ¬ (G.Adj a z ∧ G.Adj z x) ∧ ¬ (G.Adj b z ∧ G.Adj z x) ∧
        ¬ (G.Adj a z ∧ G.Adj z y) ∧ ¬ (G.Adj b z ∧ G.Adj z y)) := by
  let : Fintype V := Fintype.ofFinite V
  have hdisjoint : ¬ (x = a ∨ y = a ∨ x = b ∨ y = b) := fun h => hbad
    (original_theorem_2_1_exceptional_incident M outer hg A hAface x y hedge L hLtwo hLthree
      a b hab ha hb ta tb hta htb htab h)
  have hxa : x ≠ a := fun h => hdisjoint (Or.inl h)
  have hxb : x ≠ b := fun h => hdisjoint (Or.inr (Or.inr (Or.inl h)))
  have hya : y ≠ a := fun h => hdisjoint (Or.inr (Or.inl h))
  have hyb : y ≠ b := fun h => hdisjoint (Or.inr (Or.inr (Or.inr h)))
  have hjoin : ¬ (G.Adj a x ∨ G.Adj b x ∨ G.Adj a y ∨ G.Adj b y) := fun h => hbad
    (original_theorem_2_1_exceptional_joined M outer hg A hAface x y hxA hyA hxy hedge
      L hLtwo hLthree a b hab ha hb ta tb hta htb htab hxa hxb hya hyb h)
  have hax : ¬ G.Adj a x := fun h => hjoin (Or.inl h)
  have hbx : ¬ G.Adj b x := fun h => hjoin (Or.inr (Or.inl h))
  have hay : ¬ G.Adj a y := fun h => hjoin (Or.inr (Or.inr (Or.inl h)))
  have hby : ¬ G.Adj b y := fun h => hjoin (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨hx2,hy2,heq⟩ := exceptional_counterexample_endpoint_lists_equal_two M outer hG hg
    A hAface x y hxA hedge hNo L hLtwo hLthree a b hab ha hb ta tb hta htb htab
    hxa hxb hax hbx hbad
  refine ⟨hxa,hxb,hya,hyb,hax,hbx,hay,hby,hx2,hy2,heq,?_⟩
  have hedge' : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = y ∧ s = x) ∨ (r = x ∧ s = y) := by
    intro r hr s hs hrs
    exact (hedge r hr s hs hrs).symm
  intro z hz
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨haz,hzx⟩
    obtain ⟨c,hc,hcb,hca⟩ := original_theorem_2_1_exceptional_boundary_bridge M outer hg
      A hAface x y hxA hxy hedge L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm
      hxb hxa hby hay hbx z hz haz hzx
    exact hbad ⟨c,hc,hca,hcb⟩
  · rintro ⟨hbz,hzx⟩
    exact hbad (original_theorem_2_1_exceptional_boundary_bridge M outer hg
      A hAface x y hxA hxy hedge L hLtwo hLthree a b hab ha hb ta tb hta htb htab
      hxa hxb hay hby hax z hz hbz hzx)
  · rintro ⟨haz,hzy⟩
    obtain ⟨c,hc,hcb,hca⟩ := original_theorem_2_1_exceptional_boundary_bridge M outer hg
      A hAface y x hyA hxy.symm hedge' L hLtwo hLthree b a hab.symm hb ha tb ta htb hta htab.symm
      hyb hya hbx hax hby z hz haz hzy
    exact hbad ⟨c,hc,hca,hcb⟩
  · rintro ⟨hbz,hzy⟩
    exact hbad (original_theorem_2_1_exceptional_boundary_bridge M outer hg
      A hAface y x hyA hxy.symm hedge' L hLtwo hLthree a b hab ha hb ta tb hta htb htab
      hya hyb hax hbx hay z hz hbz hzy)

end Thomassen
