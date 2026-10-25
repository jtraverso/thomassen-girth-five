/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanChoice

/-! Closing mixed cuts through central prescribed-path vertices. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A mixed cut with at most three prescribed vertices in one piece is closed
by the complete anchored-fan theorem. The other piece supplies the actual
separator colour; all old prescribed colours are retained on both sides. -/
theorem colourable_of_mixed_two_edge_branch_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (_ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    {d : V} (q : G.Walk a d) (hq : q.length ≤ 2)
    (hcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have haST : a ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hbST : b ∈ S ∩ T := by rw [hinter]; exact Or.inr rfl
  have haS := haST.1
  have haT := haST.2
  have hbS := hbST.1
  have hbT := hbST.2
  let : Nontrivial S := (show (G.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ from hab).nontrivial
  let : Nontrivial T := (show (G.induce T).Adj ⟨a, haT⟩ ⟨b, hbT⟩ from hab).nontrivial
  obtain ⟨QS, hSv, hSe⟩ := exists_induce_path_two_cut I.precolor p hp hn hP haS haP b hbP
    (edge_cut_side_constancy S T a b hinter hedges)
  obtain ⟨QT, hTv, hTe⟩ := exists_induce_path_two_cut I.precolor p hp hn hP haT haP b hbP
    (edge_cut_side_constancy T S a b (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm))
  let JS := I.inducePrecolor S hSc.preconnected QS hSv hSe
  have hcard : JS.precolor.vertices.card ≤ 3 := by
    have hsub : QS.vertices.image Subtype.val ⊆ q.support.toFinset := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact List.mem_toFinset.2 (hcap y.1 y.2 ((hSv y).1 hy))
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
    have hqcard := List.toFinset_card_le q.support
    have hqlen := q.length_support
    change QS.vertices.card ≤ 3
    omega
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.inducePrecolor T hTc.preconnected QT hTv hTe) hTsmall
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by simpa only [inducePrecolor] using hcT
  have haJS : (⟨a, haS⟩ : S) ∈ JS.precolor.vertices := (hSv _).2 haP
  have hbJS : (⟨b, hbS⟩ : S) ∉ JS.precolor.vertices := fun h => hbP ((hSv _).1 h)
  obtain ⟨s, t, r, hr, hrn, hrP, hrlen⟩ := JS.exists_short_prescribed_path hcard ⟨⟨a, haS⟩, haJS⟩
  have hrverts : ∀ x : S, x ∈ JS.precolor.vertices ↔ x ∈ r.support := by
    simp only [hrP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hca : cT ⟨a, haT⟩ = I.prescribed a := Finset.mem_singleton.1
    (by simpa only [I.singleton a haP] using hT ⟨a, haT⟩)
  have havoid : ∀ x ∈ JS.precolor.vertices, (G.induce S).Adj ⟨b, hbS⟩ x → JS.prescribed x ≠ cT ⟨b, hbT⟩ := by
    intro x hxP hbx
    have hxa : x = ⟨a, haS⟩ := external_short_path_neighbour_unique JS.girth r hr hrlen
      ((hrverts _).1 haJS) (fun h => hbJS ((hrverts _).2 h)) hab.symm ((hrverts x).1 hxP) hbx
    subst x
    change I.prescribed a ≠ cT ⟨b, hbT⟩
    rw [← hca]
    exact cT.valid hab
  obtain ⟨f, hfb, hf, hproper⟩ := JS.exists_rootStar_colours_avoiding_precolor ⟨b, hbS⟩ (cT ⟨b, hbT⟩) (hT _) havoid
  have hbface : OnOuterFace JS.embedding JS.outer ⟨b, hbS⟩ :=
    (exists_outer_induced_of_preconnected I.embedding I.outer S hSc.preconnected).choose_spec _ hb
  obtain ⟨cS, hcS, hgS⟩ := JS.anchoredFan_extension_of_smaller (Nat.card V) hsmall hcard ⟨b, hbS⟩ hbJS
    ⟨⟨a, haS⟩, haJS, hab.symm⟩ hSc.preconnected hbface f hf hproper hSsmall
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := hcS
  have hcb : cS ⟨b, hbS⟩ = cT ⟨b, hbT⟩ := (hgS _ (Or.inl rfl)).trans hfb
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have hx := Set.mem_univ x
    rwa [← hcover] at hx
  · intro x hxS hxT
    have h : x ∈ S ∩ T := ⟨hxS, hxT⟩
    rw [hinter] at h
    rcases h with hxa | h
    · subst x
      have hsa : cS ⟨a, hxS⟩ = I.prescribed a := Finset.mem_singleton.1
        (by simpa only [I.singleton a haP] using hS ⟨a, hxS⟩)
      exact hsa.trans hca.symm
    · have hxb := Set.mem_singleton_iff.1 h
      subst x
      exact hcb

/-- Every mixed edge cut is closed: a path on at most six vertices has a
branch of at most two edges at the prescribed separator vertex. -/
theorem colourable_of_mixed_prescription_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have haST : a ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hverts : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hap := (hverts a).1 haP
  let l := (p.takeUntil a hap).reverse
  let r := p.dropUntil a hap
  have hl : l.IsPath := (hp.takeUntil hap).reverse
  have hr : r.IsPath := hp.dropUntil hap
  have heq := p.take_spec hap
  have hsupport : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ l.support ∨ x ∈ r.support := by
    intro x
    rw [hverts, ← heq, Walk.mem_support_append_iff]
    simp only [l, Walk.support_reverse, List.mem_reverse, r]
  have hsum : l.length + r.length = p.length := by
    simp only [l, r, Walk.length_reverse]
    rw [← Walk.length_append, heq]
  have hlen : p.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hn
    omega
  have hlength : l.length ≤ 2 ∨ r.length ≤ 2 := by omega
  have hbl : b ∉ l.support := fun h => hbP ((hsupport b).2 (Or.inl h))
  have hbr : b ∉ r.support := fun h => hbP ((hsupport b).2 (Or.inr h))
  have hS : ∀ {d : V} (q : G.Walk a d), q.length ≤ 2 →
      (∀ x ∈ q.support, x ∈ I.precolor.vertices) →
      (∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support) → ListColourable G I.lists := by
    intro d q hq _ hcap
    exact I.colourable_of_mixed_two_edge_branch_cut S T a b hab ha hb haP hbP p hp hn hP q hq hcap
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  have hT : ∀ {d : V} (q : G.Walk a d), q.length ≤ 2 →
      (∀ x ∈ q.support, x ∈ I.precolor.vertices) →
      (∀ x ∈ T, x ∈ I.precolor.vertices → x ∈ q.support) → ListColourable G I.lists := by
    intro d q hq _ hcap
    exact I.colourable_of_mixed_two_edge_branch_cut T S a b hab ha hb haP hbP p hp hn hP q hq hcap
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm)
      hTc hSc hTsmall hSsmall hsmall
  have hpoint (U : Set V) (h : ∀ x ∈ U, x ∈ I.precolor.vertices → x = a) :
      ∀ x ∈ U, x ∈ I.precolor.vertices → x ∈ (Walk.nil (G := G) (u := a)).support := by
    intro x hx hxP
    simpa only [Walk.support_nil, List.mem_singleton] using h x hx hxP
  have hnil : ∀ x ∈ (Walk.nil (G := G) (u := a)).support, x ∈ I.precolor.vertices := by
    intro x hx
    have hxa : x = a := by simpa only [Walk.support_nil, List.mem_singleton] using hx
    exact hxa ▸ haP
  have hsplit : ∀ {d e : V} (q : G.Walk a d) (s : G.Walk a e),
      (q.length ≤ 2 ∨ s.length ≤ 2) →
      (∀ x, x ∈ I.precolor.vertices ↔ x ∈ q.support ∨ x ∈ s.support) →
      (∀ x ∈ q.support, x ∈ S) → (∀ x ∈ s.support, x ∈ S ↔ x = a) → ListColourable G I.lists := by
    intro d e q s hlen hPqs hqS hsS
    by_cases hq : q.length ≤ 2
    · apply hS q hq (fun x hx => (hPqs x).2 (Or.inl hx))
      intro x hx hxP
      rcases (hPqs x).1 hxP with hxq | hxs
      · exact hxq
      · exact (hsS x hxs).1 hx ▸ q.start_mem_support
    · apply hT s (hlen.resolve_left hq) (fun x hx => (hPqs x).2 (Or.inr hx))
      intro x hx hxP
      rcases (hPqs x).1 hxP with hxq | hxs
      · have hxST : x ∈ S ∩ T := ⟨hqS x hxq, hx⟩
        rw [hinter] at hxST
        rcases hxST with rfl | hxb
        · exact s.start_mem_support
        · exact (hbP (Set.mem_singleton_iff.1 hxb ▸ hxP)).elim
      · exact hxs
  have hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S) :=
    edge_cut_side_constancy S T a b hinter hedges
  rcases path_side_dichotomy_avoiding_other_separator haST.1 hsep l hl hbl with hlS | hlS <;>
    rcases path_side_dichotomy_avoiding_other_separator haST.1 hsep r hr hbr with hrS | hrS
  · apply hT .nil (by simp) hnil (hpoint T ?_)
    intro x hx hxP
    have hxS := ((hsupport x).1 hxP).elim (hlS x) (hrS x)
    have hxST : x ∈ S ∩ T := ⟨hxS, hx⟩
    rw [hinter] at hxST
    exact hxST.elim id (fun h => (hbP (Set.mem_singleton_iff.1 h ▸ hxP)).elim)
  · exact hsplit l r hlength hsupport hlS hrS
  · apply hsplit r l hlength.symm (fun x => (hsupport x).trans or_comm) hrS hlS
  · apply hS .nil (by simp) hnil (hpoint S ?_)
    intro x hx hxP
    exact ((hsupport x).1 hxP).elim (fun h => (hlS x h).1 hx) (fun h => (hrS x h).1 hx)


end BoundaryInstance
end Thomassen
