/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedBoundaryDeletion

/-! Three-vertex deletion next to a prescribed boundary edge. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V} {a : V}

/-- At a noninitial native position, chordlessness gives the two actual
cyclic neighbours without indexing a supplied neighbour. -/
lemma chordless_native_cycle_vertex_neighbours (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (i : ℕ) (hi : 0 < i) (hil : i + 1 ≤ p.length) {y : V}
    (hy : y ∈ p.support) (hadj : G.Adj (p.getVert i) y) :
    y = p.getVert (i-1) ∨ y = p.getVert (i+1) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  have hedge := (walkCycleVertices_edges p hp _ y).2
    (hch.mem_edges (p.getVert_mem_support i) hy hadj)
  have hiCast : walkCycleVertices p (i : ZMod p.length) = p.getVert i := walkCycleVertices_nat_le p (by omega)
  rw [← hiCast] at hedge
  have hplus : walkCycleVertices p ((i : ZMod p.length)+1) = p.getVert (i+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using walkCycleVertices_nat_le p hil
  have hminus : walkCycleVertices p ((i : ZMod p.length)-1) = p.getVert (i-1) := by
    have hcast : ((i-1 : ℕ) : ZMod p.length) = (i : ZMod p.length)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [← hcast, walkCycleVertices_nat_le p (by omega)]
  rcases (cyclicSubgraph_adj_at_iff (walk_isCycleMap p hp) (i : ZMod p.length) y).1 hedge with h | h
  · exact Or.inr (h.trans hplus)
  · exact Or.inl (h.trans hminus)

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

/-- For a prescription on the first old face edge, a smallest counterexample
has no interior vertex with two distinct old boundary neighbours. The remaining
old arc is proved prescription-free by actual native rebasing. -/
lemma interior_boundary_neighbour_unique_of_prescribed_edge (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (z u w : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hu : OnOuterFace I.embedding I.outer u) (hw : OnOuterFace I.embedding I.outer w)
    (hzu : G.Adj z u) (hzw : G.Adj z w) : u = w := by
  have hlen : 5 ≤ p.length := five_le_egirth_iff.1 I.girth a p hp
  have hrootcase : ∀ y, OnOuterFace I.embedding I.outer y → y ≠ a → G.Adj z a → G.Adj z y → False := by
    intro y hy hya hza hzy
    have ha1 : G.Adj a (p.getVert 1) := by
      simpa only [Walk.getVert_zero, zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
    let r : G.Walk a (p.getVert 1) := .cons ha1 .nil
    have hr : r.IsPath := Walk.IsPath.mk' (by simp [r, ha1.ne])
    have hPv : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ r.support := by
      intro y
      simpa only [r, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] using hP y
    exact I.no_interior_two_path_from_prescribed_endpoint_to_noninternal_boundary hG p hp hface hroot hExact r hr hPv hbad hsmall
      z y hz hy hya (by intro k hk hkl; change k < 1 at hkl; omega) hza hzy
  by_cases hua : u = a
  · by_cases hwa : w = a
    · exact hua.trans hwa.symm
    · exact (hrootcase w hw hwa (by simpa only [hua] using hzu) hzw).elim
  by_cases hwa : w = a
  · exact (hrootcase u hu hua (by simpa only [hwa] using hzw) hzu).elim
  obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot 1 (by omega)
  have hqa : q.getVert (p.length-1) = a := by
    rw [hqo (p.length-1) (by omega), Nat.add_sub_of_le (by omega : 1 ≤ p.length), ZMod.natCast_self]
    simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hfree : ∀ y ∈ I.precolor.vertices, y ∉ cycleInterval (walkCycleVertices q) 1 (p.length-2-2) := by
    intro y hy hyArc
    obtain ⟨j, hj, hjy⟩ := hyArc
    have hjy' : q.getVert (1+j) = y := by rwa [walkCycleVertices_nat_le q (by omega : 1+j ≤ q.length)] at hjy
    rcases (hP y).1 hy with hya | hy1
    · have he := hq.getVert_injOn' (show 1+j ≤ q.length-1 from by omega) (show p.length-1 ≤ q.length-1 from by omega)
        (hjy'.trans (hya.trans hqa.symm))
      omega
    · have hq0 : q.getVert 0 = p.getVert 1 := Walk.getVert_zero q
      have he := hq.getVert_injOn' (show 1+j ≤ q.length-1 from by omega) (show 0 ≤ q.length-1 from Nat.zero_le _)
        (hjy'.trans (hy1.trans hq0.symm))
      omega
  have hindex : ∀ y, OnOuterFace I.embedding I.outer y → y ≠ a → ∃ i ≤ p.length-2, q.getVert i = y := by
    intro y hy hya
    obtain ⟨i, hiy, hi⟩ := Walk.mem_support_iff_exists_getVert.1 (hExact y hy)
    have hi0 : 0 < i := by
      by_contra h
      have he : i = 0 := by omega
      exact hya (by simpa only [he, Walk.getVert_zero] using hiy.symm)
    have hil : i < p.length := by
      by_contra h
      have he : i = p.length := by omega
      exact hya (by simpa only [he, Walk.getVert_length] using hiy.symm)
    refine ⟨i-1, by omega, ?_⟩
    rw [hqo (i-1) (by omega), Nat.add_sub_of_le hi0, walkCycleVertices_nat_le p (by omega)]
    exact hiy
  obtain ⟨i, hi, hiu⟩ := hindex u hu hua
  obtain ⟨j, hj, hjw⟩ := hindex w hw hwa
  have he := I.interior_neighbours_unique_on_free_arc hG q hq hqf hqr hbad hsmall (p.length-2) (by omega)
    hfree z hz i j hi hj (by rwa [hiu]) (by rwa [hjw])
  exact hiu.symm.trans (he ▸ hjw)


/-- Delete the prescribed initial vertex and its next two backward boundary
vertices. For a prescribed edge, a short second backward list and a three-list
at the fourth backward vertex suffice. Both kinds of residual short-edge
conflicts are excluded by the checked two/three-path cuts. The remainder may
have arbitrarily many components. -/
theorem colourable_of_prescribed_edge_short_second_good_fourth (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hlen : 6 ≤ p.length)
    (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  let b := p.getVert (p.length-1)
  let d := p.getVert (p.length-2)
  let e := p.getVert (p.length-3)
  let t := p.getVert 1
  let A : Finset V := {a,b,d}
  have hAmem : ∀ x, x ∈ A ↔ x = a ∨ x = b ∨ x = d := by intro x; simp only [A, Finset.mem_insert, Finset.mem_singleton]
  have hinj : ∀ i j, i < p.length → j < p.length → p.getVert i = p.getVert j → i = j := by
    intro i j hi hj he
    exact hp.getVert_injOn' (show i ≤ p.length-1 from by omega) (show j ≤ p.length-1 from by omega) he
  have hba : b ≠ a := by intro h; have := hinj (p.length-1) 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have hda : d ≠ a := by intro h; have := hinj (p.length-2) 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have hdb : d ≠ b := by intro h; have := hinj (p.length-2) (p.length-1) (by omega) (by omega) h; omega
  have hta : t ≠ a := by intro h; have := hinj 1 0 (by omega) (by omega) (by simpa only [Walk.getVert_zero] using h); omega
  have htb : t ≠ b := by intro h; have := hinj 1 (p.length-1) (by omega) (by omega) h; omega
  have htd : t ≠ d := by intro h; have := hinj 1 (p.length-2) (by omega) (by omega) h; omega
  have htA : t ∉ A := by simpa only [hAmem, not_or] using ⟨hta, htb, htd⟩
  have hbP : b ∉ I.precolor.vertices := by rw [hP]; exact fun h => h.elim hba (fun h => htb h.symm)
  have hdP : d ∉ I.precolor.vertices := by rw [hP]; exact fun h => h.elim hda (fun h => htd h.symm)
  have haP := (hP a).2 (Or.inl rfl)
  have htP := (hP t).2 (Or.inr rfl)
  have hf : ∀ i, OnOuterFace I.embedding I.outer (p.getVert i) := fun i =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support i)
  have hab : G.Adj a b := by
    have h := p.adj_getVert_succ (by omega : p.length-1 < p.length)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length), Walk.getVert_length] using h.symm
  have hbd : G.Adj b d := by
    have h := p.adj_getVert_succ (by omega : p.length-2 < p.length)
    simpa only [show p.length-2+1 = p.length-1 by omega] using h.symm
  have had : ¬ G.Adj a d := neighbors_nonadjacent I.girth hab.symm hbd
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact I.short_not_adj_precolored hbP haP (by omega) hab.symm
  have hNoTwo : ∀ z u w, ¬ OnOuterFace I.embedding I.outer z → OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer w → G.Adj z u → G.Adj z w → u = w :=
    I.interior_boundary_neighbour_unique_of_prescribed_edge hG p hp hface hroot hExact hP hbad hsmall
  have hAface : ∀ x ∈ A, OnOuterFace I.embedding I.outer x := by
    intro x hx
    rcases (hAmem x).1 hx with rfl | rfl | rfl
    · simpa only [Walk.getVert_zero] using hf 0
    · exact hf _
    · exact hf _
  have hNewFace : ∀ x, x ∉ A → OnOuterFace I.embedding I.outer x →
      (∃ u ∈ A, G.Adj u x) → x = t ∨ x = e := by
    intro x hx hxf ⟨u, hu, hux⟩
    have hxp := hExact x hxf
    rcases (hAmem u).1 hu with rfl | rfl | rfl
    · rcases chordless_native_cycle_root_neighbours p hp hch hxp hux with hx1 | hxb
      · exact Or.inl hx1
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl hxb)))).elim
    · rcases chordless_native_cycle_last_neighbours p hp hch hxp hux with hxa | hxd
      · exact (hx ((hAmem x).2 (Or.inl hxa))).elim
      · exact (hx ((hAmem x).2 (Or.inr (Or.inr hxd)))).elim
    · rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-2) (by omega) (by omega) hxp hux with hxe | hxb
      · exact Or.inr (by simpa only [show p.length-2-1 = p.length-3 by omega] using hxe)
      · exact (hx ((hAmem x).2 (Or.inr (Or.inl (by simpa only [show p.length-2+1 = p.length-1 by omega] using hxb))))).elim
  have hCross : ∀ x, x ∉ A → ¬ OnOuterFace I.embedding I.outer x →
      (∃ u ∈ A, G.Adj u x) → ∀ y, y ∉ A → OnOuterFace I.embedding I.outer y → ¬ G.Adj x y := by
    intro x _ hxi ⟨u, hu, hux⟩ y hy hyf hxy
    have he := hNoTwo x u y hxi (hAface u hu) hyf hux.symm hxy
    exact hy (he ▸ hu)
  have hNoThree : ∀ x y, ¬ OnOuterFace I.embedding I.outer x → ¬ OnOuterFace I.embedding I.outer y →
      G.Adj a x → G.Adj x y → G.Adj d y → False := by
    intro x y hxi hyi hax hxy hdy
    obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_rebased_native_face_cycle I.embedding I.outer p hp hface hroot (p.length-2) (by omega)
    have hq2 : q.getVert 2 = a := by
      rw [hqo 2 (by omega), Nat.sub_add_cancel (by omega : 2 ≤ p.length), ZMod.natCast_self]
      simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
    have hq1 : q.getVert 1 = b := by
      rw [hqo 1 (by omega), show p.length-2+1 = p.length-1 by omega, walkCycleVertices_nat_le p (by omega)]
    have hfree : ∀ u ∈ I.precolor.vertices, u ∉ cycleInterval (walkCycleVertices q) 1 (2-2) := by
      intro u hu ⟨i, hi, hiu⟩
      have hi0 : i = 0 := by omega
      have hbu : b = u := by simpa only [hi0, Nat.add_zero, Nat.cast_one,
        show walkCycleVertices q 1 = q.getVert 1 by simpa only [Nat.cast_one] using walkCycleVertices_nat_le q (i := 1) (by omega), hq1] using hiu
      exact hbP (hbu ▸ hu)
    exact hbad (I.colourable_of_interior_three_path_free_arc hG q hq hqf hqr 2 (by omega) (by omega) y x hyi hxi hdy.symm hxy.symm
      (by rw [hq2]; exact hax.symm) hsecond hfree hsmall)
  have hNoOld : ∀ x, x ∉ A → 3 ≤ (I.lists x).card → (∃ u ∈ A, G.Adj u x) →
      ∀ y, y ∉ A → (I.lists y).card ≤ 2 → ¬ G.Adj x y := by
    intro x hx hx3 hxN y hy hys hxy
    have hyf : OnOuterFace I.embedding I.outer y := by
      by_contra h
      have := I.interior_lists y h
      omega
    by_cases hxf : OnOuterFace I.embedding I.outer x
    · rcases hNewFace x hx hxf hxN with hxt | hxe
      · have hc : (I.lists x).card = 1 := by rw [hxt, I.singleton t htP]; exact Finset.card_singleton _
        omega
      · have hey : G.Adj e y := by rwa [hxe] at hxy
        rcases chordless_native_cycle_vertex_neighbours p hp hch (p.length-3) (by omega) (by omega) (hExact y hyf) hey with hy4 | hy2
        · have hc : 3 ≤ (I.lists y).card := by simpa only [show p.length-3-1 = p.length-4 by omega] using hy4 ▸ hfourth
          omega
        · exact hy ((hAmem y).2 (Or.inr (Or.inr (by simpa only [show p.length-3+1 = p.length-2 by omega] using hy2))))
    · exact hCross x hx hxf hxN y hy hyf hxy
  have hOldNoA : ∀ x, x ∉ A → x ∉ I.precolor.vertices → (I.lists x).card ≤ 2 → ∀ u ∈ A, ¬ G.Adj x u := by
    intro x hx hxP hxs u hu hxu
    have hxf : OnOuterFace I.embedding I.outer x := by
      by_contra h
      have := I.interior_lists x h
      omega
    rcases (hAmem u).1 hu with hua | hub | hud
    · rw [hua] at hxu
      exact I.short_not_adj_precolored hxP haP hxs hxu
    · rw [hub] at hxu
      rcases chordless_native_cycle_last_neighbours p hp hch (hExact x hxf) hxu.symm with hxa | hxd
      · exact hx ((hAmem x).2 (Or.inl hxa))
      · exact hx ((hAmem x).2 (Or.inr (Or.inr hxd)))
    · rw [hud] at hxu
      exact hdP (I.precolor.endpoints_of_mem_edges (I.short_edges hxu hxs hsecond)).2
  -- Only unprescribed old short lists need the unchanged-list assertion.
  obtain ⟨cd, hcd⟩ := I.list_nonempty d
  obtain ⟨cb, hcb, hcbA, hcbD⟩ : ∃ c ∈ I.lists b, c ≠ I.prescribed a ∧ c ≠ cd := by
    have hc : ({I.prescribed a, cd} : Finset C).card < (I.lists b).card := Finset.card_le_two.trans_lt (by omega)
    obtain ⟨c, hcL, hcN⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hN : c ≠ I.prescribed a ∧ c ≠ cd := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hcN
    exact ⟨c, hcL, hN⟩
  let f : V → C := fun x => if x = a then I.prescribed a else if x = b then cb else cd
  have hfa : f a = I.prescribed a := by simp only [f, ite_true]
  have hfb : f b = cb := by simp only [f, ite_eq_right hba, ite_true]
  have hfd : f d = cd := by simp only [f, ite_eq_right hda, ite_eq_right hdb]
  have hfA : ∀ x ∈ A, f x ∈ I.lists x := by
    intro x hx
    rcases (hAmem x).1 hx with hx | hx | hx
    · rw [hx, hfa, I.singleton a haP]; exact Finset.mem_singleton_self _
    · rw [hx, hfb]; exact hcb
    · rw [hx, hfd]; exact hcd
  have hproperA : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y := by
    intro x hx y hy hxy
    rcases (hAmem x).1 hx with hx | hx | hx <;> rcases (hAmem y).1 hy with hy | hy | hy <;> rw [hx, hy] at hxy ⊢
    · exact (hxy.ne rfl).elim
    · rw [hfa, hfb]; exact hcbA.symm
    · exact (had hxy).elim
    · rw [hfb, hfa]; exact hcbA
    · exact (hxy.ne rfl).elim
    · rw [hfb, hfd]; exact hcbD
    · exact (had hxy.symm).elim
    · rw [hfd, hfb]; exact hcbD.symm
    · exact (hxy.ne rfl).elim
  have hAconn : ConnSet G (↑A : Set V) := by
    have h := ((connSet_singleton G a).insert_adj (Set.mem_singleton a) hab.symm).insert_adj
      (Set.mem_insert b {a}) hbd.symm
    convert h using 1
    ext x
    simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  let Q : BoundaryPrecolor G := .path (.nil (u := t)) (by simp) (by simp)
  have hQv : ∀ x, x ∈ Q.vertices ↔ x = t := by intro x; simp [Q, BoundaryPrecolor.vertices]
  have hResT : residual G I.lists A f t = {I.prescribed t} := by
    apply Finset.Subset.antisymm
    · have h := residual_subset G I.lists A f t
      rwa [I.singleton t htP] at h
    · apply Finset.singleton_subset_iff.2
      apply (mem_residual_iff I.lists A f t _).2
      refine ⟨by simp only [I.singleton t htP, Finset.mem_singleton], ?_⟩
      intro u hu htu
      rcases (hAmem u).1 hu with rfl | rfl | rfl
      · rw [hfa]; exact I.proper_on_precolored_vertices htP haP htu
      · rcases chordless_native_cycle_last_neighbours p hp hch (p.getVert_mem_support 1) htu.symm with hta' | htd'
        · exact (hta hta').elim
        · exact (htd htd').elim
      · exact (I.short_not_adj_precolored hdP htP hsecond htu.symm).elim
  have hResTwo : ∀ x, x ∉ A → x ∉ Q.vertices → 2 ≤ (residual G I.lists A f x).card := by
    intro x hx hxQ
    have hxP : x ∉ I.precolor.vertices := by
      intro h
      rcases (hP x).1 h with hxa | hxt
      · exact hx ((hAmem x).2 (Or.inl hxa))
      · exact hxQ ((hQv x).2 hxt)
    by_cases hxs : (I.lists x).card ≤ 2
    · rw [residual_unchanged I.lists A f x (hOldNoA x hx hxP hxs)]
      exact I.outside_precolor_list_ge_two hxP
    · exact residual_two_edge_path_card_ge_two I.girth hab hbd hda.symm
        (fun h => hx ((hAmem x).2 (Or.inr (Or.inl h)))) I.lists f (by omega)
  have hNew : ∀ x, 3 ≤ (I.lists x).card → (residual G I.lists A f x).card ≤ 2 → ∃ u ∈ A, G.Adj u x :=
    fun x hx hxs => short_residual_neighbor I.lists A f x hx hxs
  have hShort : ∀ x, x ∉ A → ∀ y, y ∉ A → G.Adj x y →
      (residual G I.lists A f x).card ≤ 2 → (residual G I.lists A f y).card ≤ 2 → s(x,y) ∈ Q.edges := by
    intro x hx y hy hxy hxs hys
    exfalso
    by_cases hxOld : (I.lists x).card ≤ 2 <;> by_cases hyOld : (I.lists y).card ≤ 2
    · have hends := I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)
      have hxt : x = t := ((hP x).1 hends.1).resolve_left (fun h => hx ((hAmem x).2 (Or.inl h)))
      have hyt : y = t := ((hP y).1 hends.2).resolve_left (fun h => hy ((hAmem y).2 (Or.inl h)))
      exact hxy.ne (hxt.trans hyt.symm)
    · exact hNoOld y hy (by omega) (hNew y (by omega) hys) x hx hxOld hxy.symm
    · exact hNoOld x hx (by omega) (hNew x (by omega) hxs) y hy hyOld hxy
    · have hxN := hNew x (by omega) hxs
      have hyN := hNew y (by omega) hys
      by_cases hxf : OnOuterFace I.embedding I.outer x
      · by_cases hyf : OnOuterFace I.embedding I.outer y
        · have hxe : x = e := (hNewFace x hx hxf hxN).resolve_left (fun h => by
            have hc : (I.lists x).card = 1 := by rw [h, I.singleton t htP]; exact Finset.card_singleton _
            omega)
          have hye : y = e := (hNewFace y hy hyf hyN).resolve_left (fun h => by
            have hc : (I.lists y).card = 1 := by rw [h, I.singleton t htP]; exact Finset.card_singleton _
            omega)
          exact hxy.ne (hxe.trans hye.symm)
        · exact hCross y hy hyf hyN x hx hxf hxy.symm
      by_cases hyf : OnOuterFace I.embedding I.outer y
      · exact hCross x hx hxf hxN y hy hyf hxy
      rcases short_residual_two_edge_path_adjacent I.girth hab hbd hx hy I.lists f (by omega) (by omega) hxs hys hxy with h | h
      · exact hNoThree x y hxf hyf h.1 hxy h.2
      · exact hNoThree y x hyf hxf h.2 hxy.symm h.1
  apply hbad
  exact I.colourable_of_connected_boundary_deletion hG p hp hface hroot hExact A ((hAmem a).2 (Or.inl rfl)) hAconn
    f hfA hproperA Q (fun x hx => (hQv x).1 hx ▸ htA)
    (fun x hx => (hQv x).1 hx ▸ I.on_outer t htP)
    (by intro x y h; simp only [Q, BoundaryPrecolor.edges, Walk.edges_nil, List.toFinset_nil, Finset.notMem_empty] at h)
    (fun x hx => (hQv x).1 hx ▸ hResT) hResTwo hShort hsmall


/-- The remaining short-second-list branch must also have a short fourth
backward boundary list. This records the unresolved alternating-list pattern. -/
lemma prescribed_edge_fourth_boundary_list_le_two (I : BoundaryInstance G C)
    (hG : G.Preconnected) (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (hP : ∀ y, y ∈ I.precolor.vertices ↔ y = a ∨ y = p.getVert 1)
    (hlen : 6 ≤ p.length) (hsecond : (I.lists (p.getVert (p.length-2))).card ≤ 2)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    (I.lists (p.getVert (p.length-4))).card ≤ 2 := by
  by_contra h
  exact hbad (I.colourable_of_prescribed_edge_short_second_good_fourth hG p hp hface hroot hExact hP hlen hsecond (by omega) hsmall)

/-- The prescribed-edge case with an actual six-vertex outer face is closed
under the strict main induction. The fourth backward vertex is adjacent to the
other prescribed endpoint and therefore cannot have a short list. -/
theorem colourable_of_prescribed_edge_six_vertex_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hExact : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ p.support)
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : r.length = 1)
    (hfirst : p.getVert 1 ∈ I.precolor.vertices) (hlen : p.length = 6)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  by_cases hsecond : 3 ≤ (I.lists (p.getVert (p.length-2))).card
  · exact hbad (I.colourable_of_good_second_boundary_list_all_prescriptions hG p hp hface hroot hExact r hr hn hP hfirst hsecond hsmall)
  have horder := I.prescribed_path_forward_of_first_face_vertex hG p hp hface hExact r hr hn hP hfirst hbad hsmall
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z = a ∨ z = p.getVert 1 := by
    intro z
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset]
    constructor
    · intro hz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact Or.inl (by simpa only [Walk.getVert_zero] using hiz.symm)
      · exact Or.inr (hiz.symm.trans (horder 1 (by omega)))
    · rintro (hza | hz1)
      · exact hza ▸ r.start_mem_support
      · exact hz1 ▸ (horder 1 (by omega) ▸ r.getVert_mem_support 1)
  have hnotP : p.getVert 2 ∉ I.precolor.vertices := by
    intro h
    rcases (hPv _).1 h with h2a | h21
    · have hi := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from Nat.zero_le _)
        (by simpa only [Walk.getVert_zero] using h2a)
      omega
    · have hi := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 1 ≤ p.length-1 from by omega) h21
      omega
  have hfourth : 3 ≤ (I.lists (p.getVert (p.length-4))).card := by
    have h3 : 3 ≤ (I.lists (p.getVert 2)).card := by
      by_contra h
      exact I.short_not_adj_precolored hnotP hfirst (by omega)
        (by simpa only [show 1+1 = 2 by omega] using (p.adj_getVert_succ (by omega : 1 < p.length)).symm)
    simpa only [hlen, show 6-4 = 2 by omega] using h3
  exact hbad (I.colourable_of_prescribed_edge_short_second_good_fourth hG p hp hface hroot hExact hPv (by omega) (by omega) hfourth hsmall)

end BoundaryInstance
end Thomassen
