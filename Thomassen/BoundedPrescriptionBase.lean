/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedPrescription

/-! Converting a connected nonbranching prescription to an actual short walk. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- A connected vertex set of maximum induced degree two, whose simple paths
have at most five edges, is exactly a native path or cycle on at most six
vertices. Every induced edge belongs to the resulting native prescription. -/
theorem exists_native_precolor_of_connected_degree_two (P : Set V) (hP : ConnSet G P)
    (hshort : ∀ {a b : V} (p : G.Walk a b), p.IsPath →
      (∀ x ∈ p.support, x ∈ P) → p.length ≤ 5)
    (hthird : ∀ x ∈ P, ∀ r ∈ P, ∀ s ∈ P, ∀ t ∈ P,
      G.Adj x r → G.Adj x s → G.Adj x t → r ≠ s → t = r ∨ t = s) :
    ∃ Q : BoundaryPrecolor G, (∀ x, x ∈ Q.vertices ↔ x ∈ P) ∧
      ∀ {x y}, x ∈ P → y ∈ P → G.Adj x y → s(x,y) ∈ Q.edges := by
  obtain ⟨z, hz⟩ := hP.1
  let : Nonempty P := ⟨⟨z, hz⟩⟩
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length (G.induce P)
  let q : G.Walk a.1 b.1 := p.map (Embedding.induce P).toHom
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hsub : ∀ x ∈ q.support, x ∈ P := by
    intro x hx
    change x ∈ (p.map (Embedding.induce P).toHom).support at hx
    rw [Walk.support_map] at hx
    obtain ⟨y, _, hy⟩ := List.mem_map.1 hx
    change y.1 = x at hy
    subst x
    exact y.2
  have hmaxq : ∀ {r s : V} (w : G.Walk r s), w.IsPath →
      (∀ x ∈ w.support, x ∈ P) → w.length ≤ q.length := by
    intro r s w hw hs
    have hi : (w.induce P hs).IsPath := Walk.IsPath.of_map
      (f := (Embedding.induce P).toHom) (by simpa using hw)
    have hm := hmax _ _ (w.induce P hs) hi
    have hl : (w.induce P hs).length = w.length := by
      rw [← Walk.length_map (Embedding.induce P).toHom, w.map_induce hs]
      rfl
    change w.length ≤ (p.map (Embedding.induce P).toHom).length
    rw [Walk.length_map]
    exact hl ▸ hm
  have hlen : q.length ≤ 5 := hshort q hq hsub
  have hneighbours : ∀ i : ℕ, 0 < i → i < q.length → ∀ y ∈ P,
      G.Adj (q.getVert i) y → y = q.getVert (i-1) ∨ y = q.getVert (i+1) := by
    intro i hi hil y hy hiy
    apply hthird _ (hsub _ (q.getVert_mem_support i))
      _ (hsub _ (q.getVert_mem_support (i-1)))
      _ (hsub _ (q.getVert_mem_support (i+1))) y hy
    · simpa only [Nat.sub_add_cancel hi] using
        (q.adj_getVert_succ (by omega : i-1 < q.length)).symm
    · exact q.adj_getVert_succ hil
    · exact hiy
    · intro heq
      have he := hq.getVert_injOn (by change i-1 ≤ q.length; omega)
        (by change i+1 ≤ q.length; omega) heq
      omega
  have hclosed : ∀ x ∈ q.support, ∀ y ∈ P, G.Adj x y → y ∈ q.support := by
    intro x hx y hy hxy
    by_contra hyq
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    subst x
    by_cases hi0 : i = 0
    · subst i
      simp only [Walk.getVert_zero] at hxy
      have hw : (Walk.cons hxy.symm q).IsPath := Walk.IsPath.mk'
        (by simpa only [Walk.support_cons, List.nodup_cons] using And.intro hyq hq.support_nodup)
      have h := hmaxq _ hw (by
        intro w hw
        rcases (List.mem_cons.1 hw) with rfl | hw
        · exact hy
        · exact hsub w hw)
      simp only [Walk.length_cons] at h
      omega
    · by_cases hil : i = q.length
      · have hby : G.Adj b.1 y := by simpa only [hil, Walk.getVert_length] using hxy
        have h := hmaxq (q.concat hby) (hq.concat hyq hby) (by
          intro w hw
          simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | rfl
          · exact hsub w hw
          · exact hy)
        simp only [Walk.length_concat] at h
        omega
      · rcases hneighbours i (by omega) (by omega) y hy hxy with h | h
        all_goals exact hyq (h ▸ q.getVert_mem_support _)
  have hcover : ∀ x, x ∈ q.support ↔ x ∈ P := by
    intro x
    refine ⟨hsub x, fun hx => ?_⟩
    have hr := hP.2 a.1 a.2 x hx
    induction hr with
    | refl => exact q.start_mem_support
    | @tail w y _ hwy ih => exact hclosed w (ih hwy.2.1) y hwy.2.2 hwy.1
  have hchords : ∀ {x y}, x ∈ P → y ∈ P → G.Adj x y →
      s(x,y) ∈ q.edges ∨ (x = a.1 ∧ y = b.1) ∨ (x = b.1 ∧ y = a.1) := by
    have hlocal : ∀ i, 0 < i → i < q.length → ∀ y ∈ P,
        G.Adj (q.getVert i) y → s(q.getVert i,y) ∈ q.edges := by
      intro i hi hil y hy hiy
      rcases hneighbours i hi hil y hy hiy with rfl | rfl
      · rw [Sym2.eq_swap]
        exact q.mk_mem_edges_iff_exists.2 ⟨i-1, by omega, by rw [Nat.sub_add_cancel hi]⟩
      · exact q.mk_mem_edges_iff_exists.2 ⟨i, hil, rfl⟩
    intro x y hx hy hxy
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 ((hcover x).2 hx)
    obtain ⟨j, hjy, hj⟩ := Walk.mem_support_iff_exists_getVert.1 ((hcover y).2 hy)
    subst x; subst y
    by_cases hiint : 0 < i ∧ i < q.length
    · exact Or.inl (hlocal i hiint.1 hiint.2 _ hy hxy)
    · by_cases hjint : 0 < j ∧ j < q.length
      · exact Or.inl (by rw [Sym2.eq_swap]; exact hlocal j hjint.1 hjint.2 _ hx hxy.symm)
      · rcases (by omega : i = 0 ∨ i = q.length) with rfl | rfl <;>
          rcases (by omega : j = 0 ∨ j = q.length) with rfl | rfl
        · exact (hxy.ne rfl).elim
        · exact Or.inr (Or.inl ⟨q.getVert_zero, q.getVert_length⟩)
        · exact Or.inr (Or.inr ⟨q.getVert_length, q.getVert_zero⟩)
        · exact (hxy.ne rfl).elim
  have hbound : q.support.toFinset.card ≤ 6 := by
    have := List.toFinset_card_le q.support
    rw [q.length_support] at this
    omega
  by_cases hcycle : G.Adj a.1 b.1 ∧ 1 < q.length
  · let w : G.Walk a.1 a.1 := Walk.cons hcycle.1 q.reverse
    have hw : w.IsCycle := (Walk.cons_isCycle_iff q.reverse hcycle.1).2 ⟨hq.reverse, by
      intro he
      have h := hq.reverse.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
      simp only [Walk.length_reverse] at h
      omega⟩
    have hwv : ∀ x, x ∈ w.support ↔ x ∈ P := by
      intro x
      simp only [w, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse]
      exact ⟨fun h => h.elim (fun h => h ▸ a.2) ((hcover x).1), fun h => Or.inr ((hcover x).2 h)⟩
    have hwb : w.support.toFinset.card ≤ 6 := by
      have he : w.support.toFinset = q.support.toFinset := by
        ext x
        simp only [List.mem_toFinset, hwv, hcover]
      rwa [he]
    refine ⟨.cycle w hw hwb, (fun x => List.mem_toFinset.trans (hwv x)), ?_⟩
    intro x y hx hy hxy
    change s(x,y) ∈ w.edges.toFinset
    simp only [w, Walk.edges_cons, Walk.edges_reverse, List.mem_toFinset, List.mem_cons, List.mem_reverse]
    rcases hchords hx hy hxy with he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inr he
    · exact Or.inl rfl
    · exact Or.inl (Sym2.eq_swap)
  · refine ⟨.path q hq hbound, (fun x => List.mem_toFinset.trans (hcover x)), ?_⟩
    intro x y hx hy hxy
    change s(x,y) ∈ q.edges.toFinset
    apply List.mem_toFinset.2
    have hends : G.Adj a.1 b.1 → s(a.1,b.1) ∈ q.edges := by
      intro hab
      have hl : q.length = 1 := by
        have hpos : q.length ≠ 0 := fun h => hab.ne (q.eq_of_length_eq_zero h)
        have := not_and.1 hcycle hab
        omega
      exact q.mk_mem_edges_iff_exists.2 ⟨0, by omega, by
        rw [show 0+1 = q.length from hl.symm, Walk.getVert_zero, Walk.getVert_length]⟩
    rcases hchords hx hy hxy with he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact he
    · exact hends hxy
    · rw [Sym2.eq_swap]; exact hends hxy.symm

end Thomassen
