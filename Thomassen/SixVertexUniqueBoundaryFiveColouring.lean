/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexUniqueBoundaryFiveDeletion

/-! Choose colours and delete the entire forced inner five-face. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
set_option maxHeartbeats 800000
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- The free five-face can be coloured and deleted when the preceding
boundary list is short and the following one is a singleton. The entire old
prescription is retained. All residual lists and actual component faces are
handled by the previously proved deletion and pendant-prescription lemmas. -/
theorem colourable_of_free_inner_five_face_short_neighbours_unique_boundary (I : BoundaryInstance G C)
    (hG : G.Preconnected) {s t a : V}
    (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length) (hBoundaryUnique : ∀ (u x y : V), ¬ OnOuterFace I.embedding I.outer u →
      OnOuterFace I.embedding I.outer x → OnOuterFace I.embedding I.outer y →
      G.Adj u x → G.Adj u y → x=y)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length)
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (hprev : (I.lists (p.getVert (p.length-1))).card ≤ 2)
    (hnext : (I.lists (p.getVert 3)).card ≤ 1)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_contra hbad
  let d := p.getVert 1
  let b := p.getVert 2
  let prev := p.getVert (p.length-1)
  let next := p.getVert 3
  have hprev' : (I.lists prev).card ≤ 2 := hprev
  have hnext' : (I.lists next).card ≤ 1 := hnext
  have hf : ∀ j, OnOuterFace I.embedding I.outer (p.getVert j) := fun j =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support j)
  have haF : OnOuterFace I.embedding I.outer a := by simpa only [Walk.getVert_zero] using hf 0
  have hne : ∀ i j : ℕ, i < p.length → j < p.length → i ≠ j → p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij he
    exact hij (hp.getVert_injOn' (by change i ≤ p.length-1; omega) (by change j ≤ p.length-1; omega) he)
  have hda : d ≠ a := by simpa only [Walk.getVert_zero] using hne 1 0 (by omega) (by omega) (by omega)
  have hba : b ≠ a := by simpa only [Walk.getVert_zero] using hne 2 0 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := hne 2 1 (by omega) (by omega) (by omega)
  have hxa : x ≠ a := fun h => hx (h ▸ haF)
  have hxd : x ≠ d := fun h => hx (h ▸ hf 1)
  have hxb : x ≠ b := fun h => hx (h ▸ hf 2)
  have hyaNe : y ≠ a := hya.ne
  have hyd : y ≠ d := fun h => hy (h ▸ hf 1)
  have hyb : y ≠ b := fun h => hy (h ▸ hf 2)
  have hxyNe : x ≠ y := hxy.ne
  let q : G.Walk (p.getVert 2) a := .cons hbx (.cons hxy (.cons hya .nil))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨hxb.symm,hyb.symm,hba⟩,⟨hxyNe,hxa⟩,hyaNe⟩
  have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
    intro j hj hjl
    have hj' : j=1 ∨ j=2 := by change j < 3 at hjl; omega
    rcases hj' with rfl | rfl
    · exact hx
    · exact hy
  have hmeet := closing_path_intersection_of_interior I.embedding I.outer p hp hface hroot 2 q hInner
  let c := spliceFacePath p 2 q
  have hc : c.IsCycle := spliceFacePath_isCycle p hp 2 q hq (by omega) (by omega) hmeet
  have hclen : c.length=5 := by rw [spliceFacePath_length p 2 q (by omega)]; rfl
  have hc0 : c.getVert 0 = a := Walk.getVert_zero c
  have hc1 : c.getVert 1 = d := spliceFacePath_getVert_prefix p 2 q (by omega) (by omega)
  have hc2 : c.getVert 2 = b := spliceFacePath_getVert_prefix p 2 q (by omega) (by omega)
  have hc3 : c.getVert 3 = x := by
    simp only [c,spliceFacePath,Walk.getVert_append,Walk.take_length,Nat.min_eq_left (by omega : 2 ≤ p.length),
      show ¬ (3 < 2) by omega,ite_false]
    rfl
  have hc4 : c.getVert 4 = y := by
    simp only [c,spliceFacePath,Walk.getVert_append,Walk.take_length,Nat.min_eq_left (by omega : 2 ≤ p.length),
      show ¬ (4 < 2) by omega,ite_false]
    rfl
  have hc5 : c.getVert 5 = a := by rw [← hclen,Walk.getVert_length]
  have hC : ∀ z, z ∈ c.support ↔ z ∈ ({a,d,b,x,y} : Finset V) := by
    intro z
    constructor
    · intro hz
      obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      have hcase : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hi.symm.trans hc0)
      · exact Or.inr (Or.inl (hi.symm.trans hc1))
      · exact Or.inr (Or.inr (Or.inl (hi.symm.trans hc2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hi.symm.trans hc3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hi.symm.trans hc4))))
      · exact Or.inl (hi.symm.trans hc5)
    · intro hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      all_goals apply Walk.mem_support_iff_exists_getVert.2
      · exact ⟨0,hc0.trans h.symm,by omega⟩
      · exact ⟨1,hc1.trans h.symm,by omega⟩
      · exact ⟨2,hc2.trans h.symm,by omega⟩
      · exact ⟨3,hc3.trans h.symm,by omega⟩
      · exact ⟨4,hc4.trans h.symm,by omega⟩
  have hch := I.native_face_cycle_chordless_of_minimal_counterexample hG p hp hface hroot hbad hsmall
  have hBoundaryPair : ∀ z, z ∉ c.support → OnOuterFace I.embedding I.outer z →
      ∀ w ∈ c.support, G.Adj z w → (z=prev ∧ w=a) ∨ (z=next ∧ w=b) := by
    intro z hz hzF w hw hzw
    have hzSupport := (native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot z).2 hzF
    have hzC : z ∉ ({a,d,b,x,y} : Finset V) := fun h => hz ((hC z).2 h)
    have hNot : z≠a ∧ z≠d ∧ z≠b := by
      constructor
      · exact fun h => hzC (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)
      · constructor <;> intro h <;> apply hzC <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    have hwC := (hC w).1 hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hwC
    rcases hwC with hwa | hwd | hwb | hwx | hwy
    · rcases chordless_native_cycle_root_neighbours p hp hch hzSupport (by rw [← hwa]; exact hzw.symm) |>.resolve_left hNot.2.1 with hzp
      exact Or.inl ⟨hzp,hwa⟩
    · have hadj : G.Adj d z := by rw [← hwd]; exact hzw.symm
      have hNear := chordless_native_cycle_vertex_neighbours p hp hch 1 (by omega) (by omega) hzSupport hadj
      simpa only [Nat.sub_self,Walk.getVert_zero,show 1+1=2 by rfl] using hNear.elim
        (fun h => (hNot.1 (by simpa only [Nat.sub_self,Walk.getVert_zero] using h)).elim)
        (fun h => (hNot.2.2 h).elim)
    · have hadj : G.Adj b z := by rw [← hwb]; exact hzw.symm
      rcases chordless_native_cycle_vertex_neighbours p hp hch 2 (by omega) (by omega) hzSupport hadj with h | h
      · exact (hNot.2.1 h).elim
      · exact Or.inr ⟨h,hwb⟩
    · have he := hBoundaryUnique x b z hx (hf 2) hzF hbx.symm (by rw [← hwx]; exact hzw.symm)
      exact (hNot.2.2 he.symm).elim
    · have he := hBoundaryUnique y a z hy haF hzF hya (by rw [← hwy]; exact hzw.symm)
      exact (hNot.1 he.symm).elim
  have haprev : G.Adj a prev := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),Walk.getVert_length] using
      (p.adj_getVert_succ (by omega : p.length-1 < p.length)).symm
  have hbanext : G.Adj b next := p.adj_getVert_succ (by omega : 2 < p.length)
  have h3a : 3 ≤ (I.lists a).card := by
    by_contra h
    exact haP (I.precolor.endpoints_of_mem_edges (I.short_edges haprev (by omega) hprev)).1
  have h3b : 3 ≤ (I.lists b).card := by
    by_contra h
    exact hbP (I.precolor.endpoints_of_mem_edges (I.short_edges hbanext (by omega) (by omega))).1
  obtain ⟨ca,hca,hcaprev⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := I.lists prev) (t := I.lists a) (by omega)
  obtain ⟨cd,hcd,hcda⟩ := Finset.exists_mem_ne (s := I.lists d)
    (by have h2 : 2 ≤ (I.lists d).card := I.outside_precolor_list_ge_two hdP; omega) ca
  obtain ⟨cb,hcb,hcbN⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := insert cd (I.lists next)) (t := I.lists b)
    (by have h := Finset.card_insert_le cd (I.lists next); omega)
  have hcbd : cb≠cd := fun h => hcbN (Finset.mem_insert.2 (Or.inl h))
  have hcbnext : cb ∉ I.lists next := fun h => hcbN (Finset.mem_insert.2 (Or.inr h))
  obtain ⟨cx,hcx,hcxb⟩ := Finset.exists_mem_ne (s := I.lists x) (by have h := I.interior_lists x hx; omega) cb
  obtain ⟨cy,hcy,hcyN⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({cx,ca} : Finset C)) (t := I.lists y)
    (Finset.card_le_two.trans_lt (by have h := I.interior_lists y hy; omega))
  have hcyx : cy≠cx := fun h => hcyN (Finset.mem_insert.2 (Or.inl h))
  have hcya : cy≠ca := fun h => hcyN (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
  let f : V → C := fun z => if z=a then ca else if z=d then cd else if z=b then cb else if z=x then cx else cy
  have hfa : f a=ca := by simp only [f,ite_true]
  have hfd : f d=cd := by simp only [f,ite_eq_right hda,ite_true]
  have hfb : f b=cb := by simp only [f,ite_eq_right hba,ite_eq_right hbd,ite_true]
  have hfx : f x=cx := by simp only [f,ite_eq_right hxa,ite_eq_right hxd,ite_eq_right hxb,ite_true]
  have hfy : f y=cy := by simp only [f,ite_eq_right hyaNe,ite_eq_right hyd,ite_eq_right hyb,ite_eq_right hxyNe.symm]
  have hfC : ∀ z ∈ c.support, f z ∈ I.lists z := by
    intro z hz
    have hzC := (hC z).1 hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hzC
    rcases hzC with h | h | h | h | h
    · rw [h,hfa]; exact hca
    · rw [h,hfd]; exact hcd
    · rw [h,hfb]; exact hcb
    · rw [h,hfx]; exact hcx
    · rw [h,hfy]; exact hcy
  have hcch : c.IsChordless := by
    let : NeZero c.length := ⟨by omega⟩
    have hch := short_cycle_isChordless I.girth (walk_isCycleMap c hc) hc.three_le_length (by omega)
    apply Walk.isChordless_iff_forall_mem_edges.2
    intro z w hz hw hzw
    apply (walkCycleVertices_edges c hc z w).1
    exact cyclicSubgraph_of_chordless hch (by rw [walkCycleVertices_range c hc]; exact hz)
      (by rw [walkCycleVertices_range c hc]; exact hw) hzw
  have hproper : ∀ z ∈ c.support, ∀ w ∈ c.support, G.Adj z w → f z ≠ f w := by
    have hstep : ∀ i, i < c.length → f (c.getVert i) ≠ f (c.getVert (i+1)) := by
      intro i hi
      have hcase : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl
      · simpa only [hc0,hc1,hfa,hfd] using hcda.symm
      · simpa only [hc1,hc2,hfd,hfb] using hcbd.symm
      · simpa only [hc2,hc3,hfb,hfx] using hcxb.symm
      · simpa only [hc3,hc4,hfx,hfy] using hcyx.symm
      · simpa only [hc4,hc5,hfy,hfa] using hcya
    intro z hz w hw hzw
    obtain ⟨i,hi,he⟩ := c.mk_mem_edges_iff_exists.1 (hcch.mem_edges hz hw hzw)
    rcases Sym2.eq_iff.1 he with he | he
    · simpa only [he.1,he.2] using hstep i hi
    · simpa only [he.1,he.2] using (hstep i hi).symm
  have hOldUnchanged : ∀ z, z ∉ c.support → (I.lists z).card ≤ 2 →
      residual G I.lists c.support.toFinset f z = I.lists z := by
    intro z hz hzs
    apply Finset.Subset.antisymm (residual_subset G I.lists _ f z)
    intro col hcol
    apply (mem_residual_iff I.lists _ f z col).2
    refine ⟨hcol,?_⟩
    intro w hw hzw
    have hzF : OnOuterFace I.embedding I.outer z := by
      by_contra h
      have h3 := I.interior_lists z h
      omega
    rcases hBoundaryPair z hz hzF w (List.mem_toFinset.1 hw) hzw with ⟨hzp,hwa⟩ | ⟨hzn,hwb⟩
    · rw [hwa,hfa]
      exact fun h => hcaprev (by rw [← hzp]; exact h ▸ hcol)
    · rw [hwb,hfb]
      exact fun h => hcbnext (by rw [← hzn]; exact h ▸ hcol)
  apply hbad
  apply I.colourable_of_free_inner_five_face_deletion_unique_boundary hG r hr hn hP hrpos hBoundaryUnique p hp hface hroot (by omega)
    haP hdP hbP x y hx hy hbx hxy hya c hc hclen hC f hfC hproper hOldUnchanged ?_ hsmall
  intro z hz hzF ⟨w,hw,hzw⟩
  rcases hBoundaryPair z hz hzF w hw hzw with ⟨hzp,_⟩ | ⟨hzn,_⟩
  · rw [hzp]; exact hprev
  · rw [hzn]; omega

end Thomassen.BoundaryInstance
