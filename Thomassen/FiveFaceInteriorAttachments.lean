/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AlternatingFiveFaceObstruction

/-! Interior attachments outside the forced inner five-face are independent. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Edges between two interior vertices attached outside the forced five-face
would give either a triangle, a quadrilateral, a second five-face, or a six-face
with the same first reversed old facial edge. All four possibilities are
excluded by girth and preservation of the actual short face orbit. -/
theorem inner_five_face_interior_attachments_independent (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 4 ≤ p.length) (x y : V)
    (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u v2 : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (huA : u ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (hvA : v2 ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (huN : ∃ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj u z)
    (hvN : ∃ z ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj v2 z) : ¬ G.Adj u v2 := by
  intro huv
  let b := p.getVert 2
  let d := p.getVert 1
  let A : Finset V := {a,d,b,x,y}
  have hAmem : ∀ z, z ∈ A ↔ z=a ∨ z=d ∨ z=b ∨ z=x ∨ z=y := by
    intro z; simp only [A,Finset.mem_insert,Finset.mem_singleton]
  have huNe : u≠a ∧ u≠d ∧ u≠b ∧ u≠x ∧ u≠y := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using huA
  have hvNe : v2≠a ∧ v2≠d ∧ v2≠b ∧ v2≠x ∧ v2≠y := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hvA
  have hf : ∀ j, OnOuterFace I.embedding I.outer (p.getVert j) := fun j =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support j)
  have hxa : x ≠ a := fun h => hx (by rw [h]; simpa only [Walk.getVert_zero] using hf 0)
  have hxb : x ≠ b := fun h => hx (h ▸ hf 2)
  have hyb : y ≠ b := fun h => hy (h ▸ hf 2)
  have hba : b ≠ a := by
    intro h
    have he := hp.getVert_injOn' (show 2 ≤ p.length-1 from by omega) (show 0 ≤ p.length-1 from by omega)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  let q : G.Walk (p.getVert 2) a := .cons hbx (.cons hxy (.cons hya .nil))
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    simp only [q,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,List.nodup_nil,and_true,not_false_eq_true]
    exact ⟨⟨hxb.symm,hyb.symm,hba⟩,⟨hxy.ne,hxa⟩,hya.ne⟩
  have hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j) := by
    intro j hj hjl
    have hj' : j=1 ∨ j=2 := by change j < 3 at hjl; omega
    rcases hj' with rfl | rfl
    · exact hx
    · exact hy
  have hNoThree : ∀ (u v2 : V), u ∉ A → ¬ OnOuterFace I.embedding I.outer u →
      ¬ OnOuterFace I.embedding I.outer v2 → G.Adj u b → G.Adj u v2 → G.Adj v2 a → False := by
    intro u v2 huA hu hv hub huv hva
    have he := (I.interior_three_path_across_two_face_edges_unique hG p hp hface hroot hlen
      x y u v2 hx hy hu hv hbx hxy hya hub.symm huv hva hbad hsmall).1
    exact huA ((hAmem u).2 (Or.inr (Or.inr (Or.inr (Or.inl he.symm)))))
  have hNoFour : ∀ (w : G.Walk (p.getVert 2) a), w.IsPath → w.length=4 →
      (∀ j, 0 < j → j < w.length → ¬ OnOuterFace I.embedding I.outer (w.getVert j)) → False := by
    intro w hw hwl hWInner
    have he := (I.short_closed_face_prefix_unique hG p hp hface hroot 2 (by omega) hlen q w hq hw
      (by change 0 < 3; omega) (by omega) (by change 2+3 ≤ 6; omega) (by omega)
      hInner hWInner hbad hsmall).2
    change 3=w.length at he
    omega
  have hNoFourRight : ∀ (u v2 : V), u ∉ A → v2 ∉ A → ¬ OnOuterFace I.embedding I.outer u →
      ¬ OnOuterFace I.embedding I.outer v2 → G.Adj u v2 → G.Adj u b → G.Adj v2 y → False := by
    intro u v2 huA hvA hu hv huv hub hvy
    have huNe : u≠a ∧ u≠d ∧ u≠b ∧ u≠x ∧ u≠y := by
      simpa only [A,Finset.mem_insert,Finset.mem_singleton,not_or] using huA
    have hvNe : v2≠a ∧ v2≠d ∧ v2≠b ∧ v2≠x ∧ v2≠y := by
      simpa only [A,Finset.mem_insert,Finset.mem_singleton,not_or] using hvA
    let w : G.Walk (p.getVert 2) a := .cons hub.symm (.cons huv (.cons hvy (.cons hya .nil)))
    apply hNoFour w ?_ rfl ?_
    · apply Walk.IsPath.mk'
      simp only [w,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
        not_or,List.nodup_nil,and_true,not_false_eq_true]
      exact ⟨⟨huNe.2.2.1.symm,hvNe.2.2.1.symm,hyb.symm,hba⟩,
        ⟨huv.ne,huNe.2.2.2.2,huNe.1⟩,⟨hvNe.2.2.2.2,hvNe.1⟩,hya.ne⟩
    · intro j hj hjl
      have hj' : j=1 ∨ j=2 ∨ j=3 := by change j < 4 at hjl; omega
      rcases hj' with rfl | rfl | rfl
      · exact hu
      · exact hv
      · exact hy
  have hNoFourLeft : ∀ (u v2 : V), u ∉ A → v2 ∉ A → ¬ OnOuterFace I.embedding I.outer u →
      ¬ OnOuterFace I.embedding I.outer v2 → G.Adj u v2 → G.Adj u a → G.Adj v2 x → False := by
    intro u v2 huA hvA hu hv huv hua hvx
    have huNe : u≠a ∧ u≠d ∧ u≠b ∧ u≠x ∧ u≠y := by
      simpa only [A,Finset.mem_insert,Finset.mem_singleton,not_or] using huA
    have hvNe : v2≠a ∧ v2≠d ∧ v2≠b ∧ v2≠x ∧ v2≠y := by
      simpa only [A,Finset.mem_insert,Finset.mem_singleton,not_or] using hvA
    let w : G.Walk (p.getVert 2) a := .cons hbx (.cons hvx.symm (.cons huv.symm (.cons hua .nil)))
    apply hNoFour w ?_ rfl ?_
    · apply Walk.IsPath.mk'
      simp only [w,Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
        not_or,List.nodup_nil,and_true,not_false_eq_true]
      exact ⟨⟨hxb.symm,hvNe.2.2.1.symm,huNe.2.2.1.symm,hba⟩,
        ⟨hvNe.2.2.2.1.symm,huNe.2.2.2.1.symm,hxa⟩,⟨huv.ne.symm,hvNe.1⟩,huNe.1⟩
    · intro j hj hjl
      have hj' : j=1 ∨ j=2 ∨ j=3 := by change j < 4 at hjl; omega
      rcases hj' with rfl | rfl | rfl
      · exact hx
      · exact hv
      · exact hu
  have hNoMiddle : ¬ G.Adj u d ∧ ¬ G.Adj v2 d := by
    have hm := I.middle_vertex_of_interior_three_path_neighbours hG p hp hface hroot hlen x y hx hy hbx hxy hya hbad hsmall
    exact ⟨fun h => (hm u h.symm).elim huNe.1 huNe.2.2.1,
      fun h => (hm v2 h.symm).elim hvNe.1 hvNe.2.2.1⟩
  have hNear : ∀ s ∈ A, ∀ t ∈ A, G.Adj u s → G.Adj v2 t → s≠t ∧ ¬ G.Adj s t := by
    intro s hs t ht hus hvt
    refine ⟨fun he => neighbors_nonadjacent I.girth hus.symm (he ▸ hvt.symm) huv,?_⟩
    intro hst
    have hne : u≠t := fun he => huA (he ▸ ht)
    have he := common_neighbor_unique I.girth hne hus hst.symm huv hvt.symm
    exact hvA (he ▸ hs)
  obtain ⟨s,hs,hus⟩ := huN
  obtain ⟨t,ht,hvt⟩ := hvN
  have hnear := hNear s hs t ht hus hvt
  rcases (hAmem s).1 hs with hs | hs | hs | hs | hs <;>
    rcases (hAmem t).1 ht with ht | ht | ht | ht | ht
  all_goals subst s; subst t
  all_goals first
    | exact hNoMiddle.1 hus
    | exact hNoMiddle.2 hvt
    | exact hnear.1 rfl
    | exact hnear.2 hbx
    | exact hnear.2 hbx.symm
    | exact hnear.2 hxy
    | exact hnear.2 hxy.symm
    | exact hnear.2 hya
    | exact hnear.2 hya.symm
    | exact hNoThree u v2 huA hu hv hus huv hvt
    | exact hNoThree v2 u hvA hv hu hvt huv.symm hus
    | exact hNoFourRight u v2 huA hvA hu hv huv hus hvt
    | exact hNoFourRight v2 u hvA huA hv hu huv.symm hvt hus
    | exact hNoFourLeft u v2 huA hvA hu hv huv hus hvt
    | exact hNoFourLeft v2 u hvA huA hv hu huv.symm hvt hus

end Thomassen.BoundaryInstance
