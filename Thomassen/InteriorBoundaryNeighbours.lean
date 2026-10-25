/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CompatibleEdgeStarPath

/-! Bounds on all boundary neighbours, without restricting the facial length. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- In the forward native facial order, an interior vertex has at most one
unprescribed boundary neighbour. The complementary arc is rebased at the
terminal prescribed vertex; the proved free-arc reduction applies to it. -/
theorem interior_unprescribed_neighbour_unique_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x = y := by
  have hverts : ∀ z, z ∈ p.support ↔ OnOuterFace I.embedding I.outer z :=
    native_facial_cycle_support_iff I.embedding I.outer p hp hface hroot
  have hbound := I.prescribed_path_outer_cycle_length_lower_bound r hr hn hP hbad hsmall p hp hverts
  obtain ⟨q,hq,hqlen,hqo,hqface,hqroot⟩ := exists_rebased_native_face_cycle
    I.embedding I.outer p hp hface hroot r.length (by omega)
  let : NeZero p.length := ⟨by omega⟩
  have hPv : ∀ z, z ∈ I.precolor.vertices ↔ z ∈ r.support := by
    intro z; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
  have hindex : ∀ z, OnOuterFace I.embedding I.outer z → z ∉ I.precolor.vertices →
      ∃ j : ℕ, r.length < j ∧ j < p.length ∧ p.getVert j = z := by
    intro z hz hzP
    have hzrange : z ∈ Set.range (walkCycleVertices p) := by
      rw [walkCycleVertices_range p hp]; exact (hverts z).2 hz
    obtain ⟨i,hi⟩ := hzrange
    have hil : i.val < p.length := ZMod.val_lt i
    refine ⟨i.val,?_,hil,hi⟩
    by_contra h
    have hile : i.val ≤ r.length := by omega
    apply hzP ((hPv z).2 ?_)
    have hiv : p.getVert i.val = z := hi
    rw [← hiv,← horder i.val hile]
    exact r.getVert_mem_support _
  obtain ⟨i,hri,hip,hix⟩ := hindex x hx hxP
  obtain ⟨j,hrj,hjp,hjy⟩ := hindex y hy hyP
  have hqi : q.getVert (i-r.length) = x := by
    rw [hqo _ (by omega),Nat.add_sub_of_le (by omega : r.length ≤ i),walkCycleVertices_nat_le p (by omega),hix]
  have hqj : q.getVert (j-r.length) = y := by
    rw [hqo _ (by omega),Nat.add_sub_of_le (by omega : r.length ≤ j),walkCycleVertices_nat_le p (by omega),hjy]
  have hfree : ∀ z ∈ I.precolor.vertices,
      z ∉ cycleInterval (walkCycleVertices q) 1 (p.length-r.length-2) := by
    intro z hz hzarc
    obtain ⟨k,hkz,hkr⟩ := Walk.mem_support_iff_exists_getVert.1 ((hPv z).1 hz)
    obtain ⟨l,hl,hlz⟩ := hzarc
    rw [walkCycleVertices_nat_le q (by omega : 1+l ≤ q.length),hqo (1+l) (by omega),
      walkCycleVertices_nat_le p (by omega : r.length+(1+l) ≤ p.length)] at hlz
    have heq : p.getVert k = p.getVert (r.length+(1+l)) :=
      (horder k hkr).symm.trans (hkz.trans hlz.symm)
    have hi := hp.getVert_injOn' (show k ≤ p.length-1 from by omega)
      (show r.length+(1+l) ≤ p.length-1 from by omega) heq
    omega
  have he := I.interior_neighbours_unique_on_free_arc hG q hq hqface hqroot hbad hsmall
    (p.length-r.length) (by omega) hfree u hu (i-r.length) (j-r.length)
    (by omega) (by omega) (by rwa [hqi]) (by rwa [hqj])
  exact hqi.symm.trans ((congrArg q.getVert he).trans hqj)

/-- The unprescribed-neighbour uniqueness is independent of the original
face representative and of the direction of the prescribed path. -/
theorem interior_unprescribed_neighbour_unique (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huy : G.Adj u y) : x = y := by
  obtain ⟨hG,hcase⟩ := I.exists_oriented_native_face_for_prescribed_path r hr hn hP hbad hsmall
  rcases hcase with ⟨p,hp,hface,hroot,horder⟩ | ⟨p,hp,hface,hroot,horder⟩
  · exact I.interior_unprescribed_neighbour_unique_on_native_face hG p hp hface hroot
      r hr hn hP hrlen horder hbad hsmall u x y hu hx hy hxP hyP hux huy
  · have hm : ∀ z, OnOuterFace I.mirror.embedding I.mirror.outer z ↔ OnOuterFace I.embedding I.outer z :=
      mirror_onOuterFace_iff I.embedding I.outer
    exact I.mirror.interior_unprescribed_neighbour_unique_on_native_face hG p hp hface hroot
      r hr hn hP hrlen horder hbad hsmall u x y (fun h => hu ((hm u).1 h))
      ((hm x).2 hx) ((hm y).2 hy) hxP hyP hux huy

/-- Every three boundary neighbours of an interior vertex contain a repeated
vertex. Both prescribed and unprescribed neighbours are bounded separately,
so there are at most two boundary neighbours in total. -/
theorem interior_at_most_two_boundary_neighbours (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u x y z : V) (hu : ¬ OnOuterFace I.embedding I.outer u)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hz : OnOuterFace I.embedding I.outer z)
    (hux : G.Adj u x) (huy : G.Adj u y) (huz : G.Adj u z) :
    x=y ∨ x=z ∨ y=z := by
  have hPunique := I.interior_prescribed_neighbour_unique r hr hn hP hbad hsmall u
  have hFunique := I.interior_unprescribed_neighbour_unique r hr hn hP hrlen hbad hsmall u
  by_cases hxP : x ∈ I.precolor.vertices <;> by_cases hyP : y ∈ I.precolor.vertices
  · exact Or.inl (hPunique x y hu hxP hyP hux huy)
  · by_cases hzP : z ∈ I.precolor.vertices
    · exact Or.inr (Or.inl (hPunique x z hu hxP hzP hux huz))
    · exact Or.inr (Or.inr (hFunique y z hu hy hz hyP hzP huy huz))
  · by_cases hzP : z ∈ I.precolor.vertices
    · exact Or.inr (Or.inr (hPunique y z hu hyP hzP huy huz))
    · exact Or.inr (Or.inl (hFunique x z hu hx hz hxP hzP hux huz))
  · exact Or.inl (hFunique x y hu hx hy hxP hyP hux huy)

end Thomassen.BoundaryInstance
