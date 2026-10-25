/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AlternatingBoundaryLists

/-! Reversing an actual plane embedding and its selected face. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical

lemma cycleCount_inv_eq {D : Type*} (σ : Perm D) : cycleCount σ⁻¹ = cycleCount σ :=
  numClasses_congr (fun _ _ => sameCycle_inv)

lemma numComponents_inv_left {D : Type*} (σ α : Perm D) :
    numComponents σ⁻¹ α = numComponents σ α := by
  apply numClasses_congr
  intro a b
  constructor
  · exact compSetoid_le (compSetoid σ α)
      (fun z => compSetoid_of_sameCycle_left (sameCycle_inv_apply_self σ z).symm)
      (compSetoid_right σ α)
  · exact compSetoid_le (compSetoid σ⁻¹ α)
      (fun z => compSetoid_of_sameCycle_left ((SameCycle.refl σ z).apply_right).inv)
      (compSetoid_right σ⁻¹ α)

variable {V : Type u} {G : SimpleGraph V}

@[simp] lemma mirror_dartSymm_inv_apply (d : G.Dart) : (dartSymm G)⁻¹ d = d.symm := by
  rw [Perm.inv_eq_iff_eq]
  simp

lemma mirror_fst_rot_inv (M : PlaneMap G) (d : G.Dart) : (M.rot⁻¹ d).fst = d.fst := by
  have h := M.isRotationSystem.fst_apply (M.rot⁻¹ d)
  simpa using h.symm

/-- Reverse the rotation at every vertex, preserving the genus-zero certificate. -/
def mirrorPlaneMap (M : PlaneMap G) : PlaneMap G where
  rot := M.rot⁻¹
  isRotationSystem := {
    fst_apply := mirror_fst_rot_inv M
    sameCycle := fun d e h => (M.isRotationSystem.sameCycle d e h).inv }
  eulerDefect_eq_zero := by
    have heq : M.rot⁻¹ * dartSymm G = (dartSymm G).permCongr (M.rot * dartSymm G)⁻¹ := by
      apply Equiv.ext
      intro d
      simp [mul_inv_rev, dartSymm]
    change eulerDefect M.rot⁻¹ (dartSymm G) = 0
    unfold eulerDefect
    rw [numComponents_inv_left, cycleCount_inv_eq, heq, cycleCount_permCongr, cycleCount_inv_eq]
    exact M.eulerDefect_eq_zero

/-- The mirrored face permutation is the dart reversal conjugate of the
inverse old face permutation. -/
lemma mirror_facePerm (M : PlaneMap G) :
    (mirrorPlaneMap M).facePerm = (dartSymm G).permCongr M.facePerm⁻¹ := by
  apply Equiv.ext
  intro d
  simp [PlaneMap.facePerm, mirrorPlaneMap, mul_inv_rev, dartSymm]

lemma mirror_face_sameCycle (M : PlaneMap G) (d e : G.Dart) :
    SameCycle (mirrorPlaneMap M).facePerm d.symm e.symm ↔ SameCycle M.facePerm d e := by
  rw [mirror_facePerm]
  have h := sameCycle_permCongr_iff (dartSymm G) M.facePerm⁻¹ d e
  simpa only [dartSymm_apply, sameCycle_inv] using h.symm

/-- Mirroring changes the directed boundary traversal but retains precisely
the same incident vertices on the selected face. -/
lemma mirror_onOuterFace_iff (M : PlaneMap G) (outer : G.Dart) (x : V) :
    OnOuterFace (mirrorPlaneMap M) outer.symm x ↔ OnOuterFace M outer x := by
  constructor
  · rintro ⟨d, hd, hdx⟩
    have h : SameCycle M.facePerm outer d.symm := (mirror_face_sameCycle M outer d.symm).1 (by simpa only [Dart.symm_symm] using hd)
    refine ⟨M.facePerm d.symm, h.apply_right, ?_⟩
    exact (M.isRotationSystem.fst_apply d).trans hdx
  · rintro ⟨d, hd, hdx⟩
    let e := M.facePerm⁻¹ d
    have he : M.facePerm e = d := by simp [e]
    have hef : e.snd = d.fst := by
      have h := congrArg (fun (z : G.Dart) => z.fst) he
      change (M.rot e.symm).fst = d.fst at h
      rw [M.isRotationSystem.fst_apply] at h
      exact h
    exact ⟨e.symm, (mirror_face_sameCycle M outer e).2 hd.symm_apply_right, hef.trans hdx⟩


/-- A complete native facial cycle gives the exact selected face vertex set;
its corner equations cover the whole face orbit, not just a subset of it. -/
lemma native_facial_cycle_support_iff [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (x : V) :
    x ∈ p.support ↔ OnOuterFace M outer x := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  constructor
  · exact native_facial_cycle_vertices_on_outer M outer p hp hface hroot x
  · rintro ⟨d, hd, hdx⟩
    have hstep : ∀ i, M.facePerm (toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) i)) =
        toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) (i+1)) := by
      intro i
      simpa only [add_sub_cancel_right] using hface (i+1) (Set.mem_univ _)
    obtain ⟨i, hi⟩ := eq_of_sameCycle_cyc hstep (hroot.symm.trans hd)
    have hix : walkCycleVertices p i = x := by rw [hi] at hdx; exact hdx
    exact hix ▸ p.getVert_mem_support _

/-- Full indexed facial corner equations reverse in the mirrored embedding. -/
lemma mirrored_cycle_isFacial [Fintype V] (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c)
    (hface : IsFacialCycleAlong M hc Set.univ) :
    IsFacialCycleAlong (mirrorPlaneMap M) hc.reverse Set.univ := by
  have hd : ∀ i : ZMod k, toDart cyclicSubgraph_le (cycleForward hc.reverse i) =
      (toDart cyclicSubgraph_le (cycleForward hc (-i-1))).symm := by
    intro i
    apply (Dart.ext_iff _ _).2
    exact Prod.ext (by change c (-i) = c (-i-1+1); rw [sub_add_cancel])
      (by change c (-(i+1)) = c (-i-1); congr 1; ring)
  intro i _
  rw [hd, hd, show -(i-1)-1 = -i by ring, mirror_facePerm]
  have hinv : M.facePerm⁻¹ (toDart cyclicSubgraph_le (cycleForward hc (-i))) =
      toDart cyclicSubgraph_le (cycleForward hc (-i-1)) := by
    rw [Perm.inv_eq_iff_eq]
    exact (hface (-i) (Set.mem_univ _)).symm
  change (dartSymm G) (M.facePerm⁻¹ ((dartSymm G).symm
    (toDart cyclicSubgraph_le (cycleForward hc (-i))).symm)) = _
  have hsymm : (dartSymm G).symm (toDart cyclicSubgraph_le (cycleForward hc (-i))).symm =
      toDart cyclicSubgraph_le (cycleForward hc (-i)) := by
    change (dartSymm G)⁻¹ _ = _
    rw [mirror_dartSymm_inv_apply, Dart.symm_symm]
  rw [hsymm, hinv]
  rfl

/-- Reverse the old native facial order in the actual mirrored map. The new
face orbit is exactly the old selected face with its darts reversed. -/
theorem exists_mirrored_native_face_cycle [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) :
    ∃ q : G.Walk a a, ∃ hq : q.IsCycle, q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p (-(i : ZMod p.length))) ∧
      IsFacialCycleAlong (mirrorPlaneMap M) (walk_isCycleMap q hq) Set.univ ∧
      SameCycle (mirrorPlaneMap M).facePerm outer.symm (walkArcRoot q hq) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let c := walkCycleVertices p
  have hc := (walk_isCycleMap p hp).reverse
  have hfc := mirrored_cycle_isFacial M (walk_isCycleMap p hp) hface
  obtain ⟨r, hr, hrl, hro⟩ := exists_walk_of_cycleMap hlen hc
  have hz : c (-0) = a := by simp only [neg_zero, c, walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  let q := r.copy hz hz
  have hq : q.IsCycle := (Walk.isCycle_copy _ _).2 hr
  have hql : q.length = p.length := by simpa only [q, Walk.length_copy] using hrl
  have hqo : ∀ i ≤ p.length, q.getVert i = c (-(i : ZMod p.length)) := by simpa only [q, Walk.getVert_copy] using hro
  obtain ⟨hqf, hqroot⟩ := ordered_native_cycle_isFacial (mirrorPlaneMap M) hc hfc q hq hql hqo
  refine ⟨q, hq, hql, hqo, hqf, ?_⟩
  have hd : toDart cyclicSubgraph_le (cycleForward hc 0) =
      (toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) (-1))).symm := by
    apply (Dart.ext_iff _ _).2
    exact Prod.ext (by change c (-0) = c (-1+1); simp)
      (by change c (-(0+1)) = c (-1); simp)
  rw [hqroot, hd]
  exact (mirror_face_sameCycle M outer _).2
    (hroot.trans (facial_cycle_forward_sameCycle M (walk_isCycleMap p hp) hface (-1)))


/-- Reverse the actual facial order starting at any chosen old native vertex. -/
theorem exists_mirrored_native_face_cycle_at [Fintype V] (M : PlaneMap G) (outer : G.Dart)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (s : ℕ) (hs : s < p.length) :
    ∃ q : G.Walk (p.getVert s) (p.getVert s), ∃ hq : q.IsCycle, q.length = p.length ∧
      (∀ i ≤ p.length, q.getVert i = walkCycleVertices p ((s : ZMod p.length)-(i : ZMod p.length))) ∧
      IsFacialCycleAlong (mirrorPlaneMap M) (walk_isCycleMap q hq) Set.univ ∧
      SameCycle (mirrorPlaneMap M).facePerm outer.symm (walkArcRoot q hq) := by
  have hlen := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let c : ZMod p.length → V := fun i => walkCycleVertices p ((s : ZMod p.length)+i)
  have hc : IsCycleMap G c := {
    inj := fun x y h => add_left_cancel ((walk_isCycleMap p hp).inj h)
    adj := fun i => by simpa only [c, add_assoc] using (walk_isCycleMap p hp).adj ((s : ZMod p.length)+i) }
  have hd : ∀ i, toDart cyclicSubgraph_le (cycleForward hc i) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) ((s : ZMod p.length)+i)) := by
    intro i
    apply (Dart.ext_iff _ _).2
    exact Prod.ext rfl (by change walkCycleVertices p ((s : ZMod p.length)+(i+1)) = walkCycleVertices p (((s : ZMod p.length)+i)+1); rw [add_assoc])
  have hfc : IsFacialCycleAlong M hc Set.univ := by
    intro i _
    rw [hd, hd, show (s : ZMod p.length)+(i-1) = ((s : ZMod p.length)+i)-1 by ring]
    exact hface _ (Set.mem_univ _)
  obtain ⟨r, hr, hrl, hro⟩ := exists_walk_of_cycleMap hlen hc.reverse
  have hz : c (-0) = p.getVert s := by
    change walkCycleVertices p ((s : ZMod p.length)+ -0) = _
    rw [neg_zero, add_zero, walkCycleVertices_nat_le p hs.le]
  let q := r.copy hz hz
  have hq : q.IsCycle := (Walk.isCycle_copy _ _).2 hr
  have hql : q.length = p.length := by simpa only [q, Walk.length_copy] using hrl
  have hqo : ∀ i ≤ p.length, q.getVert i = c (-(i : ZMod p.length)) := by simpa only [q, Walk.getVert_copy] using hro
  obtain ⟨hqf, hqroot⟩ := ordered_native_cycle_isFacial (mirrorPlaneMap M) hc.reverse
    (mirrored_cycle_isFacial M hc hfc) q hq hql hqo
  refine ⟨q, hq, hql, ?_, hqf, ?_⟩
  · simpa only [c, sub_eq_add_neg] using hqo
  · have he : toDart cyclicSubgraph_le (cycleForward hc.reverse 0) =
        (toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) ((s : ZMod p.length)-1))).symm := by
      apply (Dart.ext_iff _ _).2
      exact Prod.ext (by change walkCycleVertices p ((s : ZMod p.length)+ -0) = walkCycleVertices p (((s : ZMod p.length)-1)+1); simp)
        (by change walkCycleVertices p ((s : ZMod p.length)+ -(0+1)) = walkCycleVertices p ((s : ZMod p.length)-1); simp [sub_eq_add_neg])
    rw [hqroot, he]
    exact (mirror_face_sameCycle M outer _).2
      (hroot.trans (facial_cycle_forward_sameCycle M (walk_isCycleMap p hp) hface _))

namespace BoundaryInstance
variable {C : Type v}

/-- Mirror the embedding while retaining every original list, prescribed
colour, native prescribed path/cycle and short-edge condition. -/
def mirror (I : BoundaryInstance G C) : BoundaryInstance G C where
  girth := I.girth
  embedding := mirrorPlaneMap I.embedding
  outer := I.outer.symm
  precolor := I.precolor
  lists := I.lists
  prescribed := I.prescribed
  on_outer := fun x hx => (mirror_onOuterFace_iff I.embedding I.outer x).2 (I.on_outer x hx)
  singleton := I.singleton
  proper_precolor := I.proper_precolor
  boundary_lists := fun x hx hp => I.boundary_lists x ((mirror_onOuterFace_iff I.embedding I.outer x).1 hx) hp
  interior_lists := fun x hx => I.interior_lists x (fun h => hx ((mirror_onOuterFace_iff I.embedding I.outer x).2 h))
  short_edges := I.short_edges


variable [Fintype V]

/-- The prescription-free three-path reduction also applies when its terminal
boundary endpoint has a short list. Mirroring preserves actual face geometry
and transports the exact open native arc. -/
theorem colourable_of_interior_three_path_free_arc_terminal_short (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hnshort : (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n-2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨q, hq, hql, hqo, hqf, hqr⟩ := exists_mirrored_native_face_cycle_at I.embedding I.outer p hp hface hroot n (by omega)
  have hqn : q.getVert n = a := by
    rw [hqo n (by omega), sub_self]
    simp only [walkCycleVertices, ZMod.val_zero, Walk.getVert_zero]
  have hfree : ∀ x ∈ I.mirror.precolor.vertices, x ∉ cycleInterval (walkCycleVertices q) 1 (n-2) := by
    intro x hx hxArc
    obtain ⟨j, hj, hjx⟩ := hxArc
    rw [walkCycleVertices_nat_le q (by omega : 1+j ≤ q.length), hqo (1+j) (by omega),
      ← Nat.cast_sub (by omega : 1+j ≤ n)] at hjx
    apply hPoutside x hx
    refine ⟨n-j-2, by omega, ?_⟩
    have he : 1+(n-j-2) = n-(1+j) := by omega
    simpa only [he] using hjx
  have hu' : ¬ OnOuterFace I.mirror.embedding I.mirror.outer u :=
    fun h => hu ((mirror_onOuterFace_iff I.embedding I.outer u).1 h)
  have hv' : ¬ OnOuterFace I.mirror.embedding I.mirror.outer v :=
    fun h => hv ((mirror_onOuterFace_iff I.embedding I.outer v).1 h)
  exact I.mirror.colourable_of_interior_three_path_free_arc hG q hq hqf hqr n hn (by omega)
    v u hv' hu' hvn huv.symm (by rwa [hqn]) hnshort hfree hsmall

/-- A short list at either boundary endpoint closes this prescription-free
three-path cut. Both orientations use actual native face orbits. -/
theorem colourable_of_interior_three_path_free_arc_one_short_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u a) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hshort : (I.lists a).card ≤ 2 ∨ (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) 1 (n-2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  rcases hshort with h | h
  · exact I.colourable_of_interior_three_path_free_arc hG p hp hface hroot n hn hnp u v hu hv hua huv hvn h hPoutside hsmall
  · exact I.colourable_of_interior_three_path_free_arc_terminal_short hG p hp hface hroot n hn hnp u v hu hv hua huv hvn h hPoutside hsmall

end BoundaryInstance
end Thomassen
