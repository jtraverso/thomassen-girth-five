/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FaceBoundary
public import Thomassen.ArcPathSeparation
public import Thomassen.CycleMapWalk
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! The actual cycle of a face when vertex deletion preserves connectivity. -/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Finite V] {G : SimpleGraph V}

/-- The period of the selected dart in the actual face permutation. -/
noncomputable def faceOrbitLength (M : PlaneMap G) (o : G.Dart) : ℕ :=
  Function.minimalPeriod M.facePerm o

/-- The actual face darts, in face-permutation order. -/
noncomputable def faceOrbitDart (M : PlaneMap G) (o : G.Dart) :
    ZMod (faceOrbitLength M o) → G.Dart := fun i => M.facePerm^[i.val] o

/-- The actual vertices, in face-permutation order. -/
noncomputable def faceOrbitVertex (M : PlaneMap G) (o : G.Dart) :
    ZMod (faceOrbitLength M o) → V := fun i => (faceOrbitDart M o i).fst

lemma faceOrbitLength_pos (M : PlaneMap G) (o : G.Dart) : 0 < faceOrbitLength M o :=
  Function.minimalPeriod_pos_of_mem_periodicPts (M.facePerm.injective.mem_periodicPts o)

lemma faceOrbitLength_three_le (M : PlaneMap G)
    (hdeg : ∀ x, 2 ≤ Nat.card {y // G.Adj x y}) (o : G.Dart) :
    3 ≤ faceOrbitLength M o := by
  have hpos := faceOrbitLength_pos M o
  have hper := Function.iterate_minimalPeriod (f := M.facePerm) (x := o)
  change M.facePerm^[faceOrbitLength M o] o = o at hper
  by_contra h
  have hcases : faceOrbitLength M o = 1 ∨ faceOrbitLength M o = 2 := by omega
  rcases hcases with hlen | hlen
  · rw [hlen, Function.iterate_one] at hper
    exact face_ne_self M.isRotationSystem o hper
  · rw [hlen, Function.iterate_succ_apply', Function.iterate_one] at hper
    exact face_face_ne_self M.isRotationSystem hdeg o hper

omit [Finite V] in
lemma faceOrbitDart_sameCycle (M : PlaneMap G) (o : G.Dart) (i : ZMod (faceOrbitLength M o)) :
    SameCycle M.facePerm o (faceOrbitDart M o i) := by
  change SameCycle M.facePerm o (M.facePerm^[i.val] o)
  rw [← Perm.coe_pow]
  exact (SameCycle.refl _ _).pow_right

lemma faceOrbitDart_injective (M : PlaneMap G) (o : G.Dart) :
    Function.Injective (faceOrbitDart M o) := by
  let : NeZero (faceOrbitLength M o) := ⟨(faceOrbitLength_pos M o).ne'⟩
  intro i j hij
  apply ZMod.val_injective
  exact Function.iterate_injOn_Iio_minimalPeriod (ZMod.val_lt i) (ZMod.val_lt j) hij

omit [Finite V] in
lemma faceOrbitDart_next (M : PlaneMap G) (o : G.Dart) (hk : 1 < faceOrbitLength M o)
    (i : ZMod (faceOrbitLength M o)) :
    faceOrbitDart M o (i + 1) = M.facePerm (faceOrbitDart M o i) := by
  let : Fact (1 < faceOrbitLength M o) := ⟨hk⟩
  change M.facePerm^[(i + 1).val] o = M.facePerm (M.facePerm^[i.val] o)
  rw [ZMod.val_add, ZMod.val_one]
  change M.facePerm^[(i.val + 1) % Function.minimalPeriod M.facePerm o] o = _
  rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

lemma faceOrbitVertex_injective (M : PlaneMap G) (o : G.Dart)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    Function.Injective (faceOrbitVertex M o) := by
  intro i j hij
  apply faceOrbitDart_injective M o
  have hinj := face_fst_injective_of_delete_preconnected M hconn o
  have heq := hinj (a₁ := ⟨faceOrbitDart M o i, faceOrbitDart_sameCycle M o i⟩)
    (a₂ := ⟨faceOrbitDart M o j, faceOrbitDart_sameCycle M o j⟩) hij
  exact congrArg Subtype.val heq

lemma faceOrbitVertex_isCycleMap (M : PlaneMap G) (o : G.Dart)
    (hk : 1 < faceOrbitLength M o)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsCycleMap G (faceOrbitVertex M o) := by
  refine ⟨faceOrbitVertex_injective M o hconn, ?_⟩
  intro i
  change G.Adj (faceOrbitDart M o i).fst (faceOrbitDart M o (i + 1)).fst
  rw [faceOrbitDart_next M o hk]
  rw [show (M.facePerm (faceOrbitDart M o i)).fst = (faceOrbitDart M o i).snd
    from M.isRotationSystem.fst_apply _]
  exact (faceOrbitDart M o i).adj

lemma faceOrbitVertex_range (M : PlaneMap G) (o : G.Dart) :
    Set.range (faceOrbitVertex M o) = {x | OnOuterFace M o x} := by
  let : NeZero (faceOrbitLength M o) := ⟨(faceOrbitLength_pos M o).ne'⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨faceOrbitDart M o i, faceOrbitDart_sameCycle M o i, rfl⟩
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    change (M.facePerm^[(n : ZMod (faceOrbitLength M o)).val] o).fst = x
    rw [ZMod.val_natCast]
    change (M.facePerm^[n % Function.minimalPeriod M.facePerm o] o).fst = x
    rw [Function.iterate_mod_minimalPeriod_eq, ← Perm.coe_pow, hn, hdx]

/-- The corner equations of the extracted cycle are the original face equations. -/
lemma faceOrbitVertex_isFacial (M : PlaneMap G) (o : G.Dart)
    (hk : 1 < faceOrbitLength M o)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    IsFacialCycleAlong M (faceOrbitVertex_isCycleMap M o hk hconn) Set.univ := by
  have hd : ∀ i : ZMod (faceOrbitLength M o),
      toDart cyclicSubgraph_le (cycleForward (faceOrbitVertex_isCycleMap M o hk hconn) i) =
        faceOrbitDart M o i := by
    intro i
    apply (Dart.ext_iff _ _).2
    refine Prod.ext rfl ?_
    change faceOrbitVertex M o (i + 1) = (faceOrbitDart M o i).snd
    change (faceOrbitDart M o (i + 1)).fst = _
    rw [faceOrbitDart_next M o hk]
    exact M.isRotationSystem.fst_apply _
  intro i _
  rw [hd, hd, ← faceOrbitDart_next M o hk, sub_add_cancel]

/-- With deletion connectivity and minimum degree two, the selected face is an
actual native simple cycle, with precisely its face vertices and all original
face-corner equations. This constructs the boundary rather than assuming one. -/
theorem exists_native_face_cycle (M : PlaneMap G) (o : G.Dart)
    (hdeg : ∀ x, 2 ≤ Nat.card {y // G.Adj x y})
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength M o ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace M o x) ∧
      IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = o := by
  have hk := faceOrbitLength_three_le M hdeg o
  let : NeZero (faceOrbitLength M o) := ⟨by omega⟩
  obtain ⟨p, hp, hlen, hget⟩ := exists_walk_of_cycleMap hk
    (faceOrbitVertex_isCycleMap M o (by omega) hconn)
  let : NeZero p.length := ⟨by omega⟩
  have hgetFace : ∀ i ≤ p.length, p.getVert i = (M.facePerm^[i] o).fst := by
    intro i hi
    rw [hget i (by omega)]
    change (M.facePerm^[(i : ZMod (faceOrbitLength M o)).val] o).fst = _
    rw [ZMod.val_natCast]
    change (M.facePerm^[i % Function.minimalPeriod M.facePerm o] o).fst = _
    rw [Function.iterate_mod_minimalPeriod_eq]
  have hnext : ∀ i : ZMod p.length, M.facePerm^[(i + 1).val] o =
      M.facePerm (M.facePerm^[i.val] o) := by
    intro i
    let : Fact (1 < p.length) := ⟨by omega⟩
    rw [ZMod.val_add, ZMod.val_one]
    generalize i.val = j
    rw [hlen]
    change M.facePerm^[(j + 1) % Function.minimalPeriod M.facePerm o] o = _
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']
  have hforward : ∀ i : ZMod p.length,
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) i) = M.facePerm^[i.val] o := by
    intro i
    apply (Dart.ext_iff _ _).2
    apply Prod.ext
    · exact hgetFace i.val (ZMod.val_lt i).le
    · change walkCycleVertices p (i + 1) = _
      rw [walkCycleVertices_next p (by omega), hgetFace (i.val + 1) (by have := ZMod.val_lt i; omega)]
      rw [Function.iterate_succ_apply']
      exact M.isRotationSystem.fst_apply _
  refine ⟨_, p, hp, hlen, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
      refine ⟨M.facePerm^[i] o, ?_, ?_⟩
      · rw [← Perm.coe_pow]
        exact (SameCycle.refl _ _).pow_right
      · exact (hgetFace i hi).symm.trans hix
    · intro hx
      obtain ⟨i, hi⟩ : x ∈ Set.range (faceOrbitVertex M o) := by
        rwa [faceOrbitVertex_range M o]
      have hval := ZMod.val_lt i
      have heq : p.getVert i.val = x := by
        rw [hget i.val hval.le, ZMod.natCast_zmod_val, hi]
      exact heq ▸ p.getVert_mem_support i.val
  · intro i _
    rw [hforward, hforward]
    simpa only [sub_add_cancel] using (hnext (i - 1)).symm
  · change toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap p hp) 0) = o
    rw [hforward, ZMod.val_zero, Function.iterate_zero, id_eq]

/-- A connected graph on at least three vertices whose vertex deletions remain
preconnected has minimum degree at least two. -/
lemma two_le_card_neighbours_of_delete_preconnected (hG : G.Preconnected)
    (hcard : 3 ≤ Nat.card V)
    (hdelete : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∀ x, 2 ≤ Nat.card {y // G.Adj x y} := by
  let : Fintype V := Fintype.ofFinite V
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  intro x
  by_contra h
  let : Subsingleton {y // G.Adj x y} := Finite.card_le_one_iff_subsingleton.1 (by omega)
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).1 (hG.degree_pos_of_nontrivial x)
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {x, y}) (t := Finset.univ) (by
      have hpair : ({x, y} : Finset V).card ≤ 2 := by simpa only [Finset.card_singleton] using Finset.card_insert_le x ({y} : Finset V)
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      omega)
  have hzx : z ≠ x := fun heq => hz (by simp [heq])
  have hzy : z ≠ y := fun heq => hz (by simp [heq])
  let v : ({y}ᶜ : Set V) := ⟨x, hxy.ne⟩
  let w : ({y}ᶜ : Set V) := ⟨z, hzy⟩
  have hvw : v ≠ w := fun heq => hzx (congrArg Subtype.val heq).symm
  obtain ⟨t, ht⟩ := ((hdelete y) v w).nonempty_neighborSet_left hvw
  have hty : t.1 = y := congrArg Subtype.val (Subsingleton.elim
    (⟨t.1, ht⟩ : {a // G.Adj x a}) ⟨y, hxy⟩)
  exact t.2 hty

/-- Native facial-cycle normalization from deletion connectivity alone, once
the connected graph has at least three vertices. -/
theorem exists_native_face_cycle_of_delete_preconnected (M : PlaneMap G) (o : G.Dart)
    (hG : G.Preconnected) (hcard : 3 ≤ Nat.card V)
    (hdelete : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) :
    ∃ a, ∃ p : G.Walk a a, ∃ hp : p.IsCycle, p.length = faceOrbitLength M o ∧
      (∀ x, x ∈ p.support ↔ OnOuterFace M o x) ∧
      IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ ∧ walkArcRoot p hp = o :=
  exists_native_face_cycle M o (two_le_card_neighbours_of_delete_preconnected hG hcard hdelete) hdelete

end Thomassen
