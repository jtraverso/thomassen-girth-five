/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Grotzsch.FacialCycle

/-!
# Faces do not repeat vertices when vertex deletion preserves connectivity

Splitting a vertex rotation at two occurrences on one face increases both the
vertex and face cycle counts. If deleting the vertex leaves its neighbours
connected, the split map stays connected, contradicting Euler's inequality.
This adapts the rotation-splitting argument in the registered `cycle_facial` proof.
-/

@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Finite V] {G : SimpleGraph V}

lemma eq_of_same_face_of_fst (M : PlaneMap G) {d e : G.Dart}
    (hface : SameCycle M.facePerm d e) (hfst : d.fst = e.fst)
    (hconn : ∀ a b, a ≠ d.fst → b ≠ d.fst → RIn G ({d.fst} : Set V)ᶜ a b) :
    d = e := by
  by_contra hde
  let v := d.fst
  let x := M.rot⁻¹ d
  let y := M.rot⁻¹ e
  let α := dartSymm G
  let σ := M.rot * swap x y
  let R := compSetoid σ α
  have hxy : x ≠ y := fun h => hde (by simpa [x, y] using congrArg M.rot h)
  have hx : x.fst = v := fst_rot_inv M d
  have hy : y.fst = v := (fst_rot_inv M e).trans hfst.symm
  have hoff : ∀ z : G.Dart, z.fst ≠ v → σ z = M.rot z := by
    intro z hz
    change M.rot (swap x y z) = M.rot z
    rw [swap_apply_of_ne_of_ne
      (fun h => hz ((congrArg (fun t : G.Dart => t.fst) h).trans hx))
      (fun h => hz ((congrArg (fun t : G.Dart => t.fst) h).trans hy))]
  have key : ∀ a b, RIn G ({v} : Set V)ᶜ a b → a ≠ v →
      ∀ p q : G.Dart, p.fst = a → q.fst = b → R p q := by
    intro a b hab ha
    induction hab with
    | refl =>
      intro p q hp hq
      refine compSetoid_of_sameCycle_left ?_
      refine sameCycle_of_agree (fun t : G.Dart => t.fst) M.isRotationSystem.fst_apply
        (c := p.fst) (fun z hz => hoff z (by rw [hz, hp]; exact ha)) rfl
        (M.isRotationSystem.sameCycle p q (hp.trans hq.symm))
    | @tail b c _ hbc ih =>
      intro p q hp hq
      let z : G.Dart := ⟨(b, c), hbc.1⟩
      have h1 := ih p z hp rfl
      have h2 : R z z.symm := compSetoid_right _ _ z
      have h3 : R z.symm q := by
        refine compSetoid_of_sameCycle_left ?_
        refine sameCycle_of_agree (fun t : G.Dart => t.fst) M.isRotationSystem.fst_apply
          (c := c) (fun z' hz' => hoff z' (hz' ▸ hbc.2.2)) rfl
          (M.isRotationSystem.sameCycle _ _ hq.symm)
      exact R.trans h1 (R.trans h2 h3)
  have hx' : x.snd ≠ v := fun h => x.adj.ne (hx.trans h.symm)
  have hy' : y.snd ≠ v := fun h => y.adj.ne (hy.trans h.symm)
  have hlink : R x y :=
    R.trans (compSetoid_right σ α x)
      (R.trans (key _ _ (hconn _ _ hx' hy') hx' x.symm y.symm rfl rfl)
        (R.symm (compSetoid_right σ α y)))
  have hK : numComponents σ α ≤ numComponents M.rot α := by
    apply numClasses_le_of_le
    intro a b hab
    exact compSetoid_le R
      (rel_apply_of_mulSwap R M.rot x y (compSetoid_left σ α) hlink)
      (compSetoid_right σ α) hab
  have hcrot : cycleCount σ = cycleCount M.rot + 1 :=
    cycleCount_mul_swap_of_sameCycle hxy
      (M.isRotationSystem.sameCycle x y (hx.trans hy.symm))
  have hfaces : SameCycle (M.rot * α) (α⁻¹ x) (α⁻¹ y) := by
    have hd : (M.rot * α) (α⁻¹ x) = d := by simp [x]
    have he : (M.rot * α) (α⁻¹ y) = e := by simp [y]
    have h : SameCycle (M.rot * α) ((M.rot * α) (α⁻¹ x))
        ((M.rot * α) (α⁻¹ y)) := by rw [hd, he]; exact hface
    exact h.of_apply_left.of_apply_right
  have hcface := cycleCount_mul_swap_of_sameCycle
    (show α⁻¹ x ≠ α⁻¹ y from fun h => hxy (α.symm.injective h)) hfaces
  have hφ : σ * α = M.rot * α * swap (α⁻¹ x) (α⁻¹ y) :=
    mulSwap_mul_eq M.rot α x y
  have h0 := M.eulerDefect_eq_zero
  have hnn := eulerDefect_nonneg σ α
  change eulerDefect M.rot α = 0 at h0
  unfold eulerDefect at h0 hnn
  rw [hcrot, hφ, hcface] at hnn
  push_cast at hnn
  omega

/-- Native deletion connectivity implies that the tail map on each face orbit is injective. -/
lemma face_fst_injective_of_delete_preconnected (M : PlaneMap G)
    (hconn : ∀ v, (G.induce ({v} : Set V)ᶜ).Preconnected) (outer : G.Dart) :
    Function.Injective (fun e : FaceApex.F M outer => e.1.fst) := by
  intro d e hfst
  apply Subtype.ext
  apply eq_of_same_face_of_fst M (d.property.symm.trans e.property) hfst
  intro a b ha hb
  have : Nonempty ↥(({d.1.fst} : Set V)ᶜ) := ⟨⟨a, ha⟩⟩
  have hc : (G.induce ({d.1.fst} : Set V)ᶜ).Connected :=
    SimpleGraph.Connected.mk (hconn d.1.fst)
  exact ((connSet_iff_induce_connected _ _).2 hc).2 a ha b hb

end Thomassen
