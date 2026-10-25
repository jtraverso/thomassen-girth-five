/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalTripleGeometry

/-! The two endpoint obstructions of the residual edge in original step (10). -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Simple two-paths are exactly common-neighbour witnesses with distinct ends. -/
theorem exists_two_path_iff_common_neighbour (x z : V) :
    (∃ p : G.Walk x z, p.IsPath ∧ p.length=2) ↔ x ≠ z ∧ ∃ w, G.Adj x w ∧ G.Adj w z := by
  constructor
  · rintro ⟨p,hp,hlen⟩
    have hlast : p.getVert 2 = z := by simpa only [hlen] using p.getVert_length
    have hne : x ≠ z := by
      intro he
      have hidx := hp.getVert_injOn (show 0 ≤ p.length from by omega)
        (show 2 ≤ p.length from by omega) (by simpa only [Walk.getVert_zero,hlast] using he)
      omega
    refine ⟨hne,p.getVert 1,?_,?_⟩
    · simpa only [Walk.getVert_zero,zero_add] using p.adj_getVert_succ (by omega : 0 < p.length)
    · simpa only [hlast] using p.adj_getVert_succ (by omega : 1 < p.length)
  · rintro ⟨hxz,w,hxw,hwz⟩
    let p : G.Walk x z := .cons hxw (.cons hwz .nil)
    exact ⟨p,by simp [p,Walk.isPath_def,hxz,hxw.ne,hwz.ne],rfl⟩

/-- Failure of the original short-set condition implies a short edge exists. -/
theorem OriginalShortSet.exists_edge_of_not (A : Set V) (hbad : ¬ OriginalShortSet G A) :
    ∃ x ∈ A, ∃ y ∈ A, G.Adj x y := by
  by_contra hn
  exact hbad (Or.inl (fun x hx y hy hxy => hn ⟨x,hx,y,hy,hxy⟩))

/-- If there is only one short edge and the original condition fails, each
of its two endpoints has a simple two-path to the short set. These are the
obstructions at q₁ and q₂ used separately in original step (10). -/
theorem OriginalShortSet.endpoint_obstructions (A : Set V) (hbad : ¬ OriginalShortSet G A)
    (x y : V) (hx : x ∈ A) (hy : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r=x ∧ s=y) ∨ (r=y ∧ s=x)) :
    (∃ z ∈ A, x ≠ z ∧ ∃ w, G.Adj x w ∧ G.Adj w z) ∧
      (∃ z ∈ A, y ≠ z ∧ ∃ w, G.Adj y w ∧ G.Adj w z) := by
  have key : ∀ (u v : V), u ∈ A → v ∈ A → G.Adj u v →
      (∀ r ∈ A, ∀ s ∈ A, G.Adj r s → (r=u ∧ s=v) ∨ (r=v ∧ s=u)) →
      ∃ z ∈ A, u ≠ z ∧ ∃ w, G.Adj u w ∧ G.Adj w z := by
    intro u v hu hv huv hE
    by_contra hn
    apply hbad
    refine Or.inr ⟨u,v,hu,hv,huv,hE,?_⟩
    intro z hz p hp hlen
    have ⟨hne,w,huw,hwz⟩ := (exists_two_path_iff_common_neighbour u z).1 ⟨p,hp,hlen⟩
    exact hn ⟨z,hz,hne,w,huw,hwz⟩
  exact ⟨key x y hx hy hxy hedge,key y x hy hx hxy.symm
    (fun r hr s hs hrs => (hedge r hr s hs hrs).symm)⟩

end Thomassen
