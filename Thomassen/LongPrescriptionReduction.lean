/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SingletonPrescriptionClosure

/-! Every remaining minimal counterexample has a path on four to six vertices. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Empty prescriptions, singleton prescriptions, edges, three-vertex paths
and all permitted cycles are complete strict-induction cases. Thus a remaining
counterexample must prescribe a native path on four to six vertices. -/
theorem remaining_counterexample_has_four_to_six_prescribed_vertices (I : BoundaryInstance G C)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ a t : V, ∃ (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6),
      I.precolor = .path r hr hn ∧ 3 ≤ r.length ∧ r.length ≤ 5 := by
  cases hP : I.precolor with
  | empty => exact (hbad (I.colourable_of_empty_prescription hP hsmall)).elim
  | @path a t r hr hn =>
    have hlen : r.length ≤ 5 := by
      rw [List.toFinset_card_of_nodup hr.support_nodup,Walk.length_support] at hn
      omega
    by_cases h0 : r.length=0
    · have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x=a := by
        intro x
        simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
        constructor
        · intro hx
          obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.1 hx
          have hk0 : k=0 := by omega
          simpa only [hk0,Walk.getVert_zero] using hk.symm
        · intro hx; rw [hx]; exact r.start_mem_support
      exact (hbad (I.colourable_of_singleton_prescription a hPv hsmall)).elim
    by_cases h1 : r.length=1
    · exact (hbad (I.colourable_of_prescribed_edge r hr hn hP h1 hsmall)).elim
    by_cases h2 : r.length=2
    · exact (hbad (I.colourable_of_three_vertex_prescribed_path r hr hn hP h2 hsmall)).elim
    exact ⟨a,t,r,hr,hn,rfl,by omega,hlen⟩
  | @cycle a r hr hn =>
    have hPv : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ r.support := by
      intro x; simp only [hP,BoundaryPrecolor.vertices,List.mem_toFinset]
    exact (hbad (I.colourable_of_prescribed_cycle r hr hn hPv hsmall)).elim

end Thomassen.BoundaryInstance
