module
public import Thomassen.OriginalShortSetTransport

/-! Independent contracts for the actual residual deletions in source (9),(10).
The exact full Theorem 2.1 remains a separate pending target. -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

def exposedShortSet (G : SimpleGraph V) (A : Set V) (D : Finset V) : Set V :=
  {z | z ∉ D ∧ (z ∈ A ∨ ∃ w ∈ D, G.Adj z w)}


section
variable [Fintype V]
theorem OriginalBoundaryInstance.extends_of_residual_components (I : OriginalBoundaryInstance G C)
    (D : Finset V) (hD : D.Nonempty) (f : V → C)
    (hf : ∀ x ∈ D, f x ∈ I.lists x)
    (hproper : ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → f x ≠ f y)
    (haD : I.a ∉ D) (hbD : I.b ∉ D) (A : Set V)
    (hshape : OriginalShortSet (G.induce (↑D : Set V)ᶜ) {x | x.1 ∈ A})
    (htwo : ∀ x, x ∉ D → 2 ≤ (residual G I.lists D f x).card)
    (hthree : ∀ x, x ∉ D → x ∉ A → 3 ≤ (residual G I.lists D f x).card)
    (hta : I.ta ∈ residual G I.lists D f I.a) (htb : I.tb ∈ residual G I.lists D f I.b)
    (hfaces : ∀ K : (G.induce (↑D : Set V)ᶜ).ConnectedComponent,
      ∀ [Nontrivial (componentVertexSet (↑D : Set V)ᶜ K)],
      ∃ o : (G.induce (componentVertexSet (↑D : Set V)ᶜ K)).Dart,
        (∀ x : componentVertexSet (↑D : Set V)ᶜ K, x.1 ∈ A →
          OnOuterFace (inducedPlaneMap I.embedding (componentVertexSet (↑D : Set V)ᶜ K)) o x) ∧
        (∀ x : componentVertexSet (↑D : Set V)ᶜ K, OnOuterFace I.embedding I.outer x.1 →
          OnOuterFace (inducedPlaneMap I.embedding (componentVertexSet (↑D : Set V)ᶜ K)) o x))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

theorem OriginalBoundaryInstance.extends_of_connected_boundary_deletion (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : Equiv.Perm.SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (D : Finset V) (ha : a ∈ D) (hD : ConnSet G (↑D : Set V)) (f : V → C)
    (hf : ∀ x ∈ D, f x ∈ I.lists x)
    (hproper : ∀ x ∈ D, ∀ y ∈ D, G.Adj x y → f x ≠ f y)
    (haD : I.a ∉ D) (hbD : I.b ∉ D) (A : Set V)
    (hshape : OriginalShortSet (G.induce (↑D : Set V)ᶜ) {x | x.1 ∈ A})
    (hA : ∀ x ∈ A, x ∈ I.short ∨ ∃ y ∈ D, G.Adj x y)
    (htwo : ∀ x, x ∉ D → 2 ≤ (residual G I.lists D f x).card)
    (hthree : ∀ x, x ∉ D → x ∉ A → 3 ≤ (residual G I.lists D f x).card)
    (hta : I.ta ∈ residual G I.lists D f I.a) (htb : I.tb ∈ residual G I.lists D f I.b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  sorry

end

section
theorem exceptional_pair_old_list_unchanged (A : Set V) (x y : V) (hxA : x ∈ A) (hyA : y ∈ A)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (f : V → C) {z : V} (hzA : z ∈ A) (hzx : z ≠ x) (hzy : z ≠ y) :
    residual G L {x,y} f z = L z := by
  sorry

theorem exceptional_pair_short_vertices_independent (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V)
    (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (hNoX : ∀ z ∈ A, ∀ p : G.Walk x z, p.IsPath → p.length = 2 → False)
    (hNoY : ∀ z ∈ A, z ≠ x → z ≠ y → ∀ w, w ≠ x → w ≠ y → G.Adj y w → G.Adj w z → False)
    {z w : V} (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y)
    (hz : z ∈ A ∨ G.Adj x z ∨ G.Adj y z)
    (hw : w ∈ A ∨ G.Adj x w ∨ G.Adj y w) : ¬ G.Adj z w := by
  sorry

theorem exceptional_pair_residual_card_ge_two (hg : 5 ≤ G.egirth)
    (A : Set V) (x y : V) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r = x ∧ s = y) ∨ (r = y ∧ s = x))
    (L : V → Finset C) (hLtwo : ∀ z, 2 ≤ (L z).card)
    (hLthree : ∀ z, z ∉ A → 3 ≤ (L z).card) (f : V → C)
    {z : V} (hzx : z ≠ x) (hzy : z ≠ y) : 2 ≤ (residual G L {x,y} f z).card := by
  sorry

end

section
variable [Fintype V]
theorem OriginalBoundaryInstance.predecessor_mem_short_of_minimal_counterexample (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) :
    p.getVert (p.length-1) ∈ I.short := by
  sorry

end

section
variable [Fintype V]
theorem OriginalBoundaryInstance.short_closed_prefix_neighbours (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (n : ℕ) (hn : 2 ≤ n) (hnp : n+2 ≤ p.length)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hql : 0 < q.length) (hshort : n+q.length ≤ 6)
    (hInner : ∀ j, 0 < j → j < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert j))
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    (i : ℕ) (hi : 0 < i) (hin : i < n) :
    ∀ z, G.Adj (p.getVert i) z → z=p.getVert (i-1) ∨ z=p.getVert (i+1) := by
  sorry

theorem OriginalBoundaryInstance.boundary_three_path_first_vertex (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y : V)
    (hxface : OnOuterFace I.embedding I.outer x) (hx1 : x ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y)
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    x=p.getVert 3 ∧
      (∀ z, G.Adj (p.getVert 2) z → z=p.getVert 1 ∨ z=x) ∧
      (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) := by
  sorry

theorem OriginalBoundaryInstance.three_path_across_two_face_edges_unique_allow_boundary (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y x' y' : V)
    (hx1 : x ≠ p.getVert 1) (hx1' : x' ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y) (hy' : ¬ OnOuterFace I.embedding I.outer y')
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (h2x' : G.Adj (p.getVert 2) x') (hxy' : G.Adj x' y') (hya' : G.Adj y' a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : x=x' ∧ y=y' := by
  sorry

end

section
variable [Fintype V]
theorem OriginalBoundaryInstance.triple_short_edge_crossing (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htA : p.getVert (p.length-1) ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False)
    {u v : V}
    (hu : u ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hv : v ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}) (huv : G.Adj u v) :
    u ∉ I.short ∧ v ∉ I.short ∧
      ((G.Adj (p.getVert 2) u ∧ G.Adj a v ∧ ¬ OnOuterFace I.embedding I.outer v) ∨
       (G.Adj a u ∧ G.Adj (p.getVert 2) v ∧ ¬ OnOuterFace I.embedding I.outer u)) := by
  sorry

theorem OriginalBoundaryInstance.triple_short_edge_unique (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htA : p.getVert (p.length-1) ∈ I.short)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False)
    {q₁ q₂ : V}
    (hq₁ : q₁ ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (hq₂ : q₂ ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2})
    (h2q : G.Adj (p.getVert 2) q₁) (hqq : G.Adj q₁ q₂) (hqa : G.Adj q₂ a) :
    ∀ u ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2},
      ∀ v ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}, G.Adj u v →
        (u=q₁ ∧ v=q₂) ∨ (u=q₂ ∧ v=q₁) := by
  sorry

end

section
theorem exists_two_path_iff_common_neighbour (x z : V) :
    (∃ p : G.Walk x z, p.IsPath ∧ p.length=2) ↔ x ≠ z ∧ ∃ w, G.Adj x w ∧ G.Adj w z := by
  sorry

theorem OriginalShortSet.exists_edge_of_not (A : Set V) (hbad : ¬ OriginalShortSet G A) :
    ∃ x ∈ A, ∃ y ∈ A, G.Adj x y := by
  sorry

theorem OriginalShortSet.endpoint_obstructions (A : Set V) (hbad : ¬ OriginalShortSet G A)
    (x y : V) (hx : x ∈ A) (hy : y ∈ A) (hxy : G.Adj x y)
    (hedge : ∀ r ∈ A, ∀ s ∈ A, G.Adj r s →
      (r=x ∧ s=y) ∨ (r=y ∧ s=x)) :
    (∃ z ∈ A, x ≠ z ∧ ∃ w, G.Adj x w ∧ G.Adj w z) ∧
      (∃ z ∈ A, y ≠ z ∧ ∃ w, G.Adj y w ∧ G.Adj w z) := by
  sorry

end

section
variable [Fintype V]
theorem OriginalBoundaryInstance.triple_residual_short_set_not_original (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htcard : (I.lists (p.getVert (p.length-1))).card=2)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) :
    ¬ OriginalShortSet (G.induce (↑({a,p.getVert 1,p.getVert 2} : Finset V) : Set V)ᶜ)
      {z | z.1 ∈ exposedShortSet G I.short {a,p.getVert 1,p.getVert 2}} := by
  sorry

theorem OriginalBoundaryInstance.triple_residual_edge_and_endpoint_obstructions (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hyA : p.getVert 1 ∈ I.short) (hxA : p.getVert 2 ∈ I.short)
    (htcard : (I.lists (p.getVert (p.length-1))).card=2)
    (hedge : ∀ r ∈ I.short, ∀ s ∈ I.short, G.Adj r s →
      (r = p.getVert 2 ∧ s = p.getVert 1) ∨ (r = p.getVert 1 ∧ s = p.getVert 2))
    (hNoX : ∀ z ∈ I.short, ∀ r : G.Walk (p.getVert 2) z, r.IsPath → r.length = 2 → False) :
    let D : Finset V := {a,p.getVert 1,p.getVert 2}
    let Q : Set V := (↑D : Set V)ᶜ
    let A : Set Q := {z | z.1 ∈ exposedShortSet G I.short D}
    ∃ q₁ q₂ : Q, q₁ ∈ A ∧ q₂ ∈ A ∧ (G.induce Q).Adj q₁ q₂ ∧
      q₁.1 ∉ I.short ∧ q₂.1 ∉ I.short ∧ ¬ OnOuterFace I.embedding I.outer q₂.1 ∧
      G.Adj (p.getVert 2) q₁.1 ∧ G.Adj q₂.1 a ∧
      (∀ r ∈ A, ∀ s ∈ A, (G.induce Q).Adj r s →
        (r=q₁ ∧ s=q₂) ∨ (r=q₂ ∧ s=q₁)) ∧
      (∀ z, G.Adj (p.getVert 1) z → z=a ∨ z=p.getVert 2) ∧
      (∃ z ∈ A, q₁ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₁ w ∧ (G.induce Q).Adj w z) ∧
      (∃ z ∈ A, q₂ ≠ z ∧ ∃ w : Q, (G.induce Q).Adj q₂ w ∧ (G.induce Q).Adj w z) := by
  sorry

end

section
variable [Fintype V]
theorem neighbours_on_facial_arc_of_not_separating (M : PlaneMap G) (outer : G.Dart)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (A : Set V) (hAC : A ⊆ {x | x ∈ p.support})
    (hArc : IsFacialCycleAlong M (walk_isCycleMap p hp) A)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp))
    (houtside : ∃ z, OnOuterFace M outer z ∧ z ∉ p.support)
    (hNoSep : ¬ NativeCycleSeparates M p hp)
    (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ p.support := by
  sorry

theorem OriginalBoundaryInstance.three_path_inner_face_corners_allow_boundary (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hch : p.IsChordless)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (hlen : 5 ≤ p.length) (x y : V) (hx1 : x ≠ p.getVert 1)
    (hy : ¬ OnOuterFace I.embedding I.outer y)
    (h2x : G.Adj (p.getVert 2) x) (hxy : G.Adj x y) (hya : G.Adj y a)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) :
    I.embedding.facePerm (walkArcRoot p hp).symm = ⟨(a,y),hya.symm⟩ ∧
      I.embedding.facePerm ⟨(a,y),hya.symm⟩ = ⟨(y,x),hxy.symm⟩ := by
  sorry

theorem OriginalBoundaryInstance.short_cycle_single_corner_neighbours (I : OriginalBoundaryInstance G C)
    (hbad : ¬ I.Extends)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends)
    {a : V} (r : G.Walk a a) (hr : r.IsCycle) (hlen : r.length ≤ 6)
    (d : G.Dart) (hd : d.fst ∉ r.support)
    (hprev : I.embedding.facePerm d = walkArcRoot r hr)
    (hcorner : I.embedding.facePerm (walkArcRoot r hr) =
      toDart cyclicSubgraph_le (cycleForward (walk_isCycleMap r hr) 1)) :
    ∀ z, G.Adj (r.getVert 1) z → z=a ∨ z=r.getVert 2 := by
  sorry

end

end Thomassen
