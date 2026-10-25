/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedLeafCut

/-! All boundary chords for prescriptions of at most four path vertices. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace BoundaryInstance

/-- A branch with at most one edge is either a singleton separator or the
private-leaf case; both are complete reductions with exact original lists. -/
theorem colourable_of_mixed_short_branch_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn)
    {d : V} (q : G.Walk a d) (hq : q.length ≤ 1)
    (hQsub : ∀ x ∈ q.support, x ∈ I.precolor.vertices)
    (hcap : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  cases q with
  | nil =>
    apply I.colourable_of_edge_cut_with_one_sided_prescription S T a b hab ha hb hcover hinter hedges hSc hTc
      ?_ hSsmall hTsmall hsmall
    intro x hx hxP
    exact Or.inl (by simpa only [Walk.support_nil, List.mem_singleton] using hcap x hx hxP)
  | @cons _ t _ hat q =>
    cases q with
    | nil =>
      apply I.colourable_of_mixed_leaf_edge_cut S T a b d hab ha hb haP hbP
        (hQsub d (by simp)) hat ?_ p hp hn hP hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
      intro x hx hxP
      simpa only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hcap x hx hxP
    | cons h q => simp only [Walk.length_cons] at hq; omega

/-- Every mixed cut is closed if either branch at its prescribed separator
end has at most one edge. The other branch may have the full remaining bound. -/
theorem colourable_of_prescription_edge_cut_with_short_branch (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hap : a ∈ p.support)
    (hbranch : (p.takeUntil a hap).length ≤ 1 ∨ (p.dropUntil a hap).length ≤ 1)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have haST : a ∈ S ∩ T := by rw [hinter]; exact Or.inl rfl
  have hverts : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ p.support := by
    simp only [hP, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  let l := (p.takeUntil a hap).reverse
  let r := p.dropUntil a hap
  have hl : l.IsPath := (hp.takeUntil hap).reverse
  have hr : r.IsPath := hp.dropUntil hap
  have heq := p.take_spec hap
  have hsupport : ∀ x, x ∈ I.precolor.vertices ↔ x ∈ l.support ∨ x ∈ r.support := by
    intro x
    rw [hverts, ← heq, Walk.mem_support_append_iff]
    simp only [l, Walk.support_reverse, List.mem_reverse, r]
  have hlength : l.length ≤ 1 ∨ r.length ≤ 1 := by
    simpa only [l, r, Walk.length_reverse] using hbranch
  have hbl : b ∉ l.support := fun h => hbP ((hsupport b).2 (Or.inl h))
  have hbr : b ∉ r.support := fun h => hbP ((hsupport b).2 (Or.inr h))
  have hS : ∀ {d : V} (q : G.Walk a d), q.length ≤ 1 →
      (∀ x ∈ q.support, x ∈ I.precolor.vertices) →
      (∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support) → ListColourable G I.lists := by
    intro d q hq hsub hcap
    exact I.colourable_of_mixed_short_branch_edge_cut S T a b hab ha hb haP hbP p hp hn hP q hq hsub hcap
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  have hT : ∀ {d : V} (q : G.Walk a d), q.length ≤ 1 →
      (∀ x ∈ q.support, x ∈ I.precolor.vertices) →
      (∀ x ∈ T, x ∈ I.precolor.vertices → x ∈ q.support) → ListColourable G I.lists := by
    intro d q hq hsub hcap
    exact I.colourable_of_mixed_short_branch_edge_cut T S a b hab ha hb haP hbP p hp hn hP q hq hsub hcap
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm)
      hTc hSc hTsmall hSsmall hsmall
  have hpoint (U : Set V) (h : ∀ x ∈ U, x ∈ I.precolor.vertices → x = a) :
      ∀ x ∈ U, x ∈ I.precolor.vertices → x ∈ (Walk.nil (G := G) (u := a)).support := by
    intro x hx hxP
    simpa only [Walk.support_nil, List.mem_singleton] using h x hx hxP
  have hnil : ∀ x ∈ (Walk.nil (G := G) (u := a)).support, x ∈ I.precolor.vertices := by
    intro x hx
    have hxa : x = a := by simpa only [Walk.support_nil, List.mem_singleton] using hx
    exact hxa ▸ haP
  have hsplit : ∀ {d e : V} (q : G.Walk a d) (s : G.Walk a e),
      (q.length ≤ 1 ∨ s.length ≤ 1) →
      (∀ x, x ∈ I.precolor.vertices ↔ x ∈ q.support ∨ x ∈ s.support) →
      (∀ x ∈ q.support, x ∈ S) → (∀ x ∈ s.support, x ∈ S ↔ x = a) → ListColourable G I.lists := by
    intro d e q s hlen hPqs hqS hsS
    by_cases hq : q.length ≤ 1
    · apply hS q hq (fun x hx => (hPqs x).2 (Or.inl hx))
      intro x hx hxP
      rcases (hPqs x).1 hxP with hxq | hxs
      · exact hxq
      · exact (hsS x hxs).1 hx ▸ q.start_mem_support
    · apply hT s (hlen.resolve_left hq) (fun x hx => (hPqs x).2 (Or.inr hx))
      intro x hx hxP
      rcases (hPqs x).1 hxP with hxq | hxs
      · have hxST : x ∈ S ∩ T := ⟨hqS x hxq, hx⟩
        rw [hinter] at hxST
        rcases hxST with rfl | hxb
        · exact s.start_mem_support
        · exact (hbP (Set.mem_singleton_iff.1 hxb ▸ hxP)).elim
      · exact hxs
  have hsep : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → (x ∈ S ↔ y ∈ S) :=
    edge_cut_side_constancy S T a b hinter hedges
  rcases path_side_dichotomy_avoiding_other_separator haST.1 hsep l hl hbl with hlS | hlS <;>
    rcases path_side_dichotomy_avoiding_other_separator haST.1 hsep r hr hbr with hrS | hrS
  · apply hT .nil (by simp) hnil (hpoint T ?_)
    intro x hx hxP
    have hxS := ((hsupport x).1 hxP).elim (hlS x) (hrS x)
    have hxST : x ∈ S ∩ T := ⟨hxS, hx⟩
    rw [hinter] at hxST
    exact hxST.elim id (fun h => (hbP (Set.mem_singleton_iff.1 h ▸ hxP)).elim)
  · exact hsplit l r hlength hsupport hlS hrS
  · apply hsplit r l hlength.symm (fun x => (hsupport x).trans or_comm) hrS hlS
  · apply hS .nil (by simp) hnil (hpoint S ?_)
    intro x hx hxP
    exact ((hsupport x).1 hxP).elim (fun h => (hlS x h).1 hx) (fun h => (hrS x h).1 hx)

/-- Every mixed edge cut is closed for a prescribed path with at most three
edges. If its two branches go to different sides, one has at most one edge. -/
theorem colourable_of_short_prescription_edge_cut (I : BoundaryInstance G C)
    (S T : Set V) (a b : V) (hab : G.Adj a b)
    (ha : OnOuterFace I.embedding I.outer a) (hb : OnOuterFace I.embedding I.outer b)
    (haP : a ∈ I.precolor.vertices) (hbP : b ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 3)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {a, b})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Connected) (hTc : (G.induce T).Connected)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hap : a ∈ p.support := by simpa only [hP, BoundaryPrecolor.vertices, List.mem_toFinset] using haP
  have heq := p.take_spec hap
  have hsum : (p.takeUntil a hap).length + (p.dropUntil a hap).length ≤ 3 := by
    rw [← Walk.length_append, heq]
    exact hlen
  exact I.colourable_of_prescription_edge_cut_with_short_branch S T a b hab ha hb haP hbP p hp hn hP hap
    (by omega) hcover hinter hedges hSc hTc hSsmall hTsmall hsmall

/-- A facial chord at a prescribed vertex at distance at most one from a
prescribed-path endpoint is closed, including paths with five or six vertices. -/
theorem colourable_of_short_branch_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hip : c i ∈ p.support)
    (hbranch : (p.takeUntil (c i) hip).length ≤ 1 ∨ (p.dropUntil (c i) hip).length ≤ 1)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
  exact I.colourable_of_prescription_edge_cut_with_short_branch S T (c i) (c j) hadj hi hj hiP hjP p hp hn hP hip
    hbranch hcover hinter hedges hSc hTc hSsmall hTsmall hsmall

/-- The only unresolved branch lengths at a mixed chord are (2,2), (2,3)
and (3,2). These are the central vertices of five/six-vertex prescriptions. -/
lemma remaining_boundary_chord_central_cases (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    (hiP : c i ∈ I.precolor.vertices) (hjP : c j ∉ I.precolor.vertices)
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hip : c i ∈ p.support) :
    ((p.takeUntil (c i) hip).length = 2 ∧ (p.dropUntil (c i) hip).length = 2) ∨
      ((p.takeUntil (c i) hip).length = 2 ∧ (p.dropUntil (c i) hip).length = 3) ∨
      ((p.takeUntil (c i) hip).length = 3 ∧ (p.dropUntil (c i) hip).length = 2) := by
  have hno : ¬ ((p.takeUntil (c i) hip).length ≤ 1 ∨ (p.dropUntil (c i) hip).length ≤ 1) := by
    intro hbranch
    exact hbad (I.colourable_of_short_branch_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj
      hiP hjP p hp hn hP hip hbranch hsmall)
  have hlen : p.length ≤ 5 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hn
    omega
  have hsum : (p.takeUntil (c i) hip).length + (p.dropUntil (c i) hip).length = p.length := by
    rw [← Walk.length_append, p.take_spec hip]
  omega

/-- Construct the actual strict facial chord cut, then close every case for a
prescribed path on at most four vertices, regardless of its endpoint placement. -/
theorem colourable_of_short_prescription_boundary_chord (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j))
    {z w : V} (p : G.Walk z w) (hp : p.IsPath) (hn : p.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path p hp hn) (hlen : p.length ≤ 3)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  by_cases hiP : c i ∈ I.precolor.vertices <;> by_cases hjP : c j ∈ I.precolor.vertices
  · exact I.colourable_of_prescribed_boundary_chord hc hk hface hG i j hadj hforward hbackward hiP hjP hsmall
  · obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
      full_face_chord_separation_at I.embedding hc hk hface hG i j hadj hforward hbackward
    exact I.colourable_of_short_prescription_edge_cut S T (c i) (c j) hadj hi hj hiP hjP p hp hn hP hlen
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  · obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
      full_face_chord_separation_at I.embedding hc hk hface hG j i hadj.symm hbackward hforward
    exact I.colourable_of_short_prescription_edge_cut S T (c j) (c i) hadj.symm hj hi hjP hiP p hp hn hP hlen
      hcover hinter hedges hSc hTc hSsmall hTsmall hsmall
  · exact I.colourable_of_unprescribed_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj hiP hjP hsmall

/-- In a smallest counterexample a boundary chord requires five or six
prescribed path vertices. Empty prescriptions and prescribed cycles are already
closed, and all shorter prescribed paths have now been eliminated as well. -/
lemma boundary_chord_requires_long_prescription (I : BoundaryInstance G C)
    (hG : G.Preconnected) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (hc : IsCycleMap G c) (hk : 3 ≤ k) (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (i j : ZMod k) (hadj : G.Adj (c i) (c j)) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hi : OnOuterFace I.embedding I.outer (c i)) (hj : OnOuterFace I.embedding I.outer (c j)) :
    5 ≤ I.precolor.vertices.card := by
  by_contra hbound
  cases hP : I.precolor with
  | empty =>
    exact hbad (I.colourable_of_unprescribed_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj
      (by simp [hP]) (by simp [hP]) hsmall)
  | path p hp hn =>
    have hlen : p.length ≤ 3 := by
      simp only [hP, BoundaryPrecolor.vertices, List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hbound
      omega
    exact hbad (I.colourable_of_short_prescription_boundary_chord hG hc hk hface i j hadj hforward hbackward hi hj
      p hp hn hP hlen hsmall)
  | cycle p hp hn =>
    exact hbad (I.colourable_of_prescribed_cycle p hp hn (by simp [hP, BoundaryPrecolor.vertices]) hsmall)

end BoundaryInstance
end Thomassen
