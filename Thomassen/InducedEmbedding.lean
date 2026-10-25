/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.Instance

/-!
# Passing from an ambient restriction to the smaller induced vertex type

The existing restriction operation keeps the ambient vertex type, with isolated
vertices outside the chosen set. Induction on the number of vertices instead
uses the subtype. These constructions transport the actual rotation and face
orbits; merely knowing that some planar embedding exists would not suffice.
-/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- Restricting the edge relation and inducing on the subtype have the same darts. -/
def induceDartEquiv (G : SimpleGraph V) (S : Set V) :
    (restrict G S).Dart ≃ (G.induce S).Dart where
  toFun d := ⟨(⟨d.fst, d.adj.2.1⟩, ⟨d.snd, d.adj.2.2⟩), d.adj.1⟩
  invFun d := ⟨(d.fst.1, d.snd.1), d.adj, d.fst.2, d.snd.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

@[simp] lemma induceDartEquiv_fst (S : Set V) (d : (restrict G S).Dart) :
    ((induceDartEquiv G S d).fst : V) = d.fst := rfl

@[simp] lemma induceDartEquiv_snd (S : Set V) (d : (restrict G S).Dart) :
    ((induceDartEquiv G S d).snd : V) = d.snd := rfl

@[simp] lemma induceDartEquiv_symm (S : Set V) (d : (restrict G S).Dart) :
    induceDartEquiv G S d.symm = (induceDartEquiv G S d).symm := rfl

lemma induceDartEquiv_dartSymm (G : SimpleGraph V) (S : Set V) :
    (induceDartEquiv G S).permCongr (dartSymm (restrict G S)) = dartSymm (G.induce S) := by
  apply Equiv.ext
  intro d
  change induceDartEquiv G S (((induceDartEquiv G S).symm d).symm) = d.symm
  rw [induceDartEquiv_symm, Equiv.apply_symm_apply]

/-- The given map on the ambient restriction, transported to its true vertex subtype. -/
noncomputable def subtypePlaneMap (S : Set V) (M : PlaneMap (restrict G S)) :
    PlaneMap (G.induce S) where
  rot := (induceDartEquiv G S).permCongr M.rot
  isRotationSystem := {
    fst_apply := by
      intro d
      apply Subtype.ext
      change (M.rot ((induceDartEquiv G S).symm d)).fst = d.fst.1
      rw [M.isRotationSystem.fst_apply]
      rfl
    sameCycle := by
      intro d e hde
      have hf : ((induceDartEquiv G S).symm d).fst =
          ((induceDartEquiv G S).symm e).fst := congrArg Subtype.val hde
      have h := (sameCycle_permCongr_iff (induceDartEquiv G S) M.rot _ _).1
        (M.isRotationSystem.sameCycle _ _ hf)
      simpa using h }
  eulerDefect_eq_zero := by
    rw [← induceDartEquiv_dartSymm G S, eulerDefect_permCongr]
    exact M.eulerDefect_eq_zero

lemma subtypePlaneMap_facePerm (S : Set V) (M : PlaneMap (restrict G S)) :
    (subtypePlaneMap S M).facePerm = (induceDartEquiv G S).permCongr M.facePerm := by
  change (induceDartEquiv G S).permCongr M.rot * dartSymm (G.induce S) = _
  rw [← induceDartEquiv_dartSymm G S, ← Equiv.permCongr_mul]
  rfl

/-- Exact preservation of face incidence, not just existence of a planar embedding. -/
lemma subtypePlaneMap_sameCycle_iff (S : Set V) (M : PlaneMap (restrict G S))
    (d e : (restrict G S).Dart) :
    SameCycle (subtypePlaneMap S M).facePerm (induceDartEquiv G S d)
      (induceDartEquiv G S e) ↔ SameCycle M.facePerm d e := by
  rw [subtypePlaneMap_facePerm]
  exact (sameCycle_permCongr_iff (induceDartEquiv G S) M.facePerm d e).symm

lemma subtypePlaneMap_onOuterFace_iff (S : Set V) (M : PlaneMap (restrict G S))
    (outer : (restrict G S).Dart) (x : S) :
    OnOuterFace (subtypePlaneMap S M) (induceDartEquiv G S outer) x ↔
      OnOuterFace M outer x.1 := by
  constructor
  · rintro ⟨e, he, hfst⟩
    refine ⟨(induceDartEquiv G S).symm e, ?_, congrArg Subtype.val hfst⟩
    apply (subtypePlaneMap_sameCycle_iff S M outer _).1
    simpa using he
  · rintro ⟨e, he, hfst⟩
    refine ⟨induceDartEquiv G S e, (subtypePlaneMap_sameCycle_iff S M outer e).2 he, ?_⟩
    exact Subtype.ext hfst

variable [Fintype V]

omit [Fintype V] in
lemma five_le_egirth_induce (S : Set V) (hg : 5 ≤ G.egirth) :
    5 ≤ (G.induce S).egirth := by
  exact hg.trans (SimpleGraph.IsContained.egirth_le
    ⟨(SimpleGraph.Embedding.induce (G := G) S).toCopy⟩)

/-- Restrict the existing rotation, then remove isolated ambient vertices. -/
noncomputable def inducedPlaneMap (M : PlaneMap G) (S : Set V) : PlaneMap (G.induce S) :=
  subtypePlaneMap S (restrictMap M (restrict_le G S))

lemma inducedPlaneMap_onOuterFace_iff (M : PlaneMap G) (S : Set V)
    (outer : (restrict G S).Dart) (x : S) :
    OnOuterFace (inducedPlaneMap M S) (induceDartEquiv G S outer) x ↔
      OnOuterFace (restrictMap M (restrict_le G S)) outer x.1 :=
  subtypePlaneMap_onOuterFace_iff S _ outer x

/-- A proper induced vertex set is strictly smaller for the induction measure. -/
lemma card_induced_vertices_lt (S : Set V) {x : V} (hx : x ∉ S) :
    Nat.card S < Nat.card V := by
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hx

/-- Restriction to a union of whole components preserves each kept rotation step. -/
lemma restrictMap_rot_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (d : (restrict G S).Dart) :
    toDart (restrict_le G S) ((restrictMap M (restrict_le G S)).rot d) =
      M.rot (toDart (restrict_le G S) d) := by
  have hfst : (M.rot (toDart (restrict_le G S) d)).fst ∈ S := by
    rw [M.isRotationSystem.fst_apply]
    exact d.adj.2.1
  have hin : InH (restrict G S) (M.rot (toDart (restrict_le G S) d)) :=
    ⟨(M.rot (toDart (restrict_le G S) d)).adj, hfst,
      hclosed _ hfst _ (M.rot (toDart (restrict_le G S) d)).adj⟩
  exact (eq_of_isNextH_of_inH M (restrict_le G S) hin
    (isNextH_rot_subRot M (restrict_le G S) d)).symm

lemma restrictMap_facePerm_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (d : (restrict G S).Dart) :
    toDart (restrict_le G S) ((restrictMap M (restrict_le G S)).facePerm d) =
      M.facePerm (toDart (restrict_le G S) d) :=
  restrictMap_rot_of_closed M S hclosed d.symm

/-- Injective commuting maps identify exactly the same finite permutation orbits. -/
lemma sameCycle_iff_of_injective_commuting {D E : Type u} [Finite D] [Finite E]
    (f : D → E) (hf : Function.Injective f) (p : Equiv.Perm D) (q : Equiv.Perm E)
    (hstep : ∀ d, f (p d) = q (f d)) (d e : D) :
    SameCycle p d e ↔ SameCycle q (f d) (f e) := by
  have hpow : ∀ n : ℕ, ∀ d, f ((p ^ n) d) = (q ^ n) (f d) := by
    intro n
    induction n with
    | zero => intro d; rfl
    | succ n ih =>
      intro d
      rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih, pow_succ', Equiv.Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, ← hpow, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hf ((hpow n d).trans hn)⟩

lemma restrictMap_sameCycle_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (d e : (restrict G S).Dart) :
    SameCycle (restrictMap M (restrict_le G S)).facePerm d e ↔
      SameCycle M.facePerm (toDart (restrict_le G S) d) (toDart (restrict_le G S) e) :=
  sameCycle_iff_of_injective_commuting (toDart (restrict_le G S))
    (toDart_injective _) _ _ (restrictMap_facePerm_of_closed M S hclosed) d e

lemma restrictMap_onOuterFace_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (outer : (restrict G S).Dart)
    (x : S) :
    OnOuterFace (restrictMap M (restrict_le G S)) outer x.1 ↔
      OnOuterFace M (toDart (restrict_le G S) outer) x.1 := by
  constructor
  · rintro ⟨e, he, hx⟩
    exact ⟨toDart (restrict_le G S) e,
      (restrictMap_sameCycle_of_closed M S hclosed outer e).1 he, hx⟩
  · rintro ⟨e, he, hx⟩
    have heS : e.fst ∈ S := hx ▸ x.2
    let e' : (restrict G S).Dart :=
      ⟨e.toProd, e.adj, heS, hclosed _ heS _ e.adj⟩
    exact ⟨e', (restrictMap_sameCycle_of_closed M S hclosed outer e').2 he, hx⟩

/-- A whole-component restriction retains exactly the original selected face. -/
lemma inducedPlaneMap_onOuterFace_of_closed (M : PlaneMap G) (S : Set V)
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (outer : (restrict G S).Dart)
    (x : S) :
    OnOuterFace (inducedPlaneMap M S) (induceDartEquiv G S outer) x ↔
      OnOuterFace M (toDart (restrict_le G S) outer) x.1 := by
  rw [inducedPlaneMap_onOuterFace_iff]
  exact restrictMap_onOuterFace_of_closed M S hclosed outer x

omit [Fintype V] in
/-- An induced colouring is precisely the old partial-colouring interface.
An explicit fallback avoids an unnecessary nonempty-colour-type assumption. -/
lemma col_restrict_iff_listColourable_induce {C : Type v} (S : Finset V)
    (L : V → Finset C) (fallback : V → C) :
    Col (restrict G (↑S : Set V)) S L (fun _ _ x y => x = y) ↔
      ListColourable (G.induce (↑S : Set V)) (fun x => L x.1) := by
  rw [col_restrict_iff]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨SimpleGraph.Coloring.mk (fun x => c x.1)
      (fun {x y} hxy => hp x.1 x.2 y.1 y.2 hxy), fun x => hc x.1 x.2⟩
  · rintro ⟨c, hc⟩
    let f : V → C := fun x => if hx : x ∈ S then c ⟨x, hx⟩ else fallback x
    refine ⟨f, ?_, ?_⟩
    · intro x hx
      simpa [f, hx] using hc ⟨x, hx⟩
    · intro x hx y hy hxy
      have h := c.valid (show (G.induce (↑S : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
      simpa [f, hx, hy] using h

end Thomassen
