/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.InducedEmbedding

/-!
# Restricting an original face to a connected subgraph

An old face can merge with other faces under restriction. Its incidences at
vertices of a connected retained subgraph still project to one face of that
subgraph. The proof follows the old face, using the registered gap theorems for
chords and components outside the retained subgraph.
-/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

omit [Fintype V] in
private lemma face_fst (M : PlaneMap G) (d : G.Dart) :
    (M.facePerm d).fst = d.snd := M.isRotationSystem.fst_apply _

/-- Gaps at incidences of the same original face belong to the same retained
face, provided the retained subgraph is connected on its active vertices. -/
lemma sameCycle_restrict_of_same_original_face (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d t : G.Dart} {e f : H.Dart}
    (hface : SameCycle M.facePerm d t)
    (hd : IsNextH M hH d e) (ht : IsNextH M hH t f) :
    SameCycle (restrictMap M hH).facePerm e f := by
  let π := (restrictMap M hH).facePerm
  let P : G.Dart → Prop := fun z =>
    (z.fst ∈ subVerts H ∧ ∃ a : H.Dart, IsNextH M hH z a ∧ SameCycle π e a) ∨
    (z.fst ∉ subVerts H ∧ ∃ (a : G.Dart) (b : H.Dart),
      a.fst ∈ subVerts H ∧ a.snd ∉ subVerts H ∧ IsNextH M hH a b ∧
      SameCycle π e b ∧ RIn G (subVerts H)ᶜ a.snd z.fst)
  have hstep : ∀ z, P z → P (M.facePerm z) := by
    intro z hz
    rcases hz with ⟨hzH, a, hza, hea⟩ | ⟨hzH, a, b, haH, haout, hab, heb, hp⟩
    · by_cases hnext : z.snd ∈ subVerts H
      · have hnf : (M.facePerm z).fst ∈ subVerts H := (face_fst M z) ▸ hnext
        obtain ⟨b, hb⟩ := exists_isNextH M hH (d := M.facePerm z) hnf
        refine Or.inl ⟨hnf, b, hb, ?_⟩
        by_cases hz : InH H z
        · have heq := eq_of_isNextH_of_inH M hH hz hza
          have hn := isNextH_rot_subRot M hH a.symm
          have hn' : IsNextH M hH (M.facePerm z) (π a) := by
            change IsNextH M hH (M.rot z.symm) ((subRot M hH) a.symm)
            rw [heq]
            exact hn
          have heqb := isNextH_unique M hH hb hn'
          rw [heqb]
          exact hea.trans ⟨1, by simp [π]⟩
        · obtain ⟨b', hb'⟩ := exists_isNextH M hH (d := z.symm) hnext
          have hzsymm : ¬ InH H z.symm := fun h => hz h.symm
          have hn := isNextH_rot_of_not M hH hzsymm hb'
          have heqb : b' = b := isNextH_unique M hH hn hb
          rw [← heqb]
          exact hea.trans (sameCycle_of_chord M hH hconn hzH hnext hz hza hb')
      · refine Or.inr ⟨?_, z, a, hzH, hnext, hza, hea, ?_⟩
        · simpa only [face_fst] using hnext
        · rw [face_fst]
    · by_cases hnext : z.snd ∈ subVerts H
      · obtain ⟨b', hb'⟩ := exists_isNextH M hH (d := z.symm) hnext
        have hzsymm : ¬ InH H z.symm := fun h => hzH ⟨z.snd, h.symm⟩
        have hn := isNextH_rot_of_not M hH hzsymm hb'
        refine Or.inl ⟨(face_fst M z) ▸ hnext, b', hn, ?_⟩
        exact heb.trans (sameCycle_of_rIn M hH hconn haH hnext haout hzH hp hab hb')
      · refine Or.inr ⟨?_, a, b, haH, haout, hab, heb, ?_⟩
        · simpa only [face_fst] using hnext
        · rw [face_fst]
          exact hp.trans (RIn.single z.adj hzH hnext)
  have hdH : d.fst ∈ subVerts H := by
    rw [← isNextH_fst M hH hd]
    exact ⟨e.snd, e.adj⟩
  have hp : ∀ n : ℕ, P ((M.facePerm ^ n) d) := by
    intro n
    induction n with
    | zero => exact Or.inl ⟨hdH, e, hd, SameCycle.refl _ _⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ ih
  obtain ⟨n, hn⟩ := hface.exists_nat_pow_eq
  have hpt : P t := hn ▸ hp n
  rcases hpt with ⟨_, b, hb, heb⟩ | ⟨htout, _⟩
  · exact (isNextH_unique M hH hb ht) ▸ heb
  · exfalso
    apply htout
    rw [← isNextH_fst M hH ht]
    exact ⟨f.snd, f.adj⟩

/-- All retained active vertices on an old face lie on the projected new face. -/
lemma onOuterFace_restrict_of_connected (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer : G.Dart) {d : G.Dart} {e : H.Dart}
    (hd : SameCycle M.facePerm outer d) (he : IsNextH M hH d e)
    {x : V} (hx : x ∈ subVerts H) (hxf : OnOuterFace M outer x) :
    OnOuterFace (restrictMap M hH) e x := by
  obtain ⟨t, ht, htx⟩ := hxf
  obtain ⟨f, hf⟩ := exists_isNextH M hH (d := t) (htx ▸ hx)
  exact ⟨f, sameCycle_restrict_of_same_original_face M hH hconn (hd.symm.trans ht) he hf,
    (isNextH_fst M hH hf).trans htx⟩

omit [Fintype V] in
/-- In a nontrivial connected induced graph, all retained vertices are active. -/
lemma subVerts_restrict_of_preconnected (S : Set V) [Nontrivial S]
    (hconn : (G.induce S).Preconnected) : subVerts (restrict G S) = S := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, hxy⟩
    exact hxy.2.1
  · intro hx
    obtain ⟨y, hxy⟩ := SimpleGraph.exists_adj_iff_not_isIsolated.2
      (hconn.not_isIsolated ⟨x, hx⟩)
    exact ⟨y.1, hxy, hx, y.2⟩

omit [Fintype V] in
/-- A connected induced graph is connected also in the ambient restriction API. -/
lemma restrict_reachable_of_induce_preconnected (S : Set V)
    (hconn : (G.induce S).Preconnected) :
    ∀ a ∈ subVerts (restrict G S), ∀ b ∈ subVerts (restrict G S),
      (restrict G S).Reachable a b := by
  intro a ha b hb
  obtain ⟨_, ha⟩ := ha
  obtain ⟨_, hb⟩ := hb
  let φ : G.induce S →g restrict G S :=
    ⟨Subtype.val, fun {x y} hxy => ⟨hxy, x.2, y.2⟩⟩
  exact (hconn ⟨a, ha.2.1⟩ ⟨b, hb.2.1⟩).map φ

/-- A chosen original face projects to some face of any nontrivial connected
induced subgraph. Only an implication is asserted: restriction may merge faces. -/
lemma exists_outer_induced_of_preconnected (M : PlaneMap G) (outer : G.Dart)
    (S : Set V) [Nontrivial S] (hconn : (G.induce S).Preconnected) :
    ∃ o : (G.induce S).Dart, ∀ x : S, OnOuterFace M outer x.1 →
      OnOuterFace (inducedPlaneMap M S) o x := by
  classical
  have hactive := subVerts_restrict_of_preconnected S hconn
  have hc := restrict_reachable_of_induce_preconnected S hconn
  by_cases hmeet : ∃ x ∈ S, OnOuterFace M outer x
  · obtain ⟨x, hx, d, hd, hdx⟩ := hmeet
    have hdH : d.fst ∈ subVerts (restrict G S) := by rw [hactive, hdx]; exact hx
    obtain ⟨e, he⟩ := exists_isNextH M (restrict_le G S) (d := d) hdH
    refine ⟨induceDartEquiv G S e, fun y hy => ?_⟩
    apply (inducedPlaneMap_onOuterFace_iff M S e y).2
    exact onOuterFace_restrict_of_connected M (restrict_le G S) hc outer hd he
      (by rw [hactive]; exact y.2) hy
  · obtain ⟨a⟩ := (inferInstance : Nonempty S)
    obtain ⟨b, hab⟩ := hconn.exists_adj_of_nontrivial a
    exact ⟨⟨(a, b), hab⟩, fun y hy => False.elim (hmeet ⟨y.1, y.2, hy⟩)⟩

/-- Deleting a connected set through an edge of the old face exposes every
remaining neighbour of that set on the same new face. The remaining induced
graph must be connected; original face incidences are retained as well. -/
lemma exists_outer_induced_after_connected_deletion (M : PlaneMap G) (outer : G.Dart)
    (A : Set V) [Nontrivial (Aᶜ : Set V)]
    (hremain : (G.induce Aᶜ).Preconnected) (hA : ConnSet G A)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∉ A) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce Aᶜ).Dart,
      (∀ x : (Aᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ x : (Aᶜ : Set V), (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) := by
  classical
  have hactive := subVerts_restrict_of_preconnected Aᶜ hremain
  have hconn := restrict_reachable_of_induce_preconnected Aᶜ hremain
  obtain ⟨e, he⟩ := exists_isNextH M (restrict_le G Aᶜ) (d := d)
    (by rw [hactive]; exact hdkeep)
  refine ⟨induceDartEquiv G Aᶜ e, ?_, ?_⟩
  · intro x hx
    apply (inducedPlaneMap_onOuterFace_iff M Aᶜ e x).2
    exact onOuterFace_restrict_of_connected M (restrict_le G Aᶜ) hconn outer hdface he
      (by rw [hactive]; exact x.2) hx
  · rintro x ⟨y, hy, hxy⟩
    let t : G.Dart := ⟨(x.1, y), hxy⟩
    have ht : t.fst ∈ subVerts (restrict G Aᶜ) := by rw [hactive]; exact x.2
    obtain ⟨f, hf⟩ := exists_isNextH M (restrict_le G Aᶜ) (d := t) ht
    have hr : RIn G (subVerts (restrict G Aᶜ))ᶜ d.snd t.snd := by
      rw [hactive, compl_compl]
      exact hA.2 _ hddelete _ hy
    have hfaces := sameCycle_of_rIn M (restrict_le G Aᶜ) hconn
      (by rw [hactive]; exact hdkeep) ht
      (by simpa only [hactive, Set.mem_compl_iff, not_not] using hddelete)
      (by simpa only [hactive, Set.mem_compl_iff, not_not] using hy) hr he hf
    apply (inducedPlaneMap_onOuterFace_iff M Aᶜ e x).2
    exact ⟨f, hfaces, isNextH_fst M (restrict_le G Aᶜ) hf⟩

end Thomassen
