/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.FaceRestriction

/-! Faces joined through a deleted connected set project to one actual face. -/

@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch
universe u
namespace Thomassen
open Classical
variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

/-- Two face incidences entering the same deleted component project to the
same face of a connected retained subgraph. -/
lemma onOuterFace_restrict_of_deleted_connection (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    (outer : G.Dart) {d t : G.Dart} {e : H.Dart}
    (htface : SameCycle M.facePerm outer t)
    (hd : d.fst ∈ subVerts H) (ht : t.fst ∈ subVerts H)
    (hdout : d.snd ∉ subVerts H) (htout : t.snd ∉ subVerts H)
    (hpath : RIn G (subVerts H)ᶜ d.snd t.snd) (he : IsNextH M hH d e)
    {x : V} (hx : x ∈ subVerts H) (hface : OnOuterFace M outer x) :
    OnOuterFace (restrictMap M hH) e x := by
  obtain ⟨f, hf⟩ := exists_isNextH M hH (d := t) ht
  have hsame := sameCycle_of_rIn M hH hconn hd ht hdout htout hpath he hf
  obtain ⟨g, hg, hgx⟩ := onOuterFace_restrict_of_connected M hH hconn outer htface hf hx hface
  exact ⟨g, hsame.trans hg, hgx⟩

/-- Deleting a connected set merges every incident old face into one new face.
The selected old face and all remaining neighbours of the deleted set are
retained too. Connectivity is required only for the actual remaining graph. -/
lemma exists_outer_induced_merging_deleted_faces (M : PlaneMap G) (outer : G.Dart)
    (A : Set V) [Nontrivial (Aᶜ : Set V)]
    (hremain : (G.induce Aᶜ).Preconnected) (hA : ConnSet G A)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∉ A) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce Aᶜ).Dart,
      (∀ x : (Aᶜ : Set V), OnOuterFace M outer x.1 →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ x : (Aᶜ : Set V), (∃ y ∈ A, G.Adj x.1 y) →
        OnOuterFace (inducedPlaneMap M Aᶜ) o x) ∧
      (∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∉ A → t.snd ∈ A →
        ∀ x : (Aᶜ : Set V), OnOuterFace M inner x.1 →
          OnOuterFace (inducedPlaneMap M Aᶜ) o x) := by
  have hactive := subVerts_restrict_of_preconnected Aᶜ hremain
  have hconn := restrict_reachable_of_induce_preconnected Aᶜ hremain
  obtain ⟨e, he⟩ := exists_isNextH M (restrict_le G Aᶜ) (d := d)
    (by rw [hactive]; exact hdkeep)
  have hother : ∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∉ A → t.snd ∈ A →
      ∀ x : (Aᶜ : Set V), OnOuterFace M inner x.1 →
        OnOuterFace (inducedPlaneMap M Aᶜ) (induceDartEquiv G Aᶜ e) x := by
    intro inner t htface htkeep htdelete x hx
    apply (inducedPlaneMap_onOuterFace_iff M Aᶜ e x).2
    apply onOuterFace_restrict_of_deleted_connection M (restrict_le G Aᶜ) hconn inner htface
      (by rw [hactive]; exact hdkeep) (by rw [hactive]; exact htkeep)
      (by simpa only [hactive, Set.mem_compl_iff, not_not] using hddelete)
      (by simpa only [hactive, Set.mem_compl_iff, not_not] using htdelete) ?_ he
      (by rw [hactive]; exact x.2) hx
    rw [hactive, compl_compl]
    exact hA.2 _ hddelete _ htdelete
  refine ⟨induceDartEquiv G Aᶜ e, hother outer d hdface hdkeep hddelete, ?_, hother⟩
  rintro x ⟨y, hy, hxy⟩
  let t : G.Dart := ⟨(x.1, y), hxy⟩
  exact hother t t (SameCycle.refl _ _) x.2 hy x (onOuterFace_self M t)

/-- Retaining a connected induced set merges old faces incident with any one
connected omitted set. Other omitted components may remain as well. -/
lemma exists_outer_induced_merging_connected_set (M : PlaneMap G) (outer : G.Dart)
    (S A : Set V) [Nontrivial S] (hremain : (G.induce S).Preconnected)
    (hA : ConnSet G A) (hAS : ∀ x ∈ A, x ∉ S)
    (d : G.Dart) (hdface : SameCycle M.facePerm outer d)
    (hdkeep : d.fst ∈ S) (hddelete : d.snd ∈ A) :
    ∃ o : (G.induce S).Dart,
      (∀ x : S, OnOuterFace M outer x.1 → OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∀ x : S, (∃ y ∈ A, G.Adj x.1 y) → OnOuterFace (inducedPlaneMap M S) o x) ∧
      (∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∈ S → t.snd ∈ A →
        ∀ x : S, OnOuterFace M inner x.1 → OnOuterFace (inducedPlaneMap M S) o x) := by
  have hactive := subVerts_restrict_of_preconnected S hremain
  have hconn := restrict_reachable_of_induce_preconnected S hremain
  obtain ⟨e, he⟩ := exists_isNextH M (restrict_le G S) (d := d)
    (by rw [hactive]; exact hdkeep)
  have hother : ∀ (inner t : G.Dart), SameCycle M.facePerm inner t → t.fst ∈ S → t.snd ∈ A →
      ∀ x : S, OnOuterFace M inner x.1 →
        OnOuterFace (inducedPlaneMap M S) (induceDartEquiv G S e) x := by
    intro inner t htface htkeep htdelete x hx
    apply (inducedPlaneMap_onOuterFace_iff M S e x).2
    apply onOuterFace_restrict_of_deleted_connection M (restrict_le G S) hconn inner htface
      (by rw [hactive]; exact hdkeep) (by rw [hactive]; exact htkeep)
      (by rw [hactive]; exact hAS _ hddelete)
      (by rw [hactive]; exact hAS _ htdelete) ?_ he
      (by rw [hactive]; exact x.2) hx
    exact (hA.2 _ hddelete _ htdelete).mono_set (fun z hz => by rw [hactive]; exact hAS z hz)
  refine ⟨induceDartEquiv G S e, hother outer d hdface hdkeep hddelete, ?_, hother⟩
  rintro x ⟨y, hy, hxy⟩
  let t : G.Dart := ⟨(x.1, y), hxy⟩
  exact hother t t (SameCycle.refl _ _) x.2 hy x (onOuterFace_self M t)

end Thomassen
