/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.OriginalShortLeafCut
public import Thomassen.InteriorFacePathCut

/-! Actual two/three-path cuts for original Theorem 2.1 reductions (4) and (5). -/
@[expose] public section
open Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Both sides of the native interior path cut have actual faces containing
all retained old boundary incidences and the whole separator. The inner-side
claim follows from the exact intersection and arc capture; arbitrary face
preservation under deletion is not assumed. -/
theorem interior_path_cut_both_faces (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong M (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle M.facePerm outer (walkArcRoot p hp)) (n : ℕ)
    (q : G.Walk (p.getVert n) a) (hq : q.IsPath)
    (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length) (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace M outer (q.getVert i)) :
    ∃ S T : Set V, Nat.card S < Nat.card V ∧ Nat.card T < Nat.card V ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x | x ∈ q.support} ∧
      (∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)) ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (∃ N : PlaneMap (G.induce S), ∃ o : (G.induce S).Dart, ∀ x : S,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) ∧
      (∃ N : PlaneMap (G.induce T), ∃ o : (G.induce T).Dart, ∀ x : T,
        OnOuterFace M outer x.1 ∨ x.1 ∈ q.support → OnOuterFace N o x) := by
  obtain ⟨S,T,hSsmall,hTsmall,hcover,hinter,hedges,hSc,hTc,_,hkeep,⟨oS,hSface⟩,hTface⟩ :=
    interior_face_path_cut M outer hg hG p hp hface hroot n q hq hn hnp hqpos hqshort hInner
  refine ⟨S,T,hSsmall,hTsmall,hcover,hinter,hedges,hSc,hTc,?_,hTface⟩
  refine ⟨inducedPlaneMap M S,oS,?_⟩
  intro x hx
  apply (hSface x).2
  rcases hx with hx | hx
  · by_cases hxArc : x.1 ∈ cycleInterval (walkCycleVertices p) 1 (n-2)
    · left
      obtain ⟨i,hi,hix⟩ := hxArc
      have hix' : p.getVert (1+i) = x.1 := by
        rwa [walkCycleVertices_nat_le p (by omega : 1+i ≤ p.length)] at hix
      have hmem := (p.take n).getVert_mem_support (1+i)
      rw [Walk.take_getVert,Nat.min_eq_right (by omega : 1+i ≤ n),hix'] at hmem
      exact hmem
    · right
      have hxT := hkeep x.1 hx hxArc
      have h : x.1 ∈ S ∩ T := ⟨x.2,hxT⟩
      rwa [hinter] at h
  · exact Or.inr hx

namespace OriginalBoundaryInstance

/-- Either orientation of a strict short-leaf/central-edge cut is valid.
Both augmented exterior faces are supplied by the actual native cut geometry. -/
theorem extends_of_short_leaf_edge_separation (I : OriginalBoundaryInstance G C)
    (S T R : Set V) (v w : V) (hvw : G.Adj v w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = R ∪ {v,w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hSc : (G.induce S).Preconnected) (hTc : (G.induce T).Preconnected)
    (hR : R ⊆ I.short) (hRaway : ∀ x ∈ R, x ≠ v ∧ x ≠ w)
    (hattach : ∀ x ∈ R, ∃ y, (y = v ∨ y = w) ∧ G.Adj x y)
    (NS : PlaneMap (G.induce S)) (oS : (G.induce S).Dart)
    (hSface : ∀ x : S, OnOuterFace I.embedding I.outer x.1 ∨ x.1 ∈ R ∪ {v,w} → OnOuterFace NS oS x)
    (NT : PlaneMap (G.induce T)) (oT : (G.induce T).Dart)
    (hTface : ∀ x : T, OnOuterFace I.embedding I.outer x.1 ∨ x.1 ∈ R ∪ {v,w} → OnOuterFace NT oT x)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  rcases hedges I.edge with h | h
  · exact I.extends_of_short_leaf_edge_cut S T R v w hvw hcover hinter hedges hSc h.1 h.2
      hR hRaway hattach NT oT (fun x hx => hTface x (Or.inl (I.on_outer x.1 hx)))
      (fun hvT => hTface ⟨v,hvT⟩ (Or.inr (Or.inr (Or.inl rfl))))
      (fun hwT => hTface ⟨w,hwT⟩ (Or.inr (Or.inr (Or.inr rfl)))) hSsmall hTsmall hsmall
  · exact I.extends_of_short_leaf_edge_cut T S R v w hvw
      (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) (fun {_ _} h => (hedges h).symm)
      hTc h.1 h.2 hR hRaway hattach NS oS (fun x hx => hSface x (Or.inl (I.on_outer x.1 hx)))
      (fun hvS => hSface ⟨v,hvS⟩ (Or.inr (Or.inr (Or.inl rfl))))
      (fun hwS => hSface ⟨w,hwS⟩ (Or.inr (Or.inr (Or.inr rfl)))) hTsmall hSsmall hsmall

/-- Original step (4): a two-edge interior path with a short endpoint is a
complete strict-induction reduction. No cut, face-corner or list-restoration
certificate is assumed by the caller. -/
theorem extends_of_interior_two_path (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haA : a ∈ I.short) (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (z : V) (hz : ¬ OnOuterFace I.embedding I.outer z)
    (hza : G.Adj z a) (hzn : G.Adj z (p.getVert n))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  have hna : p.getVert n ≠ a := by
    intro h
    have hi := hp.getVert_injOn' (show n ≤ p.length-1 from by omega)
      (show 0 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using h)
    omega
  let q : G.Walk (p.getVert n) a := .cons hzn.symm (.cons hza .nil)
  have hq : q.IsPath := by simp [q,Walk.isPath_def,hna,hzn.ne,hza.ne,Ne.symm]
  have hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert i) := by
    intro i hi hil
    have hi1 : i=1 := by change i < 2 at hil; omega
    subst i
    exact hz
  obtain ⟨S,T,hSsmall,hTsmall,hcover,hinter,hedges,hSc,hTc,⟨NS,oS,hSface⟩,⟨NT,oT,hTface⟩⟩ :=
    interior_path_cut_both_faces I.embedding I.outer I.girth hG p hp hface hroot n q hq hn hnp
      (by change 0 < 2; omega) (by change 2 ≤ 3; omega) hInner
  have hsep : {x | x ∈ q.support} = ({a} : Set V) ∪ {z,p.getVert n} := by
    ext x
    simp only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,
      Set.mem_ofPred_eq,Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  rw [hsep] at hinter
  apply I.extends_of_short_leaf_edge_separation S T {a} z (p.getVert n) hzn hcover hinter hedges
    hSc.preconnected hTc.preconnected ?_ ?_ ?_ NS oS ?_ NT oT ?_ hSsmall hTsmall hsmall
  · intro x hx
    exact Set.mem_singleton_iff.1 hx ▸ haA
  · intro x hx
    have hx' : x=a := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨hza.ne.symm,hna.symm⟩
  · intro x hx
    have hx' : x=a := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨z,Or.inl rfl,hza.symm⟩
  · intro x hx
    exact hSface x (hx.imp_right (fun h => by
      change x.1 ∈ {y | y ∈ q.support}
      rw [hsep]
      exact h))
  · intro x hx
    exact hTface x (hx.imp_right (fun h => by
      change x.1 ∈ {y | y ∈ q.support}
      rw [hsep]
      exact h))

/-- Original step (5): an interior three-edge path between two old short
vertices is a complete strict-induction reduction. Its central edge is fixed;
the two endpoint two-lists are temporarily replaced and forced back exactly. -/
theorem extends_of_interior_three_path (I : OriginalBoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haA : a ∈ I.short) (n : ℕ) (hn : 2 ≤ n) (hnp : n + 2 ≤ p.length)
    (hnA : p.getVert n ∈ I.short) (z w : V)
    (hz : ¬ OnOuterFace I.embedding I.outer z) (hw : ¬ OnOuterFace I.embedding I.outer w)
    (hnz : G.Adj (p.getVert n) z) (hzw : G.Adj z w) (hwa : G.Adj w a)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : OriginalBoundaryInstance H C),
      Nat.card W < Nat.card V → J.Extends) : I.Extends := by
  have hna : p.getVert n ≠ a := by
    intro h
    have hi := hp.getVert_injOn' (show n ≤ p.length-1 from by omega)
      (show 0 ≤ p.length-1 from by omega) (by simpa only [Walk.getVert_zero] using h)
    omega
  have hza : z ≠ a := fun h => hz (h.symm ▸ I.on_outer a haA)
  have hwn : w ≠ p.getVert n := fun h => hw (h.symm ▸ I.on_outer _ hnA)
  let q : G.Walk (p.getVert n) a := .cons hnz (.cons hzw (.cons hwa .nil))
  have hq : q.IsPath := by simp [q,Walk.isPath_def,hna,hza,hwn,hnz.ne,hzw.ne,hwa.ne,Ne.symm]
  have hInner : ∀ i, 0 < i → i < q.length → ¬ OnOuterFace I.embedding I.outer (q.getVert i) := by
    intro i hi hil
    have hi12 : i=1 ∨ i=2 := by change i < 3 at hil; omega
    rcases hi12 with rfl | rfl
    · exact hz
    · exact hw
  obtain ⟨S,T,hSsmall,hTsmall,hcover,hinter,hedges,hSc,hTc,⟨NS,oS,hSface⟩,⟨NT,oT,hTface⟩⟩ :=
    interior_path_cut_both_faces I.embedding I.outer I.girth hG p hp hface hroot n q hq hn hnp
      (by change 0 < 3; omega) (by change 3 ≤ 3; omega) hInner
  have hsep : {x | x ∈ q.support} = ({a,p.getVert n} : Set V) ∪ {z,w} := by
    ext x
    simp only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,
      Set.mem_ofPred_eq,Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  rw [hsep] at hinter
  apply I.extends_of_short_leaf_edge_separation S T {a,p.getVert n} z w hzw hcover hinter hedges
    hSc.preconnected hTc.preconnected ?_ ?_ ?_ NS oS ?_ NT oT ?_ hSsmall hTsmall hsmall
  · intro x hx
    rcases hx with rfl | hx
    · exact haA
    · exact Set.mem_singleton_iff.1 hx ▸ hnA
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨hza.symm,hwa.ne.symm⟩
    · have hx' : x=p.getVert n := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨hnz.ne,hwn.symm⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨w,Or.inr rfl,hwa.symm⟩
    · have hx' : x=p.getVert n := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨z,Or.inl rfl,hnz⟩
  · intro x hx
    exact hSface x (hx.imp_right (fun h => by
      change x.1 ∈ {y | y ∈ q.support}
      rw [hsep]
      exact h))
  · intro x hx
    exact hTface x (hx.imp_right (fun h => by
      change x.1 ∈ {y | y ∈ q.support}
      rw [hsep]
      exact h))

end OriginalBoundaryInstance
end Thomassen
