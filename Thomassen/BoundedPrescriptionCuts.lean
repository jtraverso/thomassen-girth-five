/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.BoundedPrescriptionBase

/-! Actual cuts of connected boundary prescriptions. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]
namespace ConnectedPrescription

/-- A nonempty clique separator contained in the prescribed set splits the
auxiliary problem into strictly smaller actual instances with unchanged lists.
The restrictions remain connected by the proved clique retraction. -/
theorem colourable_of_clique_cut (I : ConnectedPrescription G C)
    (S T : Set V) [Nontrivial S] [Nontrivial T]
    (hcover : S ∪ T = Set.univ)
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hclique : ∀ x ∈ S ∩ T, ∀ y ∈ S ∩ T, x ≠ y → G.Adj x y)
    (hsepP : S ∩ T ⊆ I.vertices) (hne : (S ∩ T).Nonempty)
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hScard : Nat.card S < Nat.card V) (hTcard : Nat.card T < Nat.card V)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  obtain ⟨a, ha⟩ := hne
  have hPS := connSet_inter_of_clique_separator I.vertices S T I.connected hcover hedges hclique hsepP ha
  have hPT := connSet_inter_of_clique_separator I.vertices T S I.connected
    (by rwa [Set.union_comm]) (fun {_ _} h => (hedges h).symm)
    (fun x hx y hy hxy => hclique x ⟨hx.2,hx.1⟩ y ⟨hy.2,hy.1⟩ hxy)
    (fun _ hx => hsepP ⟨hx.2,hx.1⟩) (show a ∈ T ∩ S from ⟨ha.2,ha.1⟩)
  let JS := I.induce S hS hPS
  let JT := I.induce T hT hPT
  obtain ⟨cS, hcS⟩ := hrec S (G.induce S) JS hS hScard
  obtain ⟨cT, hcT⟩ := hrec T (G.induce T) JT hT hTcard
  change ∀ x : S, cS x ∈ I.lists x.1 at hcS
  change ∀ x : T, cT x ∈ I.lists x.1 at hcT
  refine glue_induced_colourings S T I.lists (fun x => ?_) hedges cS cT hcS hcT ?_
  · have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hxS hxT
    have hx := hsepP ⟨hxS,hxT⟩
    have hs : cS ⟨x,hxS⟩ = I.prescribed x := Finset.mem_singleton.1
      (by simpa only [I.singleton x hx] using hcS ⟨x,hxS⟩)
    have ht : cT ⟨x,hxT⟩ = I.prescribed x := Finset.mem_singleton.1
      (by simpa only [I.singleton x hx] using hcT ⟨x,hxT⟩)
    exact hs.trans ht.symm

/-- A piece avoiding all prescribed vertices is an ordinary empty instance.
The selected face is obtained from the actual induced embedding. -/
noncomputable def induceEmpty (I : ConnectedPrescription G C) (T : Set V) [Nontrivial T]
    (hT : (G.induce T).Preconnected) (hdis : ∀ x ∈ T, x ∉ I.vertices) :
    BoundaryInstance (G.induce T) C := by
  let hex := exists_outer_induced_of_preconnected I.embedding I.outer T hT
  exact {
    girth := five_le_egirth_induce T I.girth
    embedding := inducedPlaneMap I.embedding T
    outer := hex.choose
    precolor := .empty
    lists := fun x => I.lists x.1
    prescribed := fun x => I.prescribed x.1
    on_outer := by simp
    singleton := by simp
    proper_precolor := by simp
    boundary_lists := fun x _ _ => I.outside_list_ge_two (hdis x.1 x.2)
    interior_lists := fun x hx => I.interior_lists x.1 (fun h => hx (hex.choose_spec x h))
    short_edges := fun {x _} hxy hx hy => (hdis x.1 x.2 (I.short_edges hxy hx hy).1).elim }

/-- At an unprescribed attachment, first colour the side containing the entire
prescription. Then the existing proved root-fan induction fixes that colour in
the other strictly smaller piece, including every old short neighbour. -/
theorem colourable_of_unprescribed_cut (I : ConnectedPrescription G C)
    (S T : Set V) [Nontrivial S] [Nontrivial T] (w : V) (hwS : w ∈ S) (hwT : w ∈ T)
    (hwP : w ∉ I.vertices) (hPS : I.vertices ⊆ S)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {w})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card)
    (hScard : Nat.card S < Nat.card V) (hTcard : Nat.card T < Nat.card V)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  have hPSconn : ConnSet G (I.vertices ∩ S) := by
    have heq : I.vertices ∩ S = I.vertices := Set.inter_eq_left.2 hPS
    rw [heq]
    exact I.connected
  let JS := I.induce S hS hPSconn
  obtain ⟨cS,hcS⟩ := hrec S (G.induce S) JS hS hScard
  have hdis : ∀ x ∈ T, x ∉ I.vertices := by
    intro x hxT hxP
    have hxw : x = w := by
      have h : x ∈ S ∩ T := ⟨hPS hxP,hxT⟩
      rwa [hinter] at h
    exact hwP (hxw ▸ hxP)
  have hJT : ∃ J : BoundaryInstance (G.induce T) C,
      J.precolor = .empty ∧ (∀ x : T, J.lists x = I.lists x.1) ∧
      OnOuterFace J.embedding J.outer (⟨w,hwT⟩ : T) := by
    rcases hboundary with hwface | hthree
    · let J := I.induceEmpty T hT hdis
      exact ⟨J,rfl,fun _ => rfl,
        (exists_outer_induced_of_preconnected I.embedding I.outer T hT).choose_spec _ hwface⟩
    · obtain ⟨z,hwz⟩ := hT.exists_adj_of_nontrivial (⟨w,hwT⟩ : T)
      let o : (G.induce T).Dart := ⟨(⟨w,hwT⟩,z),hwz⟩
      let J := BoundaryInstance.of_three_lists (inducedPlaneMap I.embedding T) o
        (five_le_egirth_induce T I.girth) (fun x => I.lists x.1) hthree (fun x => I.prescribed x.1)
      exact ⟨J,rfl,fun _ => rfl,onOuterFace_self _ o⟩
  obtain ⟨JT,hPT,hLT,hwface⟩ := hJT
  have hwcol : cS ⟨w,hwS⟩ ∈ JT.lists ⟨w,hwT⟩ := by rw [hLT]; exact hcS _
  obtain ⟨f,hfw,hf,hproper⟩ := JT.exists_rootStar_colours hPT ⟨w,hwT⟩ (cS ⟨w,hwS⟩) hwcol
  obtain ⟨cT,hcT,hagree⟩ := JT.rootStar_extension_of_smaller N hsmall hPT hT ⟨w,hwT⟩
    hwface f hf hproper (by omega)
  refine glue_induced_colourings S T I.lists (fun x => ?_) hedges cS cT hcS
    (fun x => by rw [← hLT]; exact hcT x) ?_
  · have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hxS hxT
    have hxw : x = w := by
      have h : x ∈ S ∩ T := ⟨hxS,hxT⟩
      rwa [hinter] at h
    subst x
    exact ((hagree _ (Or.inl rfl)).trans hfw).symm

/-- Every cutvertex is eliminated in the auxiliary connected-prescription
induction. If it is outside the prescription, connectedness puts the complete
prescription on one side; if it is interior, face connectivity proves that the
other side has three-lists everywhere. -/
theorem colourable_of_cutvertex (I : ConnectedPrescription G C) (hG : G.Preconnected)
    (w : V) (hdisc : ¬ (G.induce ({w} : Set V)ᶜ).Preconnected)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hrec : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : ConnectedPrescription H C),
      H.Preconnected → Nat.card W < Nat.card V → ListColourable H J.lists) :
    ListColourable G I.lists := by
  obtain ⟨r,hr⟩ := I.connected.1
  obtain ⟨S,hwS,hrS,⟨a,ha,haw⟩,⟨b,hb⟩,hsep⟩ := exists_cut_side_containing w r hdisc
  let T : Set V := insert w Sᶜ
  have hwT : w ∈ T := Or.inl rfl
  have hbT : b ∈ T := Or.inr hb
  have hbw : b ≠ w := fun h => hb (h ▸ hwS)
  have haT : a ∉ T := by
    simpa only [T, Set.mem_insert_iff, Set.mem_compl_iff, haw, false_or, not_not] using ha
  let : Nontrivial S := ⟨⟨⟨a,ha⟩,⟨w,hwS⟩,fun h => haw (congrArg Subtype.val h)⟩⟩
  let : Nontrivial T := ⟨⟨⟨b,hbT⟩,⟨w,hwT⟩,fun h => hbw (congrArg Subtype.val h)⟩⟩
  obtain ⟨hcover,hinter,hedges,hsepT⟩ := cut_side_pair_properties hwS hsep
  have hS := preconnected_cut_side hG hwS hsep
  have hT := preconnected_cut_side hG hwT hsepT
  have hScard := card_induced_vertices_lt S hb
  have hTcard := card_induced_vertices_lt T haT
  by_cases hwP : w ∈ I.vertices
  · apply I.colourable_of_clique_cut S T hcover hedges ?_ ?_ ⟨w,hwS,hwT⟩ hS hT hScard hTcard hrec
    · intro x hx y hy hxy
      have hxw : x = w := by rwa [hinter] at hx
      have hyw : y = w := by rwa [hinter] at hy
      exact (hxy (hxw.trans hyw.symm)).elim
    · intro x hx
      have hxw : x = w := by rwa [hinter] at hx
      exact hxw ▸ hwP
  · have hPS : I.vertices ⊆ S := by
      intro x hx
      have hrx : RIn G ({w} : Set V)ᶜ r x :=
        (I.connected.2 r hr x hx).mono_set (fun y hy h => hwP (h ▸ hy))
      exact (rIn_side_of_avoids_cut hsep hrx).1 hrS
    have hboundary : OnOuterFace I.embedding I.outer w ∨ ∀ x : T, 3 ≤ (I.lists x.1).card := by
      by_cases hwface : OnOuterFace I.embedding I.outer w
      · exact Or.inl hwface
      · right
        intro x
        apply I.interior_lists
        intro hxface
        have hrx : RIn G ({w} : Set V)ᶜ r x.1 :=
          ((onOuterFace_connSet I.embedding I.outer).2 r (I.on_outer r hr) x.1 hxface).mono_set
            (fun y hy h => hwface (h ▸ hy))
        have hxS := (rIn_side_of_avoids_cut hsep hrx).1 hrS
        have hxw : x.1 = w := by
          have h : x.1 ∈ S ∩ T := ⟨hxS,x.2⟩
          rwa [hinter] at h
        exact hwface (hxw ▸ hxface)
    exact I.colourable_of_unprescribed_cut S T w hwS hwT hwP hPS hcover hinter hedges
      hS hT hboundary hScard hTcard N hN hsmall hrec

end ConnectedPrescription
end Thomassen
