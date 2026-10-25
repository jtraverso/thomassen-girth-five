/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ShortPathColouring

/-! Additional short-list neighbours in short-path cuts. -/

@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- A path of at most four edges has no chord unless its endpoints are adjacent. -/
lemma four_edge_path_isChordless (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 4) (hends : ¬ G.Adj a b) : q.IsChordless := by
  apply Walk.isChordless_iff_forall_mem_edges.2
  intro x y hx hy hxy
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hx
  obtain ⟨j, hjy, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hy
  subst x
  subst y
  have hnear : ∀ i j : ℕ, i ≤ q.length → j ≤ q.length → i ≤ j →
      G.Adj (q.getVert i) (q.getVert j) → s(q.getVert i, q.getVert j) ∈ q.edges := by
    intro i j hi hj hij hxy
    rcases (by omega : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4) with h | h | h | h | h
    · exact (hxy.ne (congrArg q.getVert h.symm)).elim
    · apply q.mk_mem_edges_iff_exists.2
      exact ⟨i, by omega, by rw [h]⟩
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h02 : G.Adj (q.getVert i) (q.getVert (i + 2)) := by rwa [h] at hxy
      exact (neighbors_nonadjacent hg h01 h02 (by simpa only [Nat.add_assoc] using h12)).elim
    · have h01 := q.adj_getVert_succ (by omega : i < q.length)
      have h12 := q.adj_getVert_succ (by omega : i + 1 < q.length)
      have h23 := q.adj_getVert_succ (by omega : i + 2 < q.length)
      have hne : q.getVert i ≠ q.getVert (i + 2) := fun heq => by
        have hidx := hp.getVert_injOn hi (by change i + 2 ≤ q.length; omega) heq
        omega
      have h03 : G.Adj (q.getVert i) (q.getVert (i + 3)) := by rwa [h] at hxy
      have heq := common_neighbor_unique hg hne h01
        (by simpa only [Nat.add_assoc] using h12.symm) h03
        (by simpa only [Nat.add_assoc] using h23)
      have hidx := hp.getVert_injOn (by change i + 1 ≤ q.length; omega)
        (by change i + 3 ≤ q.length; omega) heq
      omega
    · have hi0 : i = 0 := by omega
      have hjlen : j = q.length := by omega
      rw [hi0, hjlen, Walk.getVert_zero, Walk.getVert_length] at hxy
      exact (hends hxy).elim
  rcases le_total i j with h | h
  · exact hnear i j hi hj h hxy
  · simpa only [Sym2.eq_swap] using hnear j i hj hi h hxy.symm

/-- The new first vertex of an induced extended path only touches its first edge. -/
lemma endpoint_neighbour_unique_of_chordless_cons {a b x : V}
    (q : G.Walk a b) (hx : x ∉ q.support) (hxa : G.Adj x a)
    (hch : (Walk.cons hxa q).IsChordless) :
    ∀ z ∈ q.support, G.Adj x z → z = a := by
  intro z hz hxz
  have he := hch.mem_edges (Walk.cons hxa q).start_mem_support
    (by simpa only [Walk.support_cons, List.mem_cons] using Or.inr hz) hxz
  simp only [Walk.edges_cons, List.mem_cons] at he
  rcases he with he | he
  · rcases Sym2.eq_iff.1 he with h | h
    · exact h.2
    · exact (hxa.ne h.1).elim
  · exact (hx (q.fst_mem_support_of_mem_edges he)).elim

/-- An external neighbour of an endpoint of a path of at most two edges has no
other neighbour on that path in girth at least five. -/
lemma short_path_endpoint_neighbour_unique (hg : 5 ≤ G.egirth) {a b x : V}
    (q : G.Walk a b) (hp : q.IsPath) (hlen : q.length ≤ 2)
    (hx : x ∉ q.support) (hxa : G.Adj x a) :
    ∀ z ∈ q.support, G.Adj x z → z = a := by
  have hpath : (Walk.cons hxa q).IsPath :=
    Walk.IsPath.mk' (by simpa only [Walk.support_cons, List.nodup_cons] using And.intro hx hp.support_nodup)
  have hch := short_path_isChordless hg (Walk.cons hxa q) hpath (by simp only [Walk.length_cons]; omega)
  exact endpoint_neighbour_unique_of_chordless_cons q hx hxa hch

namespace BoundaryInstance
variable {C : Type v} [Fintype V]

omit [Fintype V] in
/-- Independently choose colours for additional two-list vertices, each having
at most one neighbour in the already coloured piece. The original short-edge
invariant proves independence of the added vertices. -/
lemma extend_colouring_over_short_set (I : BoundaryInstance G C) (T A : Set V)
    (hdisjoint : Disjoint T A) (hnotP : ∀ x ∈ A, x ∉ I.precolor.vertices)
    (hshort : ∀ x ∈ A, (I.lists x).card ≤ 2)
    (c : (G.induce T).Coloring C)
    (hone : ∀ x ∈ A, ∃ y : T, ∀ z : T, G.Adj x z.1 → z = y) :
    ∃ f : V → C, (∀ x : T, f x.1 = c x) ∧
      (∀ x ∈ A, f x ∈ I.lists x) ∧
      (∀ x ∈ A ∪ T, ∀ y ∈ A ∪ T, G.Adj x y → f x ≠ f y) := by
  have hchoice : ∀ x ∈ A, ∃ t ∈ I.lists x, ∀ z : T, G.Adj x z.1 → t ≠ c z := by
    intro x hx
    obtain ⟨y, hy⟩ := hone x hx
    obtain ⟨t, ht, hty⟩ := Finset.exists_mem_ne (s := I.lists x)
      (by have h := I.outside_precolor_list_ge_two (hnotP x hx); omega) (c y)
    exact ⟨t, ht, fun z hz => by rw [hy z hz]; exact hty⟩
  let f : V → C := fun x => if hx : x ∈ T then c ⟨x, hx⟩ else
    if ha : x ∈ A then (hchoice x ha).choose else I.prescribed x
  have hfT : ∀ x : T, f x.1 = c x := by
    intro x
    simp only [f, dite_eq_left x.2]
  have hfA : ∀ x (hx : x ∈ A), f x = (hchoice x hx).choose := by
    intro x hx
    have hn : x ∉ T := fun h => Set.disjoint_left.1 hdisjoint h hx
    simp only [f, dite_eq_right hn, dite_eq_left hx]
  refine ⟨f, hfT, ?_, ?_⟩
  · intro x hx
    rw [hfA x hx]
    exact (hchoice x hx).choose_spec.1
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hnotP x hx (I.precolor.endpoints_of_mem_edges
        (I.short_edges hxy (hshort x hx) (hshort y hy))).1).elim
    · rw [hfA x hx, hfT ⟨y, hy⟩]
      exact (hchoice x hx).choose_spec.2 ⟨y, hy⟩ hxy
    · rw [hfT ⟨x, hx⟩, hfA y hy]
      exact ((hchoice y hy).choose_spec.2 ⟨x, hx⟩ hxy.symm).symm
    · rw [hfT ⟨x, hx⟩, hfT ⟨y, hy⟩]
      exact c.valid hxy

/-- Enlarge a short separator to an induced native path of at most six vertices.
The additional short vertices are coloured independently before strict induction;
all remaining old short neighbours of the separator must be captured. -/
theorem colourable_of_augmented_short_path_cut (I : BoundaryInstance G C)
    (S T : Set V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) {c d : V} (r : G.Walk c d) (hr : r.IsPath)
    (hrshort : r.length ≤ 5) (hrchordless : r.IsChordless)
    (hqr : ∀ x ∈ q.support, x ∈ r.support) (hrS : ∀ x ∈ r.support, x ∈ S)
    (hExtra : ∀ x ∈ r.support, x ∉ q.support → (I.lists x).card ≤ 2)
    (hAttach : ∀ x ∈ r.support, x ∉ q.support →
      ∃ y ∈ q.support, ∀ z ∈ q.support, G.Adj x z → z = y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x | x ∈ q.support})
    (hedges : ∀ {x y}, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ x ∈ I.precolor.vertices, x ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ x : S, x.1 ∈ r.support → OnOuterFace (inducedPlaneMap I.embedding S) oS x)
    (hInterior : ∀ x : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS x → 3 ≤ (I.lists x.1).card)
    (hCapture : ∀ x ∈ S, x ∉ r.support → (I.lists x).card ≤ 2 →
      ∀ y ∈ q.support, ¬ G.Adj x y)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hpath : ∀ x ∈ q.support, x ∈ S ∧ x ∈ T := by
    intro x hx
    have h : x ∈ S ∩ T := by rwa [hinter]
    exact h
  have hab : a ≠ b := fun h => by
    have hn := (hq.nil_iff_eq).2 h
    have hz := hn.length_eq_zero
    omega
  let : Nontrivial T := ⟨⟨⟨a, (hpath a q.start_mem_support).2⟩,
    ⟨b, (hpath b q.end_mem_support).2⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨cT, hcT⟩ := hsmall T (G.induce T) (I.induceConnected T hTconn.preconnected hP) hTsmall
  have hT : ∀ x : T, cT x ∈ I.lists x.1 := by
    simpa only [induceConnected, inducePrecolor] using hcT
  let A : Set V := {x | x ∈ r.support ∧ x ∉ q.support}
  have hAT : ∀ x ∈ A, x ∉ T := by
    intro x hx hxT
    have h : x ∈ S ∩ T := ⟨hrS x hx.1, hxT⟩
    rw [hinter] at h
    exact hx.2 h
  have hANotP : ∀ x ∈ A, x ∉ I.precolor.vertices := by
    intro x hx hxP
    exact hAT x hx (hP x hxP)
  obtain ⟨f, hfT, hfA, hfProper⟩ := I.extend_colouring_over_short_set T A
    (Set.disjoint_left.2 (fun x hxT hxA => hAT x hxA hxT)) hANotP
    (fun x hx => hExtra x hx.1 hx.2) cT (by
      intro x hxA
      obtain ⟨y, hy, huniq⟩ := hAttach x hxA.1 hxA.2
      refine ⟨⟨y, (hpath y hy).2⟩, ?_⟩
      intro z hxz
      have hzS : z.1 ∈ S := by
        rcases hedges hxz with h | h
        · exact h.2
        · exact (hAT x hxA h.1).elim
      have hzq : z.1 ∈ q.support := by
        have h : z.1 ∈ S ∩ T := ⟨hzS, z.2⟩
        rwa [hinter] at h
      exact Subtype.ext (huniq z.1 hzq hxz))
  have hrAT : ∀ x ∈ r.support, x ∈ A ∪ T := by
    intro x hx
    by_cases hxq : x ∈ q.support
    · exact Or.inr (hpath x hxq).2
    · exact Or.inl ⟨hx, hxq⟩
  have hfr : ∀ x ∈ r.support, f x ∈ I.lists x := by
    intro x hx
    rcases hrAT x hx with hxA | hxT
    · exact hfA x hxA
    · rw [hfT ⟨x, hxT⟩]
      exact hT ⟨x, hxT⟩
  have hNoShort : ∀ x ∈ S, x ∉ r.support → (I.lists x).card ≤ 2 →
      ∀ y ∈ r.support, ¬ G.Adj x y := by
    intro x hxS hxr hxShort y hyr hxy
    by_cases hyq : y ∈ q.support
    · exact hCapture x hxS hxr hxShort y hyq hxy
    · have hyA : y ∈ A := ⟨hyr, hyq⟩
      exact hANotP y hyA (I.precolor.endpoints_of_mem_edges
        (I.short_edges hxy hxShort (hExtra y hyr hyq))).2
  have hrbound : r.support.toFinset.card ≤ 6 := by
    calc
      _ ≤ r.support.length := List.toFinset_card_le r.support
      _ = r.length + 1 := r.length_support
      _ ≤ 6 := by omega
  let P : BoundaryPrecolor G := .path r hr hrbound
  have hPS : ∀ x ∈ P.vertices, x ∈ S := fun x hx => hrS x (List.mem_toFinset.1 hx)
  let Q := P.induce S hPS
  have hQv : ∀ x : S, x ∈ Q.vertices ↔ x.1 ∈ r.support := by
    intro x
    simpa only [P, BoundaryPrecolor.vertices, List.mem_toFinset] using
      BoundaryPrecolor.mem_vertices_induce P S hPS x
  let L : S → Finset C := fun x => if x.1 ∈ r.support then {f x.1} else I.lists x.1
  have hNotP : ∀ x ∈ S, x ∉ r.support → x ∉ I.precolor.vertices := by
    intro x hxS hxq hxP
    have h : x ∈ S ∩ T := ⟨hxS, hP x hxP⟩
    rw [hinter] at h
    exact hxq (hqr x h)
  let J : BoundaryInstance (G.induce S) C := {
    girth := five_le_egirth_induce S I.girth
    embedding := inducedPlaneMap I.embedding S
    outer := oS
    precolor := Q
    lists := L
    prescribed := fun x => f x.1
    on_outer := fun x hx => hface x ((hQv x).1 hx)
    singleton := fun x hx => by simp only [L, ite_eq_left ((hQv x).1 hx)]
    proper_precolor := by
      intro x y he
      have hends := Q.endpoints_of_mem_edges he
      exact hfProper x.1 (hrAT x.1 ((hQv x).1 hends.1))
        y.1 (hrAT y.1 ((hQv y).1 hends.2)) (Q.adj_of_mem_edges he)
    boundary_lists := by
      intro x _ hx
      have hnot : x.1 ∉ r.support := fun h => hx ((hQv x).2 h)
      simp only [L, ite_eq_right hnot]
      exact I.outside_precolor_list_ge_two (hNotP x.1 x.2 hnot)
    interior_lists := by
      intro x hx
      have hnot : x.1 ∉ r.support := fun h => hx (hface x h)
      simpa only [L, ite_eq_right hnot] using hInterior x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x.1 ∈ r.support <;> by_cases hyQ : y.1 ∈ r.support
      · apply (BoundaryPrecolor.mem_edges_induce P S hPS x y).2
        exact List.mem_toFinset.2 (hrchordless.mem_edges hxQ hyQ hxy)
      · have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyQ] using hy
        exact (hNoShort y.1 y.2 hyQ hyOld x.1 hxQ hxy.symm).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxQ] using hx
        exact (hNoShort x.1 x.2 hxQ hxOld y.1 hyQ hxy).elim
      · have hxOld : (I.lists x.1).card ≤ 2 := by simpa only [L, ite_eq_right hxQ] using hx
        have hyOld : (I.lists y.1).card ≤ 2 := by simpa only [L, ite_eq_right hyQ] using hy
        exact (hNotP x.1 x.2 hxQ
          (I.precolor.endpoints_of_mem_edges (I.short_edges hxy hxOld hyOld)).1).elim }
  obtain ⟨cS, hcS⟩ := hsmall S (G.induce S) J hSsmall
  change ∀ x : S, cS x ∈ L x at hcS
  have hS : ∀ x : S, cS x ∈ I.lists x.1 := by
    intro x
    by_cases hx : x.1 ∈ r.support
    · have heq : cS x = f x.1 := Finset.mem_singleton.1
        (by simpa only [L, ite_eq_left hx] using hcS x)
      rw [heq]
      exact hfr x.1 hx
    · simpa only [L, ite_eq_right hx] using hcS x
  refine glue_induced_colourings S T I.lists ?_ hedges cS cT hS hT ?_
  · intro x
    have h := Set.mem_univ x
    rwa [← hcover] at h
  · intro x hx hy
    have hxq : x ∈ q.support := by
      have h : x ∈ S ∩ T := ⟨hx, hy⟩
      rwa [hinter] at h
    have heq : cS ⟨x, hx⟩ = f x := Finset.mem_singleton.1
      (by simpa only [L, ite_eq_left (hqr x hxq)] using hcS ⟨x, hx⟩)
    exact heq.trans (hfT ⟨x, hy⟩)


/-- A separator of one or two edges can be extended by one old short-list
neighbour at each endpoint. Girth and the original short-edge invariant prove
that the resulting native path is induced; no chordlessness of the enlarged
path or choice of compatible colours is assumed. -/
theorem colourable_of_short_path_with_two_short_ends (I : BoundaryInstance G C)
    (S T : Set V) {a b x y : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 2)
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxq : x ∉ q.support) (hyq : y ∉ q.support)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hxshort : (I.lists x).card ≤ 2) (hyshort : (I.lists y).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x ∨ z.1 = y →
      OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z →
      3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → z ≠ y → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  have hab : a ≠ b := fun h => by
    have hz := ((hq.nil_iff_eq).2 h).length_eq_zero
    omega
  have hxy : x ≠ y := by
    intro heq
    have hba := short_path_endpoint_neighbour_unique I.girth q hq hqshort hxq hxa
      b q.end_mem_support (by simpa only [heq] using hby.symm)
    exact hab hba.symm
  let r : G.Walk x y := Walk.cons hxa (q.concat hby)
  have hr : r.IsPath := by
    apply Walk.IsPath.mk'
    change (x :: (q.concat hby).support).Nodup
    apply List.nodup_cons.2
    refine ⟨?_, (hq.concat hyq hby).support_nodup⟩
    simpa only [Walk.support_concat, List.mem_append, List.mem_singleton, not_or] using And.intro hxq hxy
  have hrmem : ∀ z, z ∈ r.support ↔ z ∈ q.support ∨ z = x ∨ z = y := by
    intro z
    simp only [r, Walk.support_cons, Walk.support_concat, List.mem_cons,
      List.mem_append]
    tauto
  have hqS : ∀ z ∈ q.support, z ∈ S := by
    intro z hz
    have h : z ∈ S ∩ T := by rwa [hinter]
    exact h.1
  have hxnotP : x ∉ I.precolor.vertices := by
    intro hxP
    have h : x ∈ S ∩ T := ⟨hxS, hP x hxP⟩
    rw [hinter] at h
    exact hxq h
  have hnoends : ¬ G.Adj x y := fun h => hxnotP
    (I.precolor.endpoints_of_mem_edges (I.short_edges h hxshort hyshort)).1
  apply I.colourable_of_augmented_short_path_cut S T q hq hqpos r hr
    (by simp only [r, Walk.length_cons, Walk.length_concat]; omega)
    (four_edge_path_isChordless I.girth r hr
      (by simp only [r, Walk.length_cons, Walk.length_concat]; omega) hnoends)
    (fun z hz => (hrmem z).2 (Or.inl hz)) ?_ ?_ ?_
    hcover hinter hedges hTconn hP oS ?_ hInterior ?_ hSsmall hTsmall hsmall
  · intro z hz
    rcases (hrmem z).1 hz with hz | rfl | rfl
    · exact hqS z hz
    · exact hxS
    · exact hyS
  · intro z hz hzq
    rcases ((hrmem z).1 hz).resolve_left hzq with rfl | rfl
    · exact hxshort
    · exact hyshort
  · intro z hz hzq
    rcases ((hrmem z).1 hz).resolve_left hzq with rfl | rfl
    · exact ⟨a, q.start_mem_support,
        short_path_endpoint_neighbour_unique I.girth q hq hqshort hxq hxa⟩
    · refine ⟨b, q.end_mem_support, ?_⟩
      intro w hw hyw
      exact short_path_endpoint_neighbour_unique I.girth q.reverse hq.reverse
        (by simpa only [Walk.length_reverse] using hqshort)
        (by simpa only [Walk.support_reverse, List.mem_reverse] using hyq) hby.symm
        w (by simpa only [Walk.support_reverse, List.mem_reverse] using hw) hyw
  · intro z hz
    exact hface z ((hrmem z.1).1 hz)
  · intro z hzS hzr hzshort
    exact hCapture z hzS (fun h => hzr ((hrmem z).2 (Or.inl h)))
      (fun h => hzr ((hrmem z).2 (Or.inr (Or.inl h))))
      (fun h => hzr ((hrmem z).2 (Or.inr (Or.inr h)))) hzshort

/-- If the other separator endpoint is already short, one additional short
neighbour suffices for a separator of up to three edges. The short-edge invariant
excludes the possible five-cycle chord of the enlarged path. -/
theorem colourable_of_short_path_with_one_short_end (I : BoundaryInstance G C)
    (S T : Set V) {a b x : V} (q : G.Walk a b) (hq : q.IsPath)
    (hqpos : 0 < q.length) (hqshort : q.length ≤ 3)
    (hxa : G.Adj x a) (hxq : x ∉ q.support) (hxS : x ∈ S)
    (hxshort : (I.lists x).card ≤ 2) (hbshort : (I.lists b).card ≤ 2)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z | z ∈ q.support})
    (hedges : ∀ {z w}, G.Adj z w → (z ∈ S ∧ w ∈ S) ∨ (z ∈ T ∧ w ∈ T))
    (hTconn : (G.induce T).Connected) (hP : ∀ z ∈ I.precolor.vertices, z ∈ T)
    (oS : (G.induce S).Dart)
    (hface : ∀ z : S, z.1 ∈ q.support ∨ z.1 = x →
      OnOuterFace (inducedPlaneMap I.embedding S) oS z)
    (hInterior : ∀ z : S, ¬ OnOuterFace (inducedPlaneMap I.embedding S) oS z →
      3 ≤ (I.lists z.1).card)
    (hCapture : ∀ z ∈ S, z ∉ q.support → z ≠ x → (I.lists z).card ≤ 2 →
      ∀ w ∈ q.support, ¬ G.Adj z w)
    (hSsmall : Nat.card S < Nat.card V) (hTsmall : Nat.card T < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  let r : G.Walk x b := Walk.cons hxa q
  have hr : r.IsPath := Walk.IsPath.mk'
    (by simpa only [r, Walk.support_cons, List.nodup_cons] using And.intro hxq hq.support_nodup)
  have hrmem : ∀ z, z ∈ r.support ↔ z ∈ q.support ∨ z = x := by
    intro z
    simp only [r, Walk.support_cons, List.mem_cons, or_comm]
  have hxnotP : x ∉ I.precolor.vertices := by
    intro hxP
    have h : x ∈ S ∩ T := ⟨hxS, hP x hxP⟩
    rw [hinter] at h
    exact hxq h
  have hch : r.IsChordless := four_edge_path_isChordless I.girth r hr
    (by simp only [r, Walk.length_cons]; omega)
    (fun h => hxnotP (I.precolor.endpoints_of_mem_edges (I.short_edges h hxshort hbshort)).1)
  apply I.colourable_of_augmented_short_path_cut S T q hq hqpos r hr
    (by simp only [r, Walk.length_cons]; omega) hch
    (fun z hz => (hrmem z).2 (Or.inl hz)) ?_ ?_ ?_
    hcover hinter hedges hTconn hP oS ?_ hInterior ?_ hSsmall hTsmall hsmall
  · intro z hz
    rcases (hrmem z).1 hz with hz | rfl
    · have h : z ∈ S ∩ T := by rwa [hinter]
      exact h.1
    · exact hxS
  · intro z hz hzq
    have heq := ((hrmem z).1 hz).resolve_left hzq
    simpa only [heq] using hxshort
  · intro z hz hzq
    obtain rfl := ((hrmem z).1 hz).resolve_left hzq
    exact ⟨a, q.start_mem_support, endpoint_neighbour_unique_of_chordless_cons q hxq hxa hch⟩
  · intro z hz
    exact hface z ((hrmem z.1).1 hz)
  · intro z hzS hzr hzshort
    exact hCapture z hzS (fun h => hzr ((hrmem z).2 (Or.inl h)))
      (fun h => hzr ((hrmem z).2 (Or.inr h))) hzshort

end BoundaryInstance
end Thomassen
