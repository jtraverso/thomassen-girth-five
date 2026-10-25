/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.AnchoredFanBase

/-! The actual facial-boundary step of anchored fan induction. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}

/-- A cycle vertex has no third distinct neighbour in its cycle graph. -/
lemma cyclicSubgraph_third_neighbour {k : ℕ} {c : ZMod k → V} (hc : IsCycleMap G c)
    (i : ZMod k) {r s b : V} (hr : (cyclicSubgraph G c).Adj (c i) r)
    (hs : (cyclicSubgraph G c).Adj (c i) s) (hb : (cyclicSubgraph G c).Adj (c i) b)
    (hrs : r ≠ s) : b = r ∨ b = s := by
  have hr' := (cyclicSubgraph_adj_at_iff hc i r).1 hr
  have hs' := (cyclicSubgraph_adj_at_iff hc i s).1 hs
  have hb' := (cyclicSubgraph_adj_at_iff hc i b).1 hb
  rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs' <;> rcases hb' with hb' | hb'
  all_goals first | exact (hrs (hr'.trans hs'.symm)).elim | exact Or.inl (hb'.trans hr'.symm) | exact Or.inr (hb'.trans hs'.symm)

/-- A vertex outside a short path cannot attach at its middle if all three
incident edges belong to the same facial cycle graph. -/
lemma short_facial_path_attachment_is_endpoint {k : ℕ} {c : ZMod k → V}
    (hc : IsCycleMap G c) {z w a b : V} (p : G.Walk z w) (hp : p.IsPath) (hlen : p.length ≤ 2)
    (ha : a ∈ p.support) (hb : b ∉ p.support)
    (hba : (cyclicSubgraph G c).Adj b a)
    (hedges : ∀ x y, s(x,y) ∈ p.edges → (cyclicSubgraph G c).Adj x y)
    (harange : a ∈ Set.range c) : a = z ∨ a = w := by
  cases p with
  | nil => exact Or.inl (by simpa only [Walk.support_nil, List.mem_singleton] using ha)
  | @cons z t _ hzt p =>
    cases p with
    | nil => simpa only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] using ha
    | @cons _ s _ hts p =>
      cases p with
      | nil =>
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with haz | hat | has
        · exact Or.inl haz
        · subst a
          obtain ⟨i, hi⟩ := harange
          have hzs : z ≠ w := by
            have hnd := hp.support_nodup
            simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, not_false_eq_true, or_false, not_or, List.nodup_nil, and_true] at hnd
            exact hnd.1.2
          have htz : (cyclicSubgraph G c).Adj (c i) z := by rw [hi]; exact (hedges z t (by simp)).symm
          have hts' : (cyclicSubgraph G c).Adj (c i) w := by rw [hi]; exact hedges t w (by simp)
          have htb : (cyclicSubgraph G c).Adj (c i) b := by rw [hi]; exact hba.symm
          rcases cyclicSubgraph_third_neighbour hc i htz hts' htb hzs with h | h
          · exact (hb (by simp [h])).elim
          · exact (hb (by simp [h])).elim
        · exact Or.inr has
      | cons h p => simp only [Walk.length_cons] at hlen; omega

namespace BoundaryInstance
variable [Fintype V]

/-- Both kinds of relevant chords in an anchored fan have complete strict
cuts: root-to-short-neighbour spokes and edges of the old prescription. -/
lemma anchoredFan_adj_consecutive_of_strict_induction (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    (hbad : ¬ RootStarExtension I b f)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) (i j : ZMod k)
    (hkind : (c i = b ∧ (I.lists (c j)).card ≤ 2) ∨
      (c i ∈ I.precolor.vertices ∧ c j ∈ I.precolor.vertices))
    (hadj : G.Adj (c i) (c j)) : j = i + 1 ∨ i = j + 1 := by
  by_contra h
  push Not at h
  obtain ⟨S, T, hSsmall, hTsmall, hcover, hinter, hedges, hSc, hTc⟩ :=
    full_face_chord_separation_at I.embedding hc hk hface hG i j hadj h.1 h.2
  rcases hkind with ⟨hib, hjs⟩ | ⟨hiP, hjP⟩
  · have hcut : S ∩ T = {b, c j} := by simpa only [hib] using hinter
    exact hbad (I.anchoredFan_extension_of_spoke_cut hcard b (c j) hbP ha (by rwa [hib] at hadj) hjs hbface f hf hp
      S T hcover hcut hedges hSc hTc hSsmall hTsmall N hN hsmall hfan)
  · exact hbad (I.anchoredFan_extension_of_prescribed_edge_cut hcard b hbP ha hbface f hf hp
      (c i) (c j) hadj hiP hjP S T hcover hinter hedges hSc hTc hSsmall hTsmall N hN hsmall hfan)

/-- With all relevant chords removed by strict cuts, the old prescription
and root fan form a bounded native path. This closes the normalized face step. -/
theorem anchoredFan_extension_of_facial_boundary (I : BoundaryInstance G C)
    (hcard : I.precolor.vertices.card ≤ 3) (b : V) (hbP : b ∉ I.precolor.vertices)
    (ha : ∃ a ∈ I.precolor.vertices, G.Adj b a) (hG : G.Preconnected)
    (hbface : OnOuterFace I.embedding I.outer b) (f : V → C)
    (hf : ∀ y ∈ rootStar I b, f y ∈ I.lists y)
    (hp : ∀ y ∈ rootStar I b, ∀ z ∈ rootStar I b, G.Adj y z → f y ≠ f z)
    {k : ℕ} [NeZero k] {c : ZMod k → V} (hc : IsCycleMap G c) (hk : 3 ≤ k)
    (hface : IsFacialCycleAlong I.embedding hc Set.univ)
    (hrange : ∀ y, OnOuterFace I.embedding I.outer y → y ∈ Set.range c) (hcb : c 0 = b)
    (N : ℕ) (hN : Nat.card V < N)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < N → ListColourable H J.lists)
    (hfan : AnchoredFanBelow.{u,v} C (Nat.card V)) : RootStarExtension I b f := by
  by_contra hbad
  have hallowed := I.anchoredFan_adj_consecutive_of_strict_induction hcard b hbP ha hG hbface f hf hp hbad hc hk hface N hN hsmall hfan
  have hcycle : ∀ y z, OnOuterFace I.embedding I.outer y → OnOuterFace I.embedding I.outer z →
      ((y = b ∧ (I.lists z).card ≤ 2) ∨ (y ∈ I.precolor.vertices ∧ z ∈ I.precolor.vertices)) →
      G.Adj y z → (cyclicSubgraph G c).Adj y z := by
    intro y z hy hz hkind hyz
    obtain ⟨i, hi⟩ := hrange y hy
    obtain ⟨j, hj⟩ := hrange z hz
    have hcons := hallowed i j (by rwa [hi, hj]) (by rwa [hi, hj])
    rw [← hi, ← hj]
    apply (cyclicSubgraph_adj_at_iff hc i _).2
    exact hcons.elim (fun h => Or.inl (congrArg c h)) (fun h => Or.inr (congrArg c (by linear_combination -h)))
  obtain ⟨a, haP, hba⟩ := ha
  obtain ⟨z, w, p, hpath, hn, hPdef, hplen⟩ := I.exists_short_prescribed_path hcard ⟨a, haP⟩
  have hP : ∀ y, y ∈ I.precolor.vertices ↔ y ∈ p.support := by simp only [hPdef, BoundaryPrecolor.vertices, List.mem_toFinset, implies_true]
  have hbaCycle := hcycle b a hbface (I.on_outer a haP) (Or.inl ⟨rfl, by simp [I.singleton a haP]⟩) hba
  have hpEdges : ∀ y z, s(y,z) ∈ p.edges → (cyclicSubgraph G c).Adj y z := by
    intro y z he
    have hyP := (hP y).2 (p.fst_mem_support_of_mem_edges he)
    have hzP := (hP z).2 (p.snd_mem_support_of_mem_edges he)
    exact hcycle y z (I.on_outer y hyP) (I.on_outer z hzP) (Or.inr ⟨hyP, hzP⟩) (p.adj_of_mem_edges he)
  have haEnd := short_facial_path_attachment_is_endpoint hc p hpath hplen ((hP a).1 haP)
    (fun h => hbP ((hP b).2 h)) hbaCycle hpEdges (hrange a (I.on_outer a haP))
  obtain ⟨t, q, hq, hqlen, hqverts⟩ : ∃ t, ∃ q : G.Walk a t, q.IsPath ∧ q.length ≤ 2 ∧
      ∀ y, y ∈ I.precolor.vertices ↔ y ∈ q.support := by
    rcases haEnd with haz | haw
    · let q := p.copy haz.symm rfl
      exact ⟨w, q, (Walk.isPath_copy _ _ _).2 hpath, by simpa only [q, Walk.length_copy] using hplen,
        by simpa only [q, Walk.support_copy] using hP⟩
    · let q := p.reverse.copy haw.symm rfl
      exact ⟨z, q, (Walk.isPath_copy _ _ _).2 hpath.reverse, by simpa only [q, Walk.length_copy, Walk.length_reverse] using hplen,
        by simpa only [q, Walk.support_copy, Walk.support_reverse, List.mem_reverse] using hP⟩
  have hbound : ∀ y, G.Adj b y → (I.lists y).card ≤ 2 → y = c 1 ∨ y = c (-1) := by
    intro y hby hys
    have hyface : OnOuterFace I.embedding I.outer y := by
      by_contra h
      have h3 := I.interior_lists y h
      omega
    have hedge := hcycle b y hbface hyface (Or.inl ⟨rfl, hys⟩) hby
    rw [← hcb] at hedge
    simpa only [zero_add, zero_sub] using (cyclicSubgraph_adj_at_iff hc 0 y).1 hedge
  have haChoices := hbound a hba (by simp [I.singleton a haP])
  have hne : c 1 ≠ c (-1) := by
    intro h
    have hz : (2 : ZMod k) = 0 := by have he := hc.inj h; linear_combination he
    exact zmod_two_ne_zero_of_three_le hk hz
  rcases haChoices with ha1 | ham
  · have hbx : G.Adj b (c (-1)) := by rw [← hcb]; simpa only [neg_add_cancel] using (hc.adj (-1)).symm
    apply hbad (I.rootStar_extension_of_attached_short_path q hq hqlen hqverts b hbP hba hbface f hf hp
      (c (-1)) hbx (by rw [ha1]; exact hne.symm) ?_ N hN hsmall)
    intro y hby hys
    simpa only [← ha1] using hbound y hby hys
  · have hbx : G.Adj b (c 1) := by rw [← hcb]; simpa only [zero_add] using hc.adj 0
    apply hbad (I.rootStar_extension_of_attached_short_path q hq hqlen hqverts b hbP hba hbface f hf hp
      (c 1) hbx (by rw [ham]; exact hne) ?_ N hN hsmall)
    intro y hby hys
    have h := hbound y hby hys
    simpa only [← ham] using h.symm

end BoundaryInstance
end Thomassen
