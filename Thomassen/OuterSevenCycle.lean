/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.CycleMapWalk
public import Thomassen.PublicBoundaryExtension
public import Mathlib.Tactic.IntervalCases

/-! The seven-cycle specialization of Asghar (2012), Lemma 3.2.3.
The proof releases a vertex with differently coloured neighbours, rather than
reproducing the source's simultaneous three-state induction. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V}
variable {k : ℕ} {c : ZMod k → V}

/-- A chord of a cycle of at most seven vertices creates a triangle or four-cycle. -/
lemma cycle_isChordless_of_length_le_seven [NeZero k] (hg : 5 ≤ G.egirth) (hc : IsCycleMap G c)
    (hk : 3 ≤ k) (hsmall : k ≤ 7) : IsChordless G c := by
  intro i j hxy
  let n := (j - i).val
  have hn : n < k := ZMod.val_lt _
  have hij : j = i + (n : ZMod k) := by simp [n]
  by_cases hshort : n ≤ 3
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · have hji : j = i := by simpa only [h0, Nat.cast_zero, add_zero] using hij
      exact (hxy.ne (congrArg c hji.symm)).elim
    · exact Or.inl (by simpa only [h1, Nat.cast_one] using hij)
    · exact (cycle_no_chord_two hg hc i (by simpa only [hij, h2, Nat.cast_ofNat] using hxy)).elim
    · exact (cycle_no_chord_three hg hc hk i
        (by simpa only [hij, h3, Nat.cast_ofNat] using hxy)).elim
  · have hm : 1 ≤ k - n ∧ k - n ≤ 3 := by omega
    have hji : i = j + ((k - n : ℕ) : ZMod k) := by
      rw [hij, add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hn.le, ZMod.natCast_self, add_zero]
    have hcases : k - n = 1 ∨ k - n = 2 ∨ k - n = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · exact Or.inr (by simpa only [h1, Nat.cast_one] using hji)
    · exact (cycle_no_chord_two hg hc j
        (by simpa only [hji, h2, Nat.cast_ofNat] using hxy.symm)).elim
    · exact (cycle_no_chord_three hg hc hk j
        (by simpa only [hji, h3, Nat.cast_ofNat] using hxy.symm)).elim


/-- Every proper colouring of a seven-cycle has a vertex whose two neighbours
receive distinct colours. Otherwise the colours are two-periodic on an odd cycle. -/
lemma seven_cycle_exists_distinct_neighbour_colours (d : ZMod 7 → C)
    (hproper : ∀ i, d i ≠ d (i+1)) : ∃ j, d (j-1) ≠ d (j+1) := by
  by_contra h
  push Not at h
  have h1 := h 1
  have h3 := h 3
  have h5 := h 5
  have h0 := h 0
  norm_num at h1 h3 h5 h0
  have hp := hproper 0
  norm_num at hp
  exact hp (h1.trans (h3.trans (h5.trans h0)))

/-- Seven-cycle extension by releasing one vertex. Its two differently coloured
neighbours force the original colour in a three-element auxiliary list, while
the other six prescribed vertices form a path handled by the proved extension. -/
theorem extend_outer_seven_cycle_map [Finite V] {n : ℕ} (hn : n = 7)
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    (d : ZMod n → V) (hd : IsCycleMap G d)
    (hface : ∀ i, OnOuterFace M outer (d i))
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ i, f (d i) ∈ L (d i))
    (hproper : ∀ i, f (d i) ≠ f (d (i+1))) :
    ∃ col : G.Coloring C, (∀ x, col x ∈ L x) ∧ ∀ i, col (d i) = f (d i) := by
  subst n
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨j,hj⟩ := seven_cycle_exists_distinct_neighbour_colours (fun i => f (d i)) hproper
  let v := d j
  let d' : ZMod 7 → V := fun i => d (j+1+i)
  have hd' : IsCycleMap G d' := {
    inj := fun i k h => add_left_cancel (hd.inj h)
    adj := fun i => by simpa only [d',add_assoc] using hd.adj (j+1+i) }
  obtain ⟨q,hq,hqlen,hqvert⟩ := exists_walk_of_cycleMap (by decide : 3 ≤ 7) hd'
  let r := q.take 5
  have hr : r.IsPath := hq.isPath_take (by omega)
  have hrlen : r.length = 5 := by simp only [r,Walk.take_length,hqlen]; decide
  let B := r.support.toFinset
  have hrvert : ∀ m ≤ 5, r.getVert m = d (j+1+(m : ZMod 7)) := by
    intro m hm
    rw [Walk.take_getVert,Nat.min_eq_right hm]
    exact hqvert m (by omega)
  have hB : ∀ z, z ∈ B ↔ z ∈ Set.range d ∧ z ≠ v := by
    intro z
    constructor
    · intro hz
      obtain ⟨m,hmz,hm⟩ := Walk.mem_support_iff_exists_getVert.1 (List.mem_toFinset.1 hz)
      rw [hrlen] at hm
      have hmz' : d (j+1+(m : ZMod 7)) = z := (hrvert m hm).symm.trans hmz
      refine ⟨⟨j+1+(m : ZMod 7),hmz'⟩,?_⟩
      intro hzv
      have he := hd.inj (hmz'.trans hzv)
      have hnonzero : (1+(m : ZMod 7)) ≠ 0 := by interval_cases m <;> decide
      apply hnonzero
      linear_combination he
    · rintro ⟨⟨k,rfl⟩,hkv⟩
      let m := (k-j-1).val
      have hm7 : m < 7 := ZMod.val_lt _
      have hmcast : (m : ZMod 7) = k-j-1 := ZMod.natCast_zmod_val _
      have hm6 : m ≠ 6 := by
        intro heq
        have he : k = j := by
          rw [heq] at hmcast
          have hseven : (7 : ZMod 7)=0 := by decide
          linear_combination -hmcast + hseven
        exact hkv (congrArg d he)
      have hm : m ≤ 5 := by omega
      apply List.mem_toFinset.2
      apply Walk.mem_support_iff_exists_getVert.2
      refine ⟨m,?_,by rw [hrlen]; exact hm⟩
      rw [hrvert m hm]
      congr 1
      linear_combination hmcast
  have hvB : v ∉ B := fun h => (hB v).1 h |>.2 rfl
  have hcard : B.card ≤ 6 := by
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support,hrlen]
  have hconn : ConnSet G (↑B : Set V) := by
    simpa only [B,List.coe_toFinset] using walk_support_connSet r
  have hprev : f v ≠ f (d (j-1)) := by
    simpa only [sub_add_cancel] using (hproper (j-1)).symm
  have hnext : f v ≠ f (d (j+1)) := hproper j
  let F : Finset C := {f v,f (d (j-1)),f (d (j+1))}
  have hF : F.card = 3 := by simp [F,hprev,hnext,hj]
  let L' : V → Finset C := fun z => if z ∈ B then {f z} else if z=v then F else L z
  have hlarge : ∀ z, z ∉ B → 3 ≤ (L' z).card := by
    intro z hz
    by_cases hzv : z = v
    · simp only [L',ite_eq_right hz,ite_eq_left hzv,hF]; omega
    · simpa only [L',ite_eq_right hz,ite_eq_right hzv] using hL z
  have hch := cycle_isChordless_of_length_le_seven hg hd (by decide : 3 ≤ 7) (by decide : 7 ≤ 7)
  obtain ⟨col,hcol⟩ := colourable_connected_boundary_set_six M outer hg B hcard hconn L' f
    (by intro z hz; obtain ⟨i,hi⟩ := ((hB z).1 hz).1; simpa only [hi] using hface i)
    (fun z hz => ite_eq_left hz) (by
      intro z hz w hw hzw
      obtain ⟨i,hi⟩ := ((hB z).1 hz).1
      obtain ⟨k,hk⟩ := ((hB w).1 hw).1
      subst z; subst w
      rcases hch i k hzw with he | he
      · simpa only [he] using hproper i
      · simpa only [he] using (hproper k).symm)
    (fun z _ hz => (by omega : 2 ≤ 3).trans (hlarge z hz)) (by
      intro z hz
      have hzB : z ∉ B := by
        intro h
        obtain ⟨i,hi⟩ := ((hB z).1 h).1
        exact hz (hi ▸ hface i)
      exact hlarge z hzB) (by
      intro z w _ hz hw
      constructor
      · by_contra hn; have := hlarge z hn; omega
      · by_contra hn; have := hlarge w hn; omega)
  have hfixed : ∀ z ∈ B, col z = f z := by
    intro z hz
    have h := hcol z
    change col z ∈ L' z at h
    simpa only [L',ite_eq_left hz,Finset.mem_singleton] using h
  have hprevB : d (j-1) ∈ B := (hB _).2 ⟨Set.mem_range_self _,by
    intro he; have he' := hd.inj he
    have hz : (1 : ZMod 7)=0 := by linear_combination -he'
    exact (by decide : (1 : ZMod 7) ≠ 0) hz⟩
  have hnextB : d (j+1) ∈ B := (hB _).2 ⟨Set.mem_range_self _,by
    intro he; have he' := hd.inj he
    have hz : (1 : ZMod 7)=0 := by linear_combination he'
    exact (by decide : (1 : ZMod 7) ≠ 0) hz⟩
  have hvcol : col v = f v := by
    have hm := hcol v
    change col v ∈ L' v at hm
    have hmF : col v ∈ F := by
      simpa [L',hvB] using hm
    change col v ∈ ({f v,f (d (j-1)),f (d (j+1))} : Finset C) at hmF
    rcases Finset.mem_insert.1 hmF with hm | hm
    · exact hm
    · rcases Finset.mem_insert.1 hm with hm | hm
      · exact (col.valid (show G.Adj v (d (j-1)) by simpa only [sub_add_cancel] using (hd.adj (j-1)).symm)
          (hm.trans (hfixed _ hprevB).symm)).elim
      · have hm : col v = f (d (j+1)) := Finset.mem_singleton.1 hm
        exact (col.valid (hd.adj j) (hm.trans (hfixed _ hnextB).symm)).elim
  /- Original colours on all seven vertices are now forced. -/
  have hcyclefixed : ∀ i, col (d i) = f (d i) := by
    intro i
    by_cases he : d i = v
    · simpa only [he] using hvcol
    · exact hfixed _ ((hB _).2 ⟨Set.mem_range_self _,he⟩)
  refine ⟨col,?_,hcyclefixed⟩
  intro z
  by_cases hz : z ∈ Set.range d
  · obtain ⟨i,rfl⟩ := hz
    rw [hcyclefixed i]
    exact hf i
  · have hzB : z ∉ B := fun h => hz ((hB z).1 h).1
    have hzv : z ≠ v := fun he => hz ⟨j,he.symm⟩
    have h := hcol z
    change col z ∈ L' z at h
    simpa only [L',ite_eq_right hzB,ite_eq_right hzv] using h


/-- The girth-five seven-cycle case of Asghar (2012), Lemma 3.2.3, in native
Mathlib walks. Any proper allowed colouring of an outer seven-cycle extends.
The face-incidence premise is weaker than requiring the cycle to be the whole
outer-face boundary. -/
theorem extend_outer_seven_cycle [Finite V]
    (M : PlaneMap G) (outer : G.Dart) (hg : 5 ≤ G.egirth)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hlen : p.length = 7)
    (hface : ∀ x ∈ p.support, OnOuterFace M outer x)
    (L : V → Finset C) (hL : ∀ x, 3 ≤ (L x).card)
    (f : V → C) (hf : ∀ x ∈ p.support, f x ∈ L x)
    (hproper : ∀ {x y}, s(x,y) ∈ p.edges → f x ≠ f y) :
    ∃ col : G.Coloring C, (∀ x, col x ∈ L x) ∧ ∀ x ∈ p.support, col x = f x := by
  let d := walkCycleVertices p
  have hd := walk_isCycleMap p hp
  obtain ⟨col,hcol,hfixed⟩ := extend_outer_seven_cycle_map hlen M outer hg d hd
    (fun i => hface _ (p.getVert_mem_support _)) L hL f
    (fun i => hf _ (p.getVert_mem_support _)) (by
      intro i
      apply hproper
      exact (walkCycleVertices_edges p hp _ _).1 (cycleForward hd i).adj)
  refine ⟨col,hcol,?_⟩
  intro x hx
  have hxR : x ∈ Set.range d := by rwa [walkCycleVertices_range p hp]
  obtain ⟨i,rfl⟩ := hxR
  exact hfixed i

end Thomassen
