/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.ConnectedPrescriptionGlobal

/-! Extending a prescribed connected core and its short pendant neighbours. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]

/-- A connected outer core of at most four vertices extends if it covers
every short-list edge and every short vertex outside it has at most one core
neighbour. In particular, short pendant vertices may meet a short core vertex. -/
theorem extend_small_colour_core_of_short_edges_covered (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (L : V → Finset C)
    (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (B : Finset V) (hB : B.card ≤ 4) (hconn : ConnSet G (↑B : Set V))
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hedges : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∨ y ∈ B)
    (hunique : ∀ x, x ∉ B → (L x).card ≤ 2 → ∀ y ∈ B, ∀ z ∈ B,
      G.Adj x y → G.Adj x z → y = z)
    (f : V → C) (hf : ∀ x ∈ B, f x ∈ L x)
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ B, c x = f x := by
  let : Fintype V := Fintype.ofFinite V
  let R : Set V := {x | x ∉ B ∧ (L x).card ≤ 2 ∧ ∃ y ∈ B, G.Adj x y}
  let Q : Set V := (↑B : Set V) ∪ R
  have hRind : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact (hedges hxy hx.2.1 hy.2.1).elim hx.1 hy.1
  obtain ⟨a,ha⟩ := hconn.1
  let attach : V → V := fun x => if hx : x ∈ R then hx.2.2.choose else a
  have hattach : ∀ x ∈ R, attach x ∈ B ∧ G.Adj x (attach x) := by
    intro x hx
    simpa only [attach,dite_eq_left hx] using hx.2.2.choose_spec
  have hchoose : ∀ x ∈ R, ∃ t ∈ L x, t ≠ f (attach x) := by
    intro x _
    exact Finset.exists_mem_ne (by have := hLtwo x; omega) (f (attach x))
  let g : V → C := fun x => if x ∈ B then f x else
    if hx : x ∈ R then (hchoose x hx).choose else f x
  have hgB : ∀ x ∈ B, g x = f x := fun x hx => ite_eq_left hx
  have hgR : ∀ x ∈ R, g x ∈ L x ∧ g x ≠ f (attach x) := by
    intro x hx
    simpa only [g,ite_eq_right hx.1,dite_eq_left hx] using (hchoose x hx).choose_spec
  have hgmem : ∀ x ∈ Q, g x ∈ L x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hgB x hx]; exact hf x hx
    · exact (hgR x hx).1
  have hgproper : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj x y → g x ≠ g y := by
    have hcross : ∀ x ∈ R, ∀ y ∈ B, G.Adj x y → g x ≠ g y := by
      intro x hx y hy hxy
      have he := hunique x hx.1 hx.2.1 y hy (attach x) (hattach x hx).1 hxy (hattach x hx).2
      rw [hgB y hy,he]
      exact (hgR x hx).2
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hgB x hx,hgB y hy]; exact hproper x hx y hy hxy
    · exact (hcross y hy x hx hxy.symm).symm
    · exact hcross x hx y hy hxy
    · exact (hRind x hx y hy hxy).elim
  have hQconn : ConnSet G Q := connSet_adjoin_attached_vertices (↑B : Set V) R hconn
    (fun x hx => ⟨attach x,(hattach x hx).1,(hattach x hx).2⟩)
  have hQface : ∀ x ∈ Q, OnOuterFace M outer x := by
    intro x hx
    rcases hx with hx | hx
    · exact hface x hx
    · by_contra h
      have h3 := hLinterior x h
      have h2 := hx.2.1
      omega
  have hNoShort : ∀ x, x ∉ Q → (L x).card ≤ 2 → ∀ y ∈ Q, ¬ G.Adj x y := by
    intro x hx hxs y hy hxy
    rcases hy with hy | hy
    · exact hx (Or.inr ⟨fun h => hx (Or.inl h),hxs,⟨y,hy,hxy⟩⟩)
    · exact (hedges hxy hxs hy.2.1).elim (fun h => hx (Or.inl h)) hy.1
  let L' : V → Finset C := fun x => if x ∈ Q then {g x} else L x
  let I : ConnectedPrescription G C := {
    girth := hg
    embedding := M
    outer := outer
    vertices := Q
    connected := hQconn
    paths_short := by
      intro x y p hp hs
      exact path_length_le_five_of_small_core Q B hB (by
        intro z hz hzB r hr s hs hzr hzs
        have hzR : z ∈ R := hz.resolve_left hzB
        have hrB : r ∈ B := hr.resolve_right (fun h => hRind z hzR r h hzr)
        have hsB : s ∈ B := hs.resolve_right (fun h => hRind z hzR s h hzs)
        exact hunique z hzB hzR.2.1 r hrB s hsB hzr hzs) p hp hs
    lists := L'
    prescribed := g
    on_outer := hQface
    singleton := fun x hx => ite_eq_left hx
    proper := fun {x y} hx hy hxy => hgproper x hx y hy hxy
    boundary_lists := by
      intro x _ hx
      simpa only [L',ite_eq_right hx] using hLtwo x
    interior_lists := by
      intro x hx
      have hn : x ∉ Q := fun h => hx (hQface x h)
      simpa only [L',ite_eq_right hn] using hLinterior x hx
    short_edges := by
      intro x y hxy hx hy
      by_cases hxQ : x ∈ Q <;> by_cases hyQ : y ∈ Q
      · exact ⟨hxQ,hyQ⟩
      · exact (hNoShort y hyQ (by simpa only [L',ite_eq_right hyQ] using hy) x hxQ hxy.symm).elim
      · exact (hNoShort x hxQ (by simpa only [L',ite_eq_right hxQ] using hx) y hyQ hxy).elim
      · have he := hedges hxy (by simpa only [L',ite_eq_right hxQ] using hx)
          (by simpa only [L',ite_eq_right hyQ] using hy)
        exact he.elim (fun h => (hxQ (Or.inl h)).elim) (fun h => (hyQ (Or.inl h)).elim) }
  obtain ⟨c,hc⟩ := I.colourable
  have hfixed : ∀ x ∈ Q, c x = g x := by
    intro x hx
    have h := hc x
    change c x ∈ L' x at h
    simpa only [L',ite_eq_left hx,Finset.mem_singleton] using h
  refine ⟨c,?_,fun x hx => (hfixed x (Or.inl hx)).trans (hgB x hx)⟩
  intro x
  by_cases hx : x ∈ Q
  · rw [hfixed x hx]; exact hgmem x hx
  · have h := hc x
    change c x ∈ L' x at h
    simpa only [L',ite_eq_right hx] using h

/-- A properly coloured connected outer core of at most four vertices extends
if every short-list edge is in the core and each short vertex outside it has
at most one core neighbour. -/
theorem extend_small_colour_core (M : PlaneMap G) (outer : G.Dart)
    (hg : 5 ≤ G.egirth) (L : V → Finset C)
    (hLtwo : ∀ x, 2 ≤ (L x).card)
    (hLinterior : ∀ x, ¬ OnOuterFace M outer x → 3 ≤ (L x).card)
    (B : Finset V) (hB : B.card ≤ 4) (hconn : ConnSet G (↑B : Set V))
    (hface : ∀ x ∈ B, OnOuterFace M outer x)
    (hedges : ∀ {x y}, G.Adj x y → (L x).card ≤ 2 → (L y).card ≤ 2 → x ∈ B ∧ y ∈ B)
    (hunique : ∀ x, x ∉ B → (L x).card ≤ 2 → ∀ y ∈ B, ∀ z ∈ B,
      G.Adj x y → G.Adj x z → y = z)
    (f : V → C) (hf : ∀ x ∈ B, f x ∈ L x)
    (hproper : ∀ x ∈ B, ∀ y ∈ B, G.Adj x y → f x ≠ f y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ B, c x = f x := by
  exact extend_small_colour_core_of_short_edges_covered M outer hg L hLtwo hLinterior
    B hB hconn hface (fun hxy hx hy => Or.inl (hedges hxy hx hy).1) hunique f hf hproper

end Thomassen
