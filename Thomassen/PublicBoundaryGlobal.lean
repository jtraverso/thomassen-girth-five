/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.PublicBoundaryExtension
public import Thomassen.OuterBoundary

/-! The source-aligned short-path theorem with all exterior components present. -/
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- Dvořák–Kawarabayashi (2011), Theorem 1, including possibly disconnected
plane graphs. A marked face can have several boundary dart orbits, recorded
by ComponentOuterBoundary. Proper chords of the precoloured path are allowed. -/
theorem dvorak_kawarabayashi_theorem_1_global
    (M : PlaneMap G) (B : Set V) (hB : ComponentOuterBoundary M B)
    (hg : 5 ≤ G.egirth) {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hlen : p.length ≤ 5)
    (hPB : ∀ x ∈ p.support, x ∈ B)
    (L : V → Finset C) (f : V → C)
    (hsingle : ∀ x ∈ p.support, L x = {f x})
    (hproper : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x ≠ f y)
    (hboundary : ∀ x ∈ B, x ∉ p.support → 2 ≤ (L x).card)
    (hinterior : ∀ x, x ∉ B → 3 ≤ (L x).card)
    (hshort : ∀ x, (L x).card = 2 → ∀ y, (L y).card ≤ 2 → ¬ G.Adj x y) :
    ∃ c : G.Coloring C, (∀ x, c x ∈ L x) ∧ ∀ x ∈ p.support, c x = f x := by
  have htwo : ∀ x, x ∉ p.support → 2 ≤ (L x).card := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact hboundary x hxB hx
    · exact (by omega : 2 ≤ 3).trans (hinterior x hxB)
  have hnonempty : ∀ x, (L x).Nonempty := by
    intro x
    by_cases hx : x ∈ p.support
    · rw [hsingle x hx]; exact Finset.singleton_nonempty _
    · exact Finset.card_pos.1 (by have := htwo x hx; omega)
  have hcomponent : ∀ K : G.ConnectedComponent,
      ListColourable K.toSimpleGraph (fun x : K => L x.1) := by
    intro K
    by_cases hedge : Nonempty K.toSimpleGraph.Dart
    · obtain ⟨o,ho⟩ := hB K hedge
      by_cases haK : a ∈ K.supp
      · have hPK : ∀ x ∈ p.support, x ∈ K.supp := by
          intro x hx
          exact (ConnectedComponent.sound (p.takeUntil x hx).reachable).symm.trans haK
        let q := p.induce K.supp hPK
        have hq : q.IsPath := Walk.IsPath.of_map (f := (Embedding.induce K.supp).toHom) (by
          change ((p.induce K.supp hPK).map (Embedding.induce K.supp).toHom).IsPath
          rw [Walk.map_induce]
          exact hp)
        have hqmem : ∀ x : K, x ∈ q.support ↔ x.1 ∈ p.support := by
          intro x; simp only [q,Walk.support_induce,List.mem_attachWith]
        have hqlen : q.length = p.length := by
          rw [← Walk.length_map (Embedding.induce K.supp).toHom,Walk.map_induce]
          rfl
        obtain ⟨c,hc,_⟩ := dvorak_kawarabayashi_theorem_1 (inducedPlaneMap M K.supp) o
          (five_le_egirth_induce K.supp hg) q hq (by omega)
          (fun x hx => ho x (hPB x.1 ((hqmem x).1 hx)))
          (fun x : K => L x.1) (fun x : K => f x.1)
          (fun x hx => hsingle x.1 ((hqmem x).1 hx))
          (fun x hx y hy hxy => hproper x.1 ((hqmem x).1 hx) y.1 ((hqmem y).1 hy) hxy)
          (fun x _ hx => htwo x.1 (fun h => hx ((hqmem x).2 h)))
          (fun x hx => hinterior x.1 (fun h => hx (ho x h)))
          (fun x hx y hy hxy => hshort x.1 hx y.1 hy hxy)
        exact ⟨c,hc⟩
      · have hNoP : ∀ x : K, x.1 ∉ p.support := by
          intro x hx
          exact haK ((ConnectedComponent.sound (p.takeUntil x.1 hx).reachable).trans x.2)
        let I : BoundaryInstance K.toSimpleGraph C := {
          girth := five_le_egirth_induce K.supp hg
          embedding := inducedPlaneMap M K.supp
          outer := o
          precolor := .empty
          lists := fun x => L x.1
          prescribed := fun x => f x.1
          on_outer := by simp
          singleton := by simp
          proper_precolor := by simp
          boundary_lists := fun x _ _ => htwo x.1 (hNoP x)
          interior_lists := fun x hx => hinterior x.1 (fun h => hx (ho x h))
          short_edges := by
            intro x y hxy hx hy
            have h2 := htwo x.1 (hNoP x)
            exact (hshort x.1 (by omega) y.1 hy hxy).elim }
        exact boundary_extension C K K.toSimpleGraph I
    · let g : K → C := fun x => (hnonempty x.1).choose
      exact ⟨Coloring.mk g (fun {x y} hxy => (hedge ⟨⟨(x,y),hxy⟩⟩).elim),
        fun x => (hnonempty x.1).choose_spec⟩
  let c := G.homOfConnectedComponents (fun K => (hcomponent K).choose)
  have hc : ∀ x, c x ∈ L x := fun x =>
    (hcomponent (G.connectedComponentMk x)).choose_spec
      ⟨x,ConnectedComponent.connectedComponentMk_mem⟩
  exact ⟨c,hc,fun x hx => Finset.mem_singleton.1 (by simpa only [hsingle x hx] using hc x)⟩

end Thomassen
