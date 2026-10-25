/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.MixedTwoPathClassification

/-! Separate contracts for three-path cuts with an old short free endpoint
or a prescribed path endpoint. None of the six new proof modules is imported.
The unconditional main theorem remains a separate obligation. -/
@[expose] public section
universe u v

section CompatibleShortEndedPathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- Extend a short induced path whose two ends have old short lists, with
all remaining new vertices on one edge. Old short neighbours of the internal
edge become independent leaves; old short ends have no such neighbours. -/
theorem colourable_induced_with_compatible_short_ended_path (I : BoundaryInstance G C)
    (S : Set V) (M : PlaneMap (G.induce S)) (o : (G.induce S).Dart)
    (hconn : (G.induce S).Preconnected) {a b : V} (q : G.Walk a b)
    (hq : q.IsPath) (hlen : q.length ≤ 5) (hch : q.IsChordless)
    (hQS : ∀ x ∈ q.support, x ∈ S)
    (hOldP : ∀ x ∈ S, x ∈ I.precolor.vertices → x ∈ q.support)
    (u w : V) (huw : G.Adj u w)
    (hnew : ∀ x ∈ q.support, x ∈ I.precolor.vertices ∨ (I.lists x).card ≤ 2 ∨ x = u ∨ x = w)
    (hab : a ≠ b) (haShort : (I.lists a).card ≤ 2) (hbShort : (I.lists b).card ≤ 2)
    (f : V → C) (hf : ∀ x ∈ q.support, f x ∈ I.lists x)
    (hproper : ∀ x ∈ q.support, ∀ y ∈ q.support, G.Adj x y → f x ≠ f y)
    (hface : ∀ x : S, x.1 ∈ q.support → OnOuterFace M o x)
    (hOldFace : ∀ x : S, OnOuterFace I.embedding I.outer x.1 → OnOuterFace M o x)
    (hSsmall : Nat.card S < Nat.card V)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) :
    ∃ c : (G.induce S).Coloring C, (∀ x : S, c x ∈ I.lists x.1) ∧
      ∀ x : S, x.1 ∈ q.support → c x = f x.1 := by
  sorry
end Thomassen.BoundaryInstance

end CompatibleShortEndedPathContracts

section FiveEdgePathChordlessContracts

open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
open Classical
variable {V : Type u} {G : SimpleGraph V}

/-- For a path of at most five edges, girth excludes all chords spanning two
or three edges. Only the explicitly excluded longer chords need checking. -/
lemma five_edge_path_isChordless_of_no_long_chords (hg : 5 ≤ G.egirth) {a b : V} (q : G.Walk a b)
    (hp : q.IsPath) (hlen : q.length ≤ 5)
    (hfar : ∀ i j : ℕ, i+4 ≤ j → j ≤ q.length → ¬ G.Adj (q.getVert i) (q.getVert j)) : q.IsChordless := by
  sorry
end Thomassen

end FiveEdgePathChordlessContracts

section MixedPrescribedThreePathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- A mixed interior three-path with an old short free endpoint is eliminated
when its prescribed endpoint leaves at most three old prescribed vertices
on the initial side.
Both actual pieces, their faces and every short-list attachment are derived. -/
theorem colourable_of_mixed_three_path_short_prefix (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (i j : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (hrj : r.length < j) (hjp : j < p.length)
    (hbShort : (I.lists (p.getVert j)).card ≤ 2)
    (u v2 : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert i)) (huz : G.Adj u v2) (hzj : G.Adj v2 (p.getVert j))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end MixedPrescribedThreePathContracts

section MixedThreePathClosureContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The short-prefix mixed reduction applies to the arbitrary original face
in either orientation. Native facial placement of the unprescribed endpoint
is recovered internally. -/
theorem colourable_of_mixed_three_path_short_prefix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2) (u v2 : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert i)) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The same mixed reduction is available at the terminal end of the old
prescription. Reversal preserves every old list, edge and singleton colour. -/
theorem colourable_of_mixed_three_path_short_suffix_arbitrary_face (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn)
    (i : ℕ) (hi2 : i ≤ 2) (hir : i < r.length)
    (b : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2) (u v2 : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hui : G.Adj u (r.getVert (r.length-i))) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- Every mixed interior three-path from a prescribed vertex to a free
boundary vertex with an old short list is a complete strict-induction case.
No exception for six prescribed vertices remains in this three-path case. -/
theorem colourable_of_mixed_three_path_short_free_endpoint (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : x ∈ I.precolor.vertices)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huz : G.Adj u v2) (hzb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end MixedThreePathClosureContracts

section ShortEndpointThreePathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The completed short-endpoint three-path case works on every specified
old facial subarc, with exact transport of its prescription-free condition. -/
theorem colourable_of_interior_three_path_free_subarc_one_short_endpoint (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (s n : ℕ) (hsn : s + 2 ≤ n) (hnp : n + 2 ≤ p.length) (u v : V)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v)
    (hua : G.Adj u (p.getVert s)) (huv : G.Adj u v) (hvn : G.Adj v (p.getVert n))
    (hashort : (I.lists (p.getVert s)).card ≤ 2 ∨ (I.lists (p.getVert n)).card ≤ 2)
    (hPoutside : ∀ x ∈ I.precolor.vertices, x ∉ cycleInterval (walkCycleVertices p) (s + 1) (n - s - 2))
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
theorem colourable_of_free_three_path_short_endpoint_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrlen : 2 ≤ r.length)
    (horder : ∀ i ≤ r.length, r.getVert i = p.getVert i)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u v2 x y : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hx : OnOuterFace I.embedding I.outer x) (hy : OnOuterFace I.embedding I.outer y)
    (hxP : x ∉ I.precolor.vertices) (hyP : y ∉ I.precolor.vertices)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvy : G.Adj v2 y)
    (hyShort : (I.lists y).card ≤ 2) : ListColourable G I.lists := by
  sorry
/-- A free old short boundary list cannot be joined to any other boundary
vertex by a three-edge interior path in a smallest counterexample. Both the
mixed-prescription and the entirely free facial cases are proved internally. -/
theorem colourable_of_three_path_short_free_boundary_endpoint (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : OnOuterFace I.embedding I.outer x)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hbShort : (I.lists b).card ≤ 2)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end ShortEndpointThreePathContracts

section EndpointThreePathContracts

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [instFT : Fintype V]
include instFT

/-- The free complementary facial arc closes every interior three-path from
the initial prescribed endpoint to an unprescribed boundary vertex, regardless
of the latter's list size. -/
theorem colourable_of_initial_prescribed_endpoint_three_path_on_native_face (I : BoundaryInstance G C)
    (hG : G.Preconnected) {a t : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (horder : ∀ k ≤ r.length, r.getVert k = p.getVert k)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hua : G.Adj u a) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- Initial endpoint three-path exclusion, deriving the actual native face
and its orientation from the original instance. -/
theorem colourable_of_initial_prescribed_endpoint_three_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hua : G.Adj u a) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- Terminal endpoint three-path exclusion, using the same exact lists and
prescribed colours with the original path reversed. -/
theorem colourable_of_terminal_prescribed_endpoint_three_path (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (b u v2 : V) (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hut : G.Adj u t) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
/-- The structural three-path step: a free boundary endpoint with an old
short list, or a prescribed initial/terminal endpoint at the other end, always
closes the strict-induction case. Two unrestricted free three-list endpoints
are intentionally retained for the final deletion argument. -/
theorem colourable_of_three_path_forbidden_boundary_configuration (I : BoundaryInstance G C)
    {a t : V} (r : G.Walk a t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (x b u v2 : V) (hx : OnOuterFace I.embedding I.outer x)
    (hb : OnOuterFace I.embedding I.outer b) (hbP : b ∉ I.precolor.vertices)
    (hu : ¬ OnOuterFace I.embedding I.outer u) (hv : ¬ OnOuterFace I.embedding I.outer v2)
    (hux : G.Adj u x) (huv : G.Adj u v2) (hvb : G.Adj v2 b)
    (hforbidden : (I.lists b).card ≤ 2 ∨ x=a ∨ x=t)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists) : ListColourable G I.lists := by
  sorry
end Thomassen.BoundaryInstance

end EndpointThreePathContracts
