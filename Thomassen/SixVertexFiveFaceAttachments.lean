/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Thomassen.SixVertexAlternatingFreeDeletion

/-! Boundary conflicts of interior attachments outside a free five-face. -/
@[expose] public section
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
universe u v
namespace Thomassen.BoundaryInstance
open Classical
variable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]

/-- An interior vertex attached outside a free five-face cannot also meet
an old free short list or either old prescribed endpoint. Thus the new short
lists can only attach to internal vertices of the retained prescription. -/
theorem inner_five_face_attachment_no_forbidden_boundary_neighbour_six (I : BoundaryInstance G C)
    {s t a : V} (r : G.Walk s t) (hr : r.IsPath) (hn : r.support.toFinset.card ≤ 6)
    (hP : I.precolor = .path r hr hn) (hrpos : 0 < r.length)
    (p : G.Walk a a) (hp : p.IsCycle)
    (hface : IsFacialCycleAlong I.embedding (walk_isCycleMap p hp) Set.univ)
    (hroot : SameCycle I.embedding.facePerm I.outer (walkArcRoot p hp))
    (haP : a ∉ I.precolor.vertices) (hdP : p.getVert 1 ∉ I.precolor.vertices)
    (hbP : p.getVert 2 ∉ I.precolor.vertices)
    (x y : V) (hx : ¬ OnOuterFace I.embedding I.outer x) (hy : ¬ OnOuterFace I.embedding I.outer y)
    (hbx : G.Adj (p.getVert 2) x) (hya : G.Adj y a)
    (hbad : ¬ ListColourable G I.lists)
    (hsmall : ∀ (W : Type u) [Finite W] (H : SimpleGraph W) (J : BoundaryInstance H C),
      Nat.card W < Nat.card V → ListColourable H J.lists)
    (u z : V) (hu : ¬ OnOuterFace I.embedding I.outer u) (hz : OnOuterFace I.embedding I.outer z)
    (hzA : z ∉ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V))
    (huN : ∃ w ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V), G.Adj u w)
    (hforbidden : (z ∉ I.precolor.vertices ∧ (I.lists z).card ≤ 2) ∨ z=s ∨ z=t) : ¬ G.Adj u z := by
  intro huz
  have hf : ∀ j, OnOuterFace I.embedding I.outer (p.getVert j) := fun j =>
    native_facial_cycle_vertices_on_outer I.embedding I.outer p hp hface hroot _ (p.getVert_mem_support j)
  have ha : OnOuterFace I.embedding I.outer a := by simpa only [Walk.getVert_zero] using hf 0
  have hsP : s ∈ I.precolor.vertices := by rw [hP]; exact List.mem_toFinset.2 r.start_mem_support
  have htP : t ∈ I.precolor.vertices := by rw [hP]; exact List.mem_toFinset.2 r.end_mem_support
  have hr2 : 2 ≤ r.length := by
    by_contra h
    exact (hbad (I.colourable_of_prescribed_edge r hr hn hP (by omega) hsmall)).elim
  have hTwo : ∀ w, OnOuterFace I.embedding I.outer w → w ∉ I.precolor.vertices → G.Adj u w →
      w ∈ ({a,p.getVert 1,p.getVert 2,x,y} : Finset V) → False := by
    intro w hw hwP huw hwA
    rcases hforbidden with ⟨hzP,_⟩ | hzs | hzt
    · have he := I.interior_unprescribed_neighbour_unique r hr hn hP hr2 hbad hsmall u w z hu hw hz hwP hzP huw huz
      exact hzA (he ▸ hwA)
    · exact I.no_interior_boundary_pair_at_initial_vertex r hr hn hP hrpos hbad hsmall
        u w hu hw (fun h => hwP (h ▸ hsP)) (hzs ▸ huz) huw
    · exact I.no_interior_boundary_pair_at_terminal_vertex r hr hn hP hrpos hbad hsmall
        u w hu hw (fun h => hwP (h ▸ htP)) (hzt ▸ huz) huw
  have hThree : ∀ b w, OnOuterFace I.embedding I.outer b → b ∉ I.precolor.vertices →
      ¬ OnOuterFace I.embedding I.outer w → G.Adj w b → G.Adj u w → False := by
    intro b w hb hbP hw hwb huw
    apply hbad
    rcases hforbidden with ⟨hzP,hzs⟩ | hzs | hzt
    · exact I.colourable_of_three_path_short_free_boundary_endpoint r hr hn hP hrpos
        b z w u hb hz hzP hzs hw hu hwb huw.symm huz hsmall
    · exact I.colourable_of_initial_prescribed_endpoint_three_path r hr hn hP hrpos
        b u w hb hbP hu hw (hzs ▸ huz) huw hwb hsmall
    · exact I.colourable_of_terminal_prescribed_endpoint_three_path r hr hn hP hrpos
        b u w hb hbP hu hw (hzt ▸ huz) huw hwb hsmall
  obtain ⟨w,hw,huw⟩ := huN
  simp only [Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with hwa | hwd | hwb | hwx | hwy
  · rw [hwa] at huw
    exact hTwo a ha haP huw (by simp)
  · rw [hwd] at huw
    exact hTwo _ (hf 1) hdP huw (by simp)
  · rw [hwb] at huw
    exact hTwo _ (hf 2) hbP huw (by simp)
  · rw [hwx] at huw
    exact hThree _ x (hf 2) hbP hx hbx.symm huw
  · rw [hwy] at huw
    exact hThree a y ha haP hy hya huw

end Thomassen.BoundaryInstance
