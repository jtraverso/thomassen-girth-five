#!/usr/bin/env python3
"""Generate the small standalone public contract, retaining original contracts.

The two componentwise results use a proved-equivalent ambient face certificate.
All original solution statements, definitions and proof bodies are preserved.
"""
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
header='''/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic

/-! Standalone public contract. The registered planarity/list definitions and
native cycle/face definitions are reproduced with their source attribution.
The two componentwise results use AmbientComponentOuterBoundary, proved
exactly equivalent to the original induced-map certificate in RegistryBoundary.
No selected solution proof is imported, reproduced or assumed. -/
@[expose] public section
'''
legacy=(root/'Challenge.lean').read_text()
main=legacy[legacy.index('noncomputable section'):legacy.index('/-! ### Sanity checks')]
main+=legacy[legacy.index('section Colouring'):legacy.index('end Colouring')+len('end Colouring')]
main+='\nend PlanarChoosability\nend\n'
core='''
/- Definitions reproduced from the pinned planar-list-colouring library:
Basic.lean; Reach.lean; Planar/{Orbits,Hypermap,Embedding}.lean. -/
section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V C : Type*}
def ListColourable (G : SimpleGraph V) (L : V → Finset C) : Prop :=
  ∃ c : G.Coloring C, ∀ v, c v ∈ L v
def ChoosableWith (G : SimpleGraph V) (C : Type*) (k : ℕ) : Prop :=
  ∀ L : V → Finset C, (∀ v, k ≤ (L v).card) → ListColourable G L
end LeanPool.K5MinorFreeChoosability
end
section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
noncomputable def numClasses (s : Setoid α) : ℕ := Nat.card (Quotient s)
noncomputable def cycleCount (π : Perm α) : ℕ := numClasses (SameCycle.setoid π)
end LeanPool.K5MinorFreeChoosability
end
section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
-- Name the ordinary checked proof explicitly to preserve the original
-- module-local auxiliary proof name when the two namespaces share a file.
theorem compSetoid._proof_1 (σ α : Perm D) :
    Equivalence (Relation.EqvGen (fun a b : D => b = σ a ∨ b = α a)) :=
  Relation.EqvGen.is_equivalence _
def compSetoid (σ α : Perm D) : Setoid D where
  r := Relation.EqvGen (fun a b => b = σ a ∨ b = α a)
  iseqv := compSetoid._proof_1 σ α
noncomputable def numComponents (σ α : Perm D) : ℕ := numClasses (compSetoid σ α)
noncomputable def eulerDefect (σ α : Perm D) : ℤ :=
  (Nat.card D : ℤ) + 2 * (numComponents σ α : ℤ) - cycleCount σ - cycleCount α -
    cycleCount (σ * α)
end LeanPool.K5MinorFreeChoosability
end
section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
def dartSymm : Perm G.Dart := Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive
structure IsRotationSystem (σ : Perm G.Dart) : Prop where
  fst_apply : ∀ d, (σ d).fst = d.fst
  sameCycle : ∀ d e : G.Dart, d.fst = e.fst → σ.SameCycle d e
structure PlaneMap where
  rot : Perm G.Dart
  isRotationSystem : IsRotationSystem G rot
  eulerDefect_eq_zero : eulerDefect rot (dartSymm G) = 0
def IsPlanar : Prop := Nonempty (PlaneMap G)
namespace PlaneMap
variable {G} (M : PlaneMap G)
def facePerm : Perm G.Dart := M.rot * dartSymm G
end PlaneMap
end LeanPool.K5MinorFreeChoosability
end
section
namespace LeanPool.K5MinorFreeChoosability
variable {W : Type*}
def RIn (G : SimpleGraph W) (s : Set W) : W → W → Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)
def ConnSet (G : SimpleGraph W) (s : Set W) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, RIn G s a b
end LeanPool.K5MinorFreeChoosability
end
/- Native cycle definitions: Grotzsch/FacialCycle.lean in the pinned source. -/
section
namespace Grotzsch
variable {V : Type*} {G : SimpleGraph V}
structure IsCycleMap (G : SimpleGraph V) {k : ℕ} (c : ZMod k → V) : Prop where
  inj : Function.Injective c
  adj : ∀ i, G.Adj (c i) (c (i + 1))
def IsChordless (G : SimpleGraph V) {k : ℕ} (c : ZMod k → V) : Prop :=
  ∀ i j, G.Adj (c i) (c j) → j = i + 1 ∨ i = j + 1
end Grotzsch
end
section
open LeanPool.K5MinorFreeChoosability
universe u
namespace Thomassen
variable {V : Type u} {G : SimpleGraph V}
def OnOuterFace (M : PlaneMap G) (outer : G.Dart) (x : V) : Prop :=
  ∃ e : G.Dart, Equiv.Perm.SameCycle M.facePerm outer e ∧ e.fst = x
variable [Fintype V]
/-- Same actual ambient face orbit for the marked vertices of each component.
Isolated vertices require no dart. Equivalent to ComponentOuterBoundary. -/
def AmbientComponentOuterBoundary (M : PlaneMap G) (B : Set V) : Prop :=
  ∀ K : G.ConnectedComponent, Nonempty K.toSimpleGraph.Dart →
    ∃ outer : G.Dart, outer.fst ∈ K.supp ∧
      ∀ x : K, x.1 ∈ B → OnOuterFace M outer x.1
end Thomassen
end
'''
b=(root/'ThomassenByproductsChallenge.lean').read_text();b=b[b.index('@[expose] public section'):]
b=b.replace('dvorak_kawarabayashi_theorem_1_global','dvorak_kawarabayashi_theorem_1_on_component_faces').replace('ComponentOuterBoundary M B','AmbientComponentOuterBoundary M B')
f=(root/'ThomassenOriginalFullChallenge.lean').read_text();f=f[f.index('/-- Thomassen (1995), Theorem 2.1'):f.rindex('end Thomassen')]
f=f.replace('theorem original_theorem_2_1','theorem original_theorem_2_1_on_component_faces').replace('ComponentOuterBoundary M B','AmbientComponentOuterBoundary M B')
p=(root/'ThomassenOriginalPaperChallenge.lean').read_text();c=p[p.index('theorem original_corollary_2_2'):p.index('end Thomassen\nend',p.index('theorem original_corollary_2_2'))]
m=(root/'ThomassenMainChallenge.lean').read_text();m=m[m.index('/-- Thomassen (1995):'):m.rindex('end PlanarChoosability')]
text=header+main+core+b+'\nnamespace PlanarChoosability\n'+m+'end PlanarChoosability\n\nnamespace Thomassen\nsection\nvariable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]\n'+f+'end\nsection\nvariable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]\n'+c+'end\nend Thomassen\n'
assert len(text.encode())<=100*1024
(root/'ThomassenRegistryChallenge.lean').write_text(text)
mainconfig=json.loads((root/'comparator.json').read_text());bp=json.loads((root/'comparator.byproducts.json').read_text())
names=mainconfig['theorem_names']+['Thomassen.original_theorem_2_1_on_component_faces','Thomassen.original_corollary_2_2']+[s.replace('dvorak_kawarabayashi_theorem_1_global','dvorak_kawarabayashi_theorem_1_on_component_faces') for s in bp['theorem_names']]
config={**mainconfig,'challenge_module':'ThomassenRegistryChallenge','theorem_names':names,'definition_names':mainconfig['definition_names']+['Thomassen.AmbientComponentOuterBoundary']}
(root/'comparator.registry.json').write_text(json.dumps(config,indent=2)+'\n')
(root/'verification/registry-contract-source-map.json').write_text(json.dumps({'standalone':True,'generator':'scripts/prepare-registry-contract.py','bytes':len(text.encode()),'hard_cap_bytes':102400,'lines':len(text.splitlines()),'trusted_imports':['Mathlib.Combinatorics.SimpleGraph.Girth','Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex','Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected','Mathlib.GroupTheory.Perm.Cycle.Basic','Mathlib.Data.Fintype.Card','Mathlib.Data.ZMod.Basic'],'reproduced_definitions_sources':['Challenge.lean','LeanPool/K5MinorFreeChoosability/Basic.lean','LeanPool/K5MinorFreeChoosability/Reach.lean','LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean','LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean','LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean','Grotzsch/FacialCycle.lean','Thomassen/Instance.lean','Thomassen/RegistryBoundary.lean'],'selected_solution_proof_modules_reproduced':False,'boundary_equivalence':'Thomassen.ambientComponentOuterBoundary_iff','boundary_equivalence_proof':'Thomassen/RegistryBoundary.lean','public_presentation_changes':{'Thomassen.original_theorem_2_1':'Thomassen.original_theorem_2_1_on_component_faces','Thomassen.dvorak_kawarabayashi_theorem_1_global':'Thomassen.dvorak_kawarabayashi_theorem_1_on_component_faces'},'original_individual_contracts_unchanged':True},indent=2)+'\n')
print(f'Compact standalone contract: {len(text.encode())} bytes, {len(text.splitlines())} lines, 15 statements and 10 definitions.')
