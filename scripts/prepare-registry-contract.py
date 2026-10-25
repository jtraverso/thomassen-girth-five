#!/usr/bin/env python3
"""Assemble the public registry contract from the frozen independent contracts.

The original contracts/configurations are retained byte for byte. Only public
statements and the already independently compared boundary definition are used.
"""
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
b=(root/'ThomassenByproductsChallenge.lean').read_text()
b=b[b.index('@[expose] public section'):]
b=b.replace('universe u v\n','')
f=(root/'ThomassenOriginalFullChallenge.lean').read_text()
f=f[f.index('/-- Thomassen (1995), Theorem 2.1'):f.rindex('end Thomassen')]
p=(root/'ThomassenOriginalPaperChallenge.lean').read_text()
c=p[p.index('theorem original_corollary_2_2'):p.index('end Thomassen\nend',p.index('theorem original_corollary_2_2'))]
m=(root/'ThomassenMainChallenge.lean').read_text()
m=m[m.index('/-- Thomassen (1995):'):m.rindex('end PlanarChoosability')]
d=p[p.index('def ComponentOuterBoundary'):p.index('end Thomassen',p.index('def ComponentOuterBoundary'))]
header='''/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Challenge
public import Thomassen.CycleWalk
public import Thomassen.InducedInstance

/-! Public registry contract. Statements are reproduced from the existing
independent main, full-original, corollary and byproduct contracts. No selected
solution proof module is imported. Intentional placeholders occur only here;
the solution supplies and kernel-checks their proof bodies. -/
universe u v
@[expose] public section
open LeanPool.K5MinorFreeChoosability Grotzsch SimpleGraph
namespace Thomassen
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
'''
body=header+d+'end Thomassen\n\n'+b+'\nnamespace PlanarChoosability\n'+m+'end PlanarChoosability\n\nnamespace Thomassen\nsection\nvariable {V : Type u} {C : Type v} {G : SimpleGraph V} [Fintype V]\n'+f+'end\n\nsection\nvariable {V : Type u} {C : Type v} {G : SimpleGraph V} [Finite V]\n'+c+'end\nend Thomassen\n'
(root/'ThomassenRegistryChallenge.lean').write_text(body)
main=json.loads((root/'comparator.json').read_text())
bp=json.loads((root/'comparator.byproducts.json').read_text())
config={**main,'challenge_module':'ThomassenRegistryChallenge','theorem_names':main['theorem_names']+['Thomassen.original_theorem_2_1','Thomassen.original_corollary_2_2']+bp['theorem_names'],'definition_names':main['definition_names']+['Thomassen.ComponentOuterBoundary']}
(root/'comparator.registry.json').write_text(json.dumps(config,indent=2)+'\n')
print(f'Registry contract: {len(config["theorem_names"])} theorem statements, {len(config["definition_names"])} definitions.')
