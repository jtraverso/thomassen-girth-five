#!/usr/bin/env python3
"""Audit source layout, immutable contracts, reuse and the registry surface.

This is a reproducible packaging audit, not a replacement for kernel checks
or the official Palomar sandboxed mechanical preflight.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parent.parent

def digest(path):
    return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()

def read(path):
    return json.loads((ROOT/path).read_text())

def without_comments(source):
    out=[];i=0;depth=0
    while i<len(source):
        pair=source[i:i+2]
        if pair=='/-':depth+=1;i+=2
        elif depth and pair=='-/':depth-=1;i+=2
        elif not depth and pair=='--':
            j=source.find('\n',i);i=len(source) if j<0 else j
        else:
            if not depth:out.append(source[i])
            i+=1
    assert depth==0,'Unclosed block comment'
    return ''.join(out)

baseline=read('verification/freeze-baseline-hashes.json')
for path,expected in baseline['unchanged_original_contracts'].items():
    assert digest(path)==expected,f'Original contract changed: {path}'
reuse=read('verification/source-reuse.json')
for entry in reuse['files']:
    assert digest(entry['path'])==entry['current_sha256'],f'Reused file changed: {entry["path"]}'
metadata=read('verification/freeze-metadata-audit.json')
assert metadata['passed'] and digest(metadata['metadata'])==metadata['metadata_sha256'],'Metadata needs revalidation'
config=read('comparator.registry.json')
assert config['solution_module']=='ThomassenSolution'
assert config['challenge_module']=='ThomassenRegistryChallenge'
assert config['enable_nanoda'] is True
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert len(config['theorem_names'])==15 and len(set(config['theorem_names']))==15
assert len(config['definition_names'])==10 and len(set(config['definition_names']))==10
wanted=set(read('comparator.json')['theorem_names']+read('comparator.original-full.json')['theorem_names']+
    ['Thomassen.original_corollary_2_2']+read('comparator.byproducts.json')['theorem_names'])
assert set(config['theorem_names'])==wanted,'Registry statement omitted or added unexpectedly'
assert set(config['definition_names'])==set(read('comparator.json')['definition_names']+['Thomassen.ComponentOuterBoundary'])
closure=set()
def visit(module):
    path=module.replace('.','/')+'.lean'
    if path in closure or not (ROOT/path).is_file():return
    closure.add(path)
    source=without_comments((ROOT/path).read_text())
    for imported in re.findall(r'(?m)^(?:(?:public|private)\s+)?import\s+([\w.]+)',source):visit(imported)
visit(config['challenge_module'])
proof_modules=['ThomassenSolution.lean','Thomassen/BoundaryExtension.lean','Thomassen/OriginalTheorem.lean',
    'Thomassen/OriginalClosure.lean','Thomassen/OriginalCorollary.lean','Thomassen/PublicBoundaryGlobal.lean',
    'Thomassen/InfiniteChoosability.lean','Thomassen/ArbitraryShortCycle.lean','Thomassen/OuterSevenCycle.lean']
assert not set(proof_modules)&closure,'Selected solution module imported by the challenge'
source_paths=set(subprocess.check_output(['git','ls-files'],cwd=ROOT,text=True).splitlines())
source_paths.update(p.relative_to(ROOT).as_posix() for p in ROOT.glob('*.lean'))
lean=[];largest=('',0);violations=[]
for path in sorted(p for p in source_paths if p.endswith('.lean')):
    p=ROOT/path
    assert not p.is_symlink(),f'Source symlink: {path}'
    source=p.read_text(encoding='utf-8');lines=len(source.splitlines())
    assert lines<=10000,f'Source line limit: {path}'
    assert re.match(r'^\s*module(?:\s|$)',without_comments(source)),f'Missing module header: {path}'
    if lines>largest[1]:largest=(path,lines)
    lean.append({'path':path,'sha256':digest(path),'lines':lines})
    if path.startswith(('Thomassen/','LeanPool/','Grotzsch/')) or path in ['Solution.lean','ThomassenSolution.lean']:
        for token in re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b',without_comments(source)):
            violations.append({'path':path,'token':token})
assert not violations,violations
for package in read('lake-manifest.json')['packages']:
    assert package['type']=='git' and re.fullmatch('[a-f0-9]{40}',package['rev']),package['name']
    assert package['url'].startswith('https://github.com/'),package['name']
assert not [p for p in source_paths if re.search(r'\.(?:olean|ilean|a|so|dylib|dll|exe)$',p)],'Prebuilt output tracked'
assert not [p for p in source_paths if p.startswith('.lake/')],'Lake cache tracked'
assert not [p for p in ROOT.iterdir() if p.is_file() and p.name.lower() in {'licence','copying','unlicense','ofl'}],'Multiple root licences'
assert (ROOT/'LICENSE').read_text().startswith('                                 Apache License')
report={'passed':True,'scope':'Local freeze packaging audit; official Palomar verification remains separate',
    'registry_theorems':15,'registry_definitions':10,'permitted_axioms':config['permitted_axioms'],
    'registry_challenge_sha256':digest('ThomassenRegistryChallenge.lean'),
    'registry_comparator_sha256':digest('comparator.registry.json'),
    'original_contracts_preserved':baseline,'reused_source_files_unchanged':len(reuse['files']),
    'selected_proof_modules_absent_from_challenge_closure':proof_modules,
    'challenge_local_source_closure':sorted(closure),'solution_forbidden_constructs':violations,
    'lean_sources':lean,'lean_source_count':len(lean),'largest_lean_file':{'path':largest[0],'lines':largest[1]},
    'metadata_audit':'verification/freeze-metadata-audit.json','pinned_git_dependencies':len(read('lake-manifest.json')['packages'])}
(ROOT/'verification/freeze-source-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'Freeze source audit passed: {len(lean)} Lean files, {len(reuse["files"])} reused hashes, 15 theorems, 10 definitions; original contracts preserved.')
