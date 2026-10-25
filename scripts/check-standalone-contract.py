#!/usr/bin/env python3
"""Compile the public contract using only pinned dependency build output.

No candidate project .olean is on LEAN_PATH. This catches imports accepted by
ordinary local Lake builds but unavailable to Palomar's protected contract.
"""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import tempfile

root=Path(__file__).resolve().parent.parent
source=root/'ThomassenRegistryChallenge.lean'
imports=re.findall(r'(?m)^(?:(?:public|private)\s+)?import\s+([\w.]+)',source.read_text())
assert imports and all(x.startswith('Mathlib.') for x in imports),imports
assert source.stat().st_size<=102400,'Contract exceeds the official 100 KiB hard cap'
manifest=json.loads((root/'lake-manifest.json').read_text())
paths=[root/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in manifest['packages']]
paths=[p for p in paths if p.is_dir()]
assert paths and (root/'.lake/packages/mathlib/.lake/build/lib/lean').is_dir(),'Install pinned Mathlib and its dependency cache first'
lean=shutil.which('lean')
assert lean,'Lean is unavailable'
env=dict(os.environ)
env['ELAN_TOOLCHAIN']=(root/'lean-toolchain').read_text().strip()
env['LEAN_PATH']=os.pathsep.join(map(str,paths))
with tempfile.TemporaryDirectory(prefix='thomassen-contract-') as temp:
    copy=Path(temp)/'ThomassenRegistryChallenge.lean'
    copy.write_bytes(source.read_bytes())
    command=[lean,'-o',str(Path(temp)/'ThomassenRegistryChallenge.olean'),str(copy)]
    subprocess.run(command,cwd=temp,env=env,check=True)
print('Standalone contract accepted with only pinned dependency output; no project build output on LEAN_PATH.')
