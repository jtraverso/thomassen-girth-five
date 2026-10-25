#!/usr/bin/env python3
"""Replay the new invariant and CONDITIONAL assembly through Lean and NanoDa.

This is a kernel check of the exported declarations, not an independent
Challenge/Solution statement comparison and not a check of the main theorem.
"""
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
names = json.loads((root / "verification/assembly-declarations.json").read_text())
subprocess.run(["lake", "build", "Thomassen.Assembly", "--wfail"], cwd=root, check=True)
export = root / ".lake/assembly-support.ndjson"
with export.open("w") as out:
    subprocess.run(
        ["lake", "env", "leanexport", "Thomassen.Assembly", "--", *names],
        cwd=root, stdout=out, check=True,
    )
subprocess.run(["lake", "check", f"--from-export={export}"], cwd=root, check=True)
config = root / ".lake/assembly-nanoda.json"
config.write_text(json.dumps({
    "use_stdin": False,
    "export_file_path": str(export),
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": True,
    "num_threads": 4,
    "nat_extension": True,
    "string_extension": True,
}))
subprocess.run(["nanoda_bin", str(config)], cwd=root, check=True)
print("Lean and NanoDa accepted the invariant lemmas and conditional assembly.")
print("The full boundary-extension proof and unconditional main theorem are checked separately by comparator.json.")
