#!/usr/bin/env python3
"""Audit solution sources; independent challenge placeholders are out of scope."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent


def without_comments(source):
    result = []
    index = 0
    depth = 0
    while index < len(source):
        token = source[index:index + 2]
        if token == '/-':
            depth += 1
            index += 2
        elif depth and token == '-/':
            depth -= 1
            index += 2
        elif not depth and token == '--':
            end = source.find('\n', index)
            index = len(source) if end < 0 else end
        else:
            if not depth:
                result.append(source[index])
            index += 1
    if depth:
        raise ValueError('Unclosed block comment in audited source')
    return ''.join(result)


paths = sorted((ROOT / 'Thomassen').glob('*.lean')) + [ROOT / 'ThomassenSolution.lean']
violations = []
sources = []
for path in paths:
    raw = path.read_bytes()
    relative = str(path.relative_to(ROOT))
    sources.append({'path': relative, 'sha256': hashlib.sha256(raw).hexdigest()})
    for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b', without_comments(raw.decode())):
        violations.append({'path': relative, 'token': match.group()})

report = {
    'scope': 'Thomassen/*.lean and ThomassenSolution.lean',
    'solution_module_count': len(paths),
    'excluded': 'Independent challenge modules intentionally contain theorem placeholders.',
    'forbidden_tokens': ['sorry', 'admit', 'axiom', 'native_decide'],
    'sources': sources,
    'violations': violations,
    'passed': not violations,
}
(ROOT / 'verification/source-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'Source audit: {len(paths)} solution modules; {len(violations)} forbidden constructs.')
if violations:
    raise SystemExit(1)
