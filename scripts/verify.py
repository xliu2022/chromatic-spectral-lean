#!/usr/bin/env python3
"""Build and audit the formalization using the pinned Lean environment."""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def lean_code(text: str) -> str:
    """Remove nested block comments, line comments and string contents."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            in_string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake', help='Lake executable (default: lake)')
    parser.add_argument('--comparator', action='store_true',
                        help='Also run Lake Comparator and NanoDa (requires Linux and bubblewrap)')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    logs = root / 'verification'
    logs.mkdir(exist_ok=True)
    sources = sorted(p for p in root.rglob('*.lean') if '.lake' not in p.parts and '.git' not in p.parts)
    forbidden = re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|Lean\.ofReduceBool')
    config = json.loads((root / 'comparator.json').read_text(encoding='utf-8'))
    expected = set(config['theorem_names'])
    challenge = root / (config['challenge_module'].replace('.', '/') + '.lean')
    # The Challenge uses one namespace for its six public statements. Only a
    # listed theorem with a standalone placeholder proof gets this exception.
    names = '|'.join(re.escape(name.removeprefix('ChromaticSpectral.')) for name in expected)
    challenge_proof = re.compile(
        rf'(^theorem (?:{names})\b.*(?:\n[ \t].*)*? := by\n[ \t]+)sorry[ \t]*$',
        re.MULTILINE,
    )
    issues = []
    for path in sources:
        text = path.read_text(encoding='utf-8')
        code = lean_code(text)
        if not code.lstrip().startswith('module\n'):
            issues.append(f'{path.relative_to(root)}: missing module header')
        if path == challenge:
            code = challenge_proof.sub(r'\1', code)
        for match in forbidden.finditer(code):
            line = code.count('\n', 0, match.start()) + 1
            issues.append(f'{path.relative_to(root)}:{line}: forbidden proof token {match.group()}')
    if issues:
        print('\n'.join(issues), file=sys.stderr)
        return 1
    print(f'Source scan passed: {len(sources)} Lean files.', flush=True)

    commands = [
        ([args.lake, 'build'], 'build.log'),
        ([args.lake, 'env', 'lean', 'Audit.lean'], 'axioms.log'),
        ([args.lake, 'env', 'lean', 'Examples.lean'], 'examples.log'),
        ([args.lake, 'env', 'lean', '--version'], 'lean-version.log'),
    ]
    if args.comparator:
        commands.append(([args.lake, 'comparator', '--config', 'comparator.json'], 'comparator.log'))
    for command, log in commands:
        print('Running: ' + ' '.join(command), flush=True)
        result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / log).write_text(result.stdout, encoding='utf-8')
        if result.returncode:
            print(result.stdout[-16000:], file=sys.stderr)
            return result.returncode
        print(f'Passed; log: verification/{log}', flush=True)

    output = (logs / 'axioms.log').read_text(encoding='utf-8')
    allowed = set(config['permitted_axioms'])
    if not allowed <= {'propext', 'Classical.choice', 'Quot.sound'}:
        print('Comparator configuration allows an unexpected axiom.', file=sys.stderr)
        return 1
    audited = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output, flags=re.S):
        axioms = {item.strip() for item in raw.split(',') if item.strip()}
        if not axioms <= allowed:
            print(f'Unexpected axiom dependencies in {name}: {sorted(axioms - allowed)}', file=sys.stderr)
            return 1
        audited[name] = sorted(axioms)
    if set(audited) != expected:
        print(f'Audit target mismatch: found {sorted(audited)}, expected {sorted(expected)}', file=sys.stderr)
        return 1

    manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    summary = {
        'status': 'passed',
        'verified_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
        'mathlib_commit': mathlib['rev'],
        'lean_source_files': len(sources),
        'lean_source_lines': sum(len(p.read_text(encoding='utf-8').splitlines()) for p in sources),
        'axiom_audit': audited,
        'comparator': 'passed' if args.comparator else 'not run by this command',
        'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    }
    (logs / 'summary.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(f'Verification passed: {len(expected)} final declarations, only standard Lean axioms.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
