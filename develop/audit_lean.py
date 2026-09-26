#!/usr/bin/env python3
"""Build the closed result module and record its source and axiom closure."""

import hashlib
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent / 'lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    subprocess.run([sys.executable, str(ROOT.parent / 'build_lean.py'), 'Main'], check=True)
    env = dict(os.environ)
    env['LEAN_PATH'] = str(ROOT) + os.pathsep + env.get('LEAN_PATH', '')
    proc = subprocess.run(['lean', '-R', str(ROOT), str(ROOT / 'Main.lean')],
                          env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / 'build-logs' / 'final-axioms.txt').write_text(proc.stdout)
    if proc.returncode or 'sorryAx' in proc.stdout or 'declaration uses `sorry`' in proc.stdout:
        raise RuntimeError(proc.stdout)
    closures = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", proc.stdout):
        axioms = [s.strip() for s in body.split(',') if s.strip()]
        if not set(axioms) <= ALLOWED:
            raise RuntimeError(f'Unexpected axioms in {name}: {axioms}')
        closures[name] = axioms
    if len(closures) < 18:
        raise RuntimeError('Missing final theorem axiom reports')
    modules = {}

    def visit(module):
        if module in modules:
            return
        source = ROOT / (module.replace('.', '/') + '.lean')
        body = source.read_text()
        if re.search(r'\b(sorry|admit|sorryAx|native_decide)\b|decide\s+\+native|^\s*axiom\s', body, re.M):
            raise RuntimeError(f'Forbidden proof shortcut in {module}')
        deps = re.findall(r'^import\s+(\S+)', body, re.M)
        local = [d for d in deps if (ROOT / (d.replace('.', '/') + '.lean')).exists()]
        output = source.with_suffix('.olean')
        if not output.exists() or output.stat().st_mtime < source.stat().st_mtime:
            raise RuntimeError(f'Missing or stale compiled output for {module}')
        modules[module] = dict(source=str(source.relative_to(ROOT)), sha256=digest(source),
                               olean_sha256=digest(output), local_imports=local)
        for dep in local:
            visit(dep)
            dep_output = ROOT / (dep.replace('.', '/') + '.olean')
            if output.stat().st_mtime < dep_output.stat().st_mtime:
                raise RuntimeError(f'Stale imported output for {module}: {dep}')

    visit('Main')
    version = subprocess.run(['lean', '--version'], check=True, text=True,
                             stdout=subprocess.PIPE).stdout.strip()
    report = dict(schema_version=1, status='passed',
                  checked_at_utc=datetime.now(timezone.utc).isoformat(), toolchain=version,
                  mathlib_revision='db584cd6d46c92f209a44c0f1c829460d327499d',
                  root_module='Main', module_count=len(modules),
                  build_context=os.environ.get('CLOITRE_BUILD_CONTEXT', 'local_incremental'),
                  source_shortcut_scan='passed', axiom_closures=closures,
                  modules=dict(sorted(modules.items())),
                  limitations=['The optimized Python suffix DP and K=200 decimal extrema '
                               'enclosures are separately computed, not asserted by this audit.',
                               'The original six-letter substitution identity remains open.',
                               'Dependency/toolchain provenance is recorded separately by '
                               'the clean-build runner. Rocq was not compiled.'])
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(status='passed', modules=len(modules),
                          audited_theorems=len(closures), allowed_axioms=sorted(ALLOWED))))


if __name__ == '__main__':
    main()
