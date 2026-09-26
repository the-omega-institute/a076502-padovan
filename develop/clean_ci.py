#!/usr/bin/env python3
"""Rebuild the complete local Lean closure in an isolated, fresh Lake project."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

DEVELOP = Path(__file__).resolve().parent
LEAN = DEVELOP / 'lean'
MATHLIB_REV = 'db584cd6d46c92f209a44c0f1c829460d327499d'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(module='Main', found=None):
    found = {} if found is None else found
    if module in found:
        return found
    source = LEAN / (module.replace('.', '/') + '.lean')
    found[module] = source
    for dep in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
        if (LEAN / (dep.replace('.', '/') + '.lean')).exists():
            closure(dep, found)
    return found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=DEVELOP / 'ci-results')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='cloitre-clean-'))
    target = work / 'develop' / 'lean'
    target.mkdir(parents=True)
    sources = closure()
    hashes = {str(p.relative_to(LEAN)): digest(p) for p in sources.values()}
    for path in sources.values():
        dest = target / path.relative_to(LEAN)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
    for name in ['lakefile.toml', 'lean-toolchain']:
        shutil.copyfile(LEAN / name, target / name)
    for name in ['build_lean.py', 'audit_lean.py']:
        shutil.copyfile(DEVELOP / name, target.parent / name)
    assert not list(target.rglob('*.olean')) and not (target / '.lake').exists()
    env = dict(os.environ)
    for key in list(env):
        if key.startswith(('LEAN_', 'LAKE_', 'MATHLIB_CACHE_')):
            env.pop(key)
    env['MATHLIB_CACHE_DIR'] = str(work / 'mathlib-download-cache')
    env['CLOITRE_BUILD_CONTEXT'] = 'isolated_fresh_dependencies_and_local_modules'
    env['GIT_CONFIG_COUNT'] = '1'
    env['GIT_CONFIG_KEY_0'] = 'core.hooksPath'
    env['GIT_CONFIG_VALUE_0'] = '/dev/null'
    report = dict(schema_version=1, status='running',
                  started_at_utc=datetime.now(timezone.utc).isoformat(),
                  platform=platform.platform(), workspace=str(work),
                  source_hashes=hashes, local_modules=len(sources),
                  copied_local_oleans=0, reused_local_mathlib_checkout=False,
                  dependency_policy='Fresh git checkouts and fresh downloads of pinned Mathlib '
                  'binary cache; all collaboration modules compiled from source. '
                  'Mathlib itself and the Lean compiler are not bootstrapped from source.',
                  runner_files={n:digest(DEVELOP/n) for n in ['clean_ci.py','audit_lean.py','build_lean.py']},
                  steps=[])

    def persist():
        (args.output / 'clean-build.json').write_text(json.dumps(report, indent=2)+'\n')

    def run(name, cmd):
        report['current_step'] = name
        persist()
        print(f'{name}: starting (log: {args.output / (name+".log")})', flush=True)
        start = time.monotonic()
        with (args.output / (name+'.log')).open('w') as log:
            proc = subprocess.run(cmd, cwd=target, env=env, stdout=log, stderr=subprocess.STDOUT)
        report['steps'].append(dict(name=name, command=cmd, exit=proc.returncode,
                                    seconds=round(time.monotonic()-start,3)))
        persist()
        if proc.returncode:
            raise RuntimeError(f'{name} failed; see {args.output / (name+".log")}')
        print(f'{name}: passed', flush=True)

    try:
        run('toolchain', ['lean','--version'])
        run('dependencies', ['lake','update'])
        manifest = json.loads((target / 'lake-manifest.json').read_text())
        mathlib = next(p for p in manifest['packages'] if p['name']=='mathlib')
        if mathlib['rev'] != MATHLIB_REV:
            raise RuntimeError('Unexpected Mathlib revision')
        report['resolved_dependencies'] = {p['name']:p['rev'] for p in manifest['packages']}
        shutil.copyfile(target / 'lake-manifest.json', args.output / 'lake-manifest.json')
        run('dependency-cache', ['lake','exe','cache','get'])
        if list(target.glob('*.olean')) or list((target/'Generated').glob('*.olean')):
            raise RuntimeError('Local proof outputs appeared before clean build')
        run('proof-audit', ['lake','env',sys.executable,'../audit_lean.py'])
        verified = json.loads((target/'verification.json').read_text())
        actual = {m['source']:m['sha256'] for m in verified['modules'].values()}
        if actual != hashes:
            raise RuntimeError('Verified source closure differs from copied closure')
        rebuilt = json.loads((target/'build-logs/latest-build.json').read_text())
        if len(rebuilt)!=len(sources) or any(m['exit']!=0 for m in rebuilt):
            raise RuntimeError('Not every local proof module was rebuilt')
        if any(digest(LEAN / name)!=value for name,value in hashes.items()):
            raise RuntimeError('Original proof sources changed during build')
        shutil.copyfile(target/'verification.json',args.output/'verification.json')
        shutil.copytree(target/'build-logs',args.output/'build-logs',dirs_exist_ok=True)
        report.update(status='passed',rebuilt_modules=len(rebuilt),
                      audited_theorems=len(verified['axiom_closures']),
                      hosted_ci_run=os.environ.get('GITHUB_ACTIONS')=='true')
    except Exception as exc:
        report.update(status='failed',error=str(exc))
        raise
    finally:
        report['finished_at_utc']=datetime.now(timezone.utc).isoformat()
        persist()
    print(json.dumps({k:report[k] for k in ['status','rebuilt_modules','audited_theorems','workspace']}))


if __name__=='__main__':
    main()
