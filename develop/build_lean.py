#!/usr/bin/env python3
"""Run inside `lake env` using the project's pinned Lean/Mathlib environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent / 'lean'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    env = dict(os.environ)
    env['LEAN_PATH'] = str(ROOT) + os.pathsep + env.get('LEAN_PATH', '')
    checked = {}
    report = []
    logdir = ROOT / 'build-logs'
    logdir.mkdir(exist_ok=True)

    def build(module):
        if module in checked:
            return checked[module]
        source = ROOT / (module.replace('.', '/') + '.lean')
        body = source.read_text()
        dependencies = [s for s in re.findall(r'^import\s+(\S+)',body,re.M)
                        if (ROOT / (s.replace('.', '/')+'.lean')).exists()]
        for dep in dependencies:
            build(dep)
        output = source.with_suffix('.olean')
        latest = max([source.stat().st_mtime] + [checked[d] for d in dependencies])
        if output.exists() and output.stat().st_mtime >= latest:
            checked[module] = output.stat().st_mtime
            return checked[module]
        start = time.monotonic()
        proc = subprocess.run(['lean','-R',str(ROOT),'-o',str(output),str(source)],
                              env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logdir / (module+'.txt')).write_text(proc.stdout)
        item = dict(module=module,exit=proc.returncode,seconds=round(time.monotonic()-start,3),
                    sha256=hashlib.sha256(source.read_bytes()).hexdigest())
        report.append(item)
        print(json.dumps(item),flush=True)
        if proc.returncode or 'declaration uses `sorry`' in proc.stdout:
            output.unlink(missing_ok=True)
            print(proc.stdout,flush=True)
            sys.exit(1)
        checked[module] = output.stat().st_mtime
        return checked[module]

    for module in args.modules:
        build(module)
    (logdir/'latest-build.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
