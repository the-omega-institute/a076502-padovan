#!/usr/bin/env python3
"""Export only base relations; Walnut reconstructs all quantified formulas."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from automata_proof import bits, constant, prefixed_zero_domain, at_least_two, difference_graph
from export_lean_certificates import read

ROOT = Path(__file__).resolve().parent


def export(dfa,path):
    # Walnut starts at the first listed state.
    order=[dfa.start]+[s for s in range(len(dfa.rows)) if s!=dfa.start]
    lines=[' '.join(['{0,1}']*len(dfa.names))]
    for s in order:
        lines+=['',f'{s} {int(s in dfa.final)}']
        for c,t in enumerate(dfa.rows[s]):
            if t>=0:
                lines.append(' '.join(map(str,bits(c,len(dfa.names))))+' -> '+str(t))
    path.write_text('\n'.join(lines)+'\n')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--java',required=True)
    p.add_argument('--jar',type=Path,required=True)
    args=p.parse_args()
    home=ROOT/'walnut'
    library=home/'Automata Library'
    library.mkdir(parents=True,exist_ok=True)
    for name,a in [('add',read('adder')),('B',read('candidate-graph')),
                   ('P',prefixed_zero_domain(('n',),3)),
                   ('P2',prefixed_zero_domain(('x','y'),3)),
                   ('One',constant('n',1)),('Zero',constant('n',0)),
                   ('GeTwo',at_least_two('n')),('D',difference_graph())]:
        export(a,library/(name+'.txt'))
    commands='''def Succ "E one $One(one) & $add(m,one,n)";
def PredB "E m $Succ(m,n) & $B(m,p)";
def H "E p $PredB(n,p) & $add(h,p,n)";
def BH "E h $H(h,n) & $B(h,v)";
def K "E v $BH(n,v) & $add(k,v,n)";
def BK "E k $K(k,n) & $B(k,w)";
def Good "E b,w $B(n,b) & $BK(n,w) & $add(b,w,n)";
def NextB "E np $Succ(n,np) & $B(np,bp)";
def DiffGood "E b,bp,d $B(n,b) & $NextB(bp,n) & $D(n,d) & $add(b,d,bp)";
eval adderTotality "A x,y ($P2(x,y) => (E z $add(x,y,z)))";
eval graphTotality "A n ($P(n) => (E b $B(n,b)))";
eval valueBound "A n ($P(n) => (E b,r $B(n,b) & $add(b,r,n)))";
eval positive "A n,b (($B(n,b) & $Zero(b)) => $Zero(n))";
eval recurrence "A n (($P(n) & $GeTwo(n)) => $Good(n))";
eval difference "A n ($P(n) => $DiffGood(n))";
exit;
'''
    commanddir=home/'Command Files'
    commanddir.mkdir(exist_ok=True)
    commandfile=commanddir/'check.txt'
    commandfile.write_text(commands)
    session=Path(tempfile.mkdtemp(prefix='run-',dir=home))
    proc=subprocess.run([args.java,'-jar',str(args.jar.resolve()),'--home-dir='+str(home),
                         '--session-dir='+str(session),'check.txt'],cwd=home,
                        text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (home/'run.log').write_text(proc.stdout)
    print(proc.stdout)
    checks={}
    for name in ['adderTotality','graphTotality','valueBound','positive','recurrence','difference']:
        candidates=list(session.rglob(name+'.txt'))
        contents=[p.read_text().strip() for p in candidates]
        checks[name]=any(c.lower()=='true' for c in contents)
    errors=any(token in proc.stdout for token in ['Exception','Undefined token','File does not exist'])
    report=dict(exit=proc.returncode,errors=errors,session=str(session.relative_to(ROOT)),
                jar_sha256=hashlib.sha256(args.jar.read_bytes()).hexdigest(),
                walnut_tag='v7.1.0',walnut_commit='67e69c248d07324b25de1d4a498e877ac504999a',checks=checks,
                scope='Base tables imported; all quantified formulas reconstructed by Walnut. Integer semantics rely on the mathematical carry invariant.')
    (ROOT/'automata-results'/'walnut.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    if proc.returncode or errors or not all(checks.values()):
        raise SystemExit(1)


if __name__=='__main__':
    main()
