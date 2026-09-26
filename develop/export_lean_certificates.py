#!/usr/bin/env python3
"""Export finite tables and invariant witnesses for Lean kernel checking.

Generation is untrusted: the emitted propositions are proved by kernel
reduction, and the generic theorem connects them to all input lengths.
"""

from collections import deque
import json
from pathlib import Path
from automata_proof import DFA, project, prefixed_zero_domain, intersect, greedy, reachable

ROOT = Path(__file__).parent


def read(name):
    data = json.loads((ROOT / 'automata-results' / (name+'.json')).read_text())
    return DFA(tuple(data['names']), data['rows'], set(data['final']), data['start'])


def total(dfa):
    sink = len(dfa.rows)
    return [[x if x >= 0 else sink for x in row] for row in dfa.rows] + [[sink]*dfa.width]


def invariant(a, b):
    ar,br=total(a),total(b)
    pairs=[(a.start,b.start)];seen=set(pairs)
    for q,s in pairs:
        assert q not in a.final or s in b.final
        for u,v in zip(ar[q],br[s]):
            if (u,v) not in seen:
                seen.add((u,v));pairs.append((u,v))
    return pairs


def lookup(values):
    if len(values)==1:
        return '(.leaf '+str(values[0])+')'
    if len(values)%2:
        values=values+[values[-1]]
    return '(.node '+lookup(values[::2])+' '+lookup(values[1::2])+')'


def table(name, dfa):
    rows = total(dfa)
    data = '#['+','.join('#['+','.join(map(str,row))+']' for row in rows)+']'
    final = '#['+','.join('true' if i in dfa.final else 'false' for i in range(len(rows)))+']'
    return f'''def {name}Rows : Array (Array Nat) := {data}
def {name}Final : Array Bool := {final}
def {name}Transitions : Lookup Nat := {lookup([v for row in rows for v in row])}
def {name}Acceptance : Lookup Bool := {lookup(['true' if i in dfa.final else 'false' for i in range(len(rows))])}
def {name} : Machine {dfa.width} {len(rows)} where
  start := ⟨{dfa.start}, by decide⟩
  step q c := Fin.ofNat {len(rows)} ({name}Transitions.get (q.val * {dfa.width} + c.val))
  accept q := {name}Acceptance.get q.val
'''


def emit():
    add,graph=read('adder'),read('candidate-graph')
    g=prefixed_zero_domain(('n',),3)
    # Saturated value class: zero, the final singleton 1, or value >=2.
    threshold,_=reachable(('n',),0,lambda v,b:min(2,2*v+b[0]),lambda v:v==2)
    g2=intersect(g,threshold)
    checks=[('adderTotality',prefixed_zero_domain(('x','y'),3),project(add,('x','y'))),
            ('graphTotality',g,project(graph,('n',))),
            ('candidateBound',g,read('bounded')),
            ('recurrenceLanguage',g2,read('recurrence')),
            ('differenceLanguage',g,read('first_difference'))]
    lines=['import AutomataCertificate','set_option maxRecDepth 1000000',
           'set_option maxHeartbeats 0','namespace CloitreCollaboration.Certificate.Concrete']
    sizes=[]
    for name,a,b in checks:
        pairs=invariant(a,b)
        lines.extend([table(name+'Left',a),table(name+'Right',b)])
        literals=', '.join(f'(⟨{q}, by decide⟩, ⟨{s}, by decide⟩)' for q,s in pairs)
        lines.append(f'def {name}Pairs : List (Fin {len(a.rows)+1} × Fin {len(b.rows)+1}) := [{literals}]')
        lines.append(f'theorem {name}Certificate : Valid {name}Left {name}Right {name}Pairs := by decide')
        lines.append(f'theorem {name}AllWords (w) : accepts {name}Left w → accepts {name}Right w :=\n  valid_implies_inclusion _ _ _ {name}Certificate w')
        lines.append(f'#print axioms {name}AllWords')
        sizes.append({'name':name,'left_states':len(a.rows)+1,'right_states':len(b.rows)+1,'invariant_pairs':len(pairs)})
    lines.append('end CloitreCollaboration.Certificate.Concrete')
    out=ROOT/'lean'/'ConcreteCertificates.lean'
    out.write_text('\n\n'.join(lines)+'\n')
    print(json.dumps({'file':str(out),'bytes':out.stat().st_size,'checks':sizes},indent=2))


if __name__=='__main__':
    emit()
