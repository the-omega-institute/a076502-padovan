#!/usr/bin/env python3
"""Emit proof-carrying projections/products. Lean checks every emitted witness."""

import json
from itertools import product
from pathlib import Path
from automata_proof import DFA, bits, encode, reachable, minimize, rename, constant, difference_graph
from export_lean_certificates import read, total, invariant, table, lookup

ROOT = Path(__file__).parent
OUT = ROOT / 'lean' / 'Generated'
OUT.mkdir(exist_ok=True)
REGISTRY = {}
REPORT = []


def fin(n):
    return f'⟨{n}, by decide⟩'


def begin(name, imports):
    return [*(f'import {i}' for i in sorted(set(imports))),
            'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0',
            'namespace CloitreCollaboration.Certificate.Operations']


def finish(name, lines):
    lines.append('end CloitreCollaboration.Certificate.Operations')
    path=OUT / (name + '.lean')
    body='\n\n'.join(lines) + '\n'
    if not path.exists() or path.read_text()!=body:
        path.write_text(body)


def base(name, dfa):
    lines = begin(name, ['AutomataCertificate'])
    lines.append(table(name, dfa))
    finish(name, lines)
    REGISTRY[name] = dfa
    return name


def include(lines, label, a_name, a, b_name, b):
    pairs = invariant(a, b)
    ids={pair:i for i,pair in enumerate(pairs)}
    ar,br=total(a),total(b)
    edges=[[ids[(ar[q][c],br[s][c])] for c in range(a.width)] for q,s in pairs]
    value = ','.join(f'({fin(q)},{fin(s)})' for q, s in pairs)
    lines.append(f'def {label}Pairs : Array (Fin {len(a.rows)+1} × Fin {len(b.rows)+1}) := #[{value}]')
    leaves=[f'({fin(q)},{fin(s)})' for q,s in pairs]
    lines.append(f'def {label}Nodes : Lookup (Fin {len(a.rows)+1} × Fin {len(b.rows)+1}) := {lookup(leaves)}')
    lines.append(f'def {label}Node (q : Fin {len(pairs)}) := {label}Nodes.get q.val')
    value=','.join('#['+','.join(map(str,row))+']' for row in edges)
    lines.append(f'def {label}Edges : Array (Array Nat) := #[{value}]')
    lines.append(f'def {label}EdgeTree : Lookup Nat := {lookup([x for row in edges for x in row])}')
    lines.append(f'def {label}Edge (q : Fin {len(pairs)}) (c : Fin {a.width}) : Fin {len(pairs)} := Fin.ofNat {len(pairs)} ({label}EdgeTree.get (q.val*{a.width}+c.val))')
    lines.append(f'theorem {label}Valid : CoverValid {a_name} {b_name} {label}Node 0 {label}Edge := by decide +kernel')
    lines.append(f'theorem {label} (w) : accepts {a_name} w → accepts {b_name} w :=\n  cover_inclusion _ _ _ _ _ {label}Valid w')


def projection(name, source, keep):
    a = REGISTRY[source]
    inds = [a.names.index(n) for n in keep]
    letters = [encode(bits(c, len(a.names))[i] for i in inds) for c in range(a.width)]
    ar = total(a)
    raw, labels = reachable(keep, frozenset([a.start]),
        lambda ss, ds: frozenset(ar[s][c] for s in ss for c in range(a.width)
                                if letters[c] == encode(ds)),
        lambda ss: bool(ss & a.final))
    out = minimize(raw)
    lines = begin(name, ['Generated.' + source])
    lines.extend([table(name, out), table(name + 'Raw', raw)])
    # The extra unreachable sink added by table() has the empty subset.
    ss = labels + [frozenset()]
    values = ','.join('['+','.join(fin(x) for x in sorted(s))+']' for s in ss)
    lines.append(f'def {name}Subsets : Array (List (Fin {len(a.rows)+1})) := #[{values}]')
    leaves=['['+','.join(fin(x) for x in sorted(s))+']' for s in ss]
    lines.append(f'def {name}SubsetTree : Lookup (List (Fin {len(a.rows)+1})) := {lookup(leaves)}')
    lines.append(f'def {name}Subset (q : Fin {len(raw.rows)+1}) : Finset (Fin {len(a.rows)+1}) := ({name}SubsetTree.get q.val).toFinset')
    lines.append(f'def {name}Letters : Array Nat := #[{",".join(map(str,letters))}]')
    lines.append(f'def {name}Letter (c : Fin {a.width}) : Fin {out.width} := Fin.ofNat {out.width} ({name}Letters[c.val]!)')
    lines.append(f'theorem {name}ProjectionCheck : ProjectionCheck {source} {name}Raw {name}Letter {name}Subset := by decide +kernel')
    include(lines, name+'ToRaw', name, out, name+'Raw', raw)
    lines.append(f'theorem {name}Sound (w) (hw : accepts {name} w) :\n    ∃ u, u.map {name}Letter = w ∧ accepts {source} u :=\n  projection_sound _ _ _ _ (projectionCheck_valid _ _ _ _ {name}ProjectionCheck) w ({name}ToRaw w hw)')
    lines.append(f'#print axioms {name}Sound')
    finish(name, lines)
    REGISTRY[name] = out
    REPORT.append(dict(name=name, kind='projection', raw=len(raw.rows), result=len(out.rows)))
    print(REPORT[-1], flush=True)
    return name


def intersection(name, components):
    # components are (source symbol, renamed track names).
    dfas = [rename(REGISTRY[src], names) for src, names in components]
    names = tuple(dict.fromkeys(n for d in dfas for n in d.names))
    inds = [[names.index(n) for n in d.names] for d in dfas]

    def step(ss, ds):
        ts = tuple(d.rows[s][encode(ds[i] for i in ix)] for d, s, ix in zip(dfas, ss, inds))
        return None if -1 in ts else ts

    raw, labels = reachable(names, tuple(d.start for d in dfas), step,
                            lambda ss: all(s in d.final for s, d in zip(ss, dfas)))
    # Do not minimize before extracting state maps. Remove dead states explicitly.
    live = set(raw.final)
    while True:
        larger = live | {q for q,row in enumerate(raw.rows) if any(t in live for t in row)}
        if larger == live:
            break
        live = larger
    order = [raw.start] + sorted(live - {raw.start})
    ids = {s:i for i,s in enumerate(order)}
    trimmed = DFA(names, [[ids.get(t,-1) for t in raw.rows[s]] for s in order],
                  {ids[s] for s in raw.final})
    out = minimize(trimmed)
    lines = begin(name, ['Generated.'+src for src,_ in components])
    lines.extend([table(name, out), table(name+'Raw', trimmed)])
    include(lines,name+'ToRaw',name,out,name+'Raw',trimmed)
    for j,((source,_),d,ix) in enumerate(zip(components,dfas,inds)):
        part = name+'Part'+str(j)
        maps = ','.join('some '+fin(labels[q][j]) for q in order)+',none'
        letters = [encode(bits(c,len(names))[i] for i in ix) for c in range(out.width)]
        lines.append(f'def {part}States : Array (Option (Fin {len(d.rows)+1})) := #[{maps}]')
        leaves=['(some '+fin(labels[q][j])+')' for q in order]+['none']
        lines.append(f'def {part}StateTree : Lookup (Option (Fin {len(d.rows)+1})) := {lookup(leaves)}')
        lines.append(f'def {part}State (q : Fin {len(trimmed.rows)+1}) := {part}StateTree.get q.val')
        lines.append(f'def {part}Letters : Array Nat := #[{",".join(map(str,letters))}]')
        lines.append(f'def {part}Letter (c : Fin {out.width}) : Fin {d.width} := Fin.ofNat {d.width} ({part}Letters[c.val]!)')
        lines.append(f'theorem {part}Check : ProductCheck {source} {name}Raw {part}Letter {part}State := by decide +kernel')
        lines.append(f'theorem {part}Sound (w) (hw : accepts {name} w) : accepts {source} (w.map {part}Letter) :=\n  product_sound _ _ _ _ (productCheck_valid _ _ _ _ {part}Check) w ({name}ToRaw w hw)')
        lines.append(f'#print axioms {part}Sound')
    finish(name, lines)
    REGISTRY[name] = out
    REPORT.append(dict(name=name, kind='product', raw=len(raw.rows), live=len(trimmed.rows), result=len(out.rows)))
    print(REPORT[-1], flush=True)
    return name


def compose(name, components, keep):
    return projection(name, intersection(name+'Product',components), keep)


def main():
    base('Adder',read('adder'))
    base('Graph',read('candidate-graph'))
    base('One',constant('one',1))
    base('Zero',constant('zero',0))
    compose('Bounded',[('Graph',('n','b')),('Adder',('b','r','n'))],('n',))
    compose('Zeros',[('Graph',('n','b')),('Zero',('b',))],('n',))
    compose('Successor',[('Adder',('m','one','n')),('One',('one',))],('n','m'))
    compose('PredB',[('Successor',('n','m')),('Graph',('m','p'))],('n','p'))
    compose('H',[('PredB',('n','p')),('Adder',('h','p','n'))],('n','h'))
    compose('BH',[('H',('n','h')),('Graph',('h','v'))],('n','v'))
    compose('K',[('BH',('n','v')),('Adder',('k','v','n'))],('n','k'))
    compose('BK',[('K',('n','k')),('Graph',('k','w'))],('n','w'))
    compose('Recurrence',[('Graph',('n','b')),('BK',('n','w')),('Adder',('b','w','n'))],('n',))
    projection('GraphDomain','Graph',('n',))
    projection('AdderDomain','Adder',('x','y'))
    base('DifferenceGraph',difference_graph())
    compose('NextB',[('Successor',('np','n')),('Graph',('np','bp'))],('n','bp'))
    compose('Difference',[('Graph',('n','b')),('NextB',('n','bp')),
                          ('DifferenceGraph',('n','d')),('Adder',('b','d','bp'))],('n',))
    (ROOT/'automata-results'/'lean-operations.json').write_text(json.dumps(REPORT,indent=2)+'\n')


if __name__ == '__main__':
    main()
