#!/usr/bin/env python3
"""Untrusted producer of finite live-state semantic trace certificates."""

from automata_proof import DFA, reachable, greedy, carry_step, value, author_table
from export_operations import ROOT, OUT, begin, finish, include, fin
from export_lean_certificates import read, table, lookup


def trim_labels(a,labels):
    live=set(a.final)
    while True:
        larger=live|{q for q,row in enumerate(a.rows) if any(t in live for t in row)}
        if larger==live:break
        live=larger
    order=[a.start]+sorted(live-{a.start})
    ids={s:i for i,s in enumerate(order)}
    return (DFA(a.names,[[ids.get(t,-1) for t in a.rows[s]] for s in order],
                {ids[s] for s in a.final}),[labels[s] for s in order])


def carry(r):
    return '⟨'+','.join(str(x) if x>=0 else '('+str(x)+')' for x in r)+'⟩'


def main():
    g=greedy('_'); e=author_table('E_DFAO')
    def addstep(s,l):
        r,last,gs=s;z=l[0]+l[1]-l[2];nr=carry_step(r,z)
        ng=tuple(g.rows[q][b] for q,b in zip(gs,l))
        return None if min(ng)<0 or max(map(abs,nr))>8 else (nr,z,ng)
    a,labels=reachable(('x','y','z'),((0,0,0),0,(0,0,0)),addstep,lambda s:value(s[0])==s[1])
    a,labels=trim_labels(a,labels)
    lines=begin('AdderTrace',['Generated.Adder','PrimitiveSemantics'])
    lines.append('open Primitive WordArithmetic')
    lines.append(table('RawAdder',a))
    include(lines,'adderToTrace','Adder',read('adder'),'RawAdder',a)
    vals=','.join('some ('+carry(r)+','+str(last)+')' for r,last,gs in labels)+',none'
    lines.append(f'def adderLabels : Array (Option (Carry × Int)) := #[{vals}]')
    leaves=['(some ('+carry(r)+','+str(last)+'))' for r,last,gs in labels]+['none']
    lines.append(f'def adderLabelTree : Lookup (Option (Carry × Int)) := {lookup(leaves)}')
    lines.append(f'def adderLabel (q : Fin {len(a.rows)+1}) := adderLabelTree.get q.val')
    lines.append('theorem adderTrace : TraceCheck RawAdder (zeroCarry,0) addStep addGood adderLabel := by decide +kernel')
    lines.append('theorem adderValue (w) (hw : accepts Adder w) :\n    wordValue (digit 2) w + wordValue (digit 1) w = wordValue (digit 0) w :=\n  add_trace_value w (trace_sound _ _ _ _ _ adderTrace w (adderToTrace w hw))')
    lines.append('#print axioms adderValue')
    finish('AdderTrace',lines)
    print('adder live states',len(a.rows),flush=True)

    def graphstep(s,l):
        q,gx,gy,old,recent,r,last=s;x,y=l
        qn=e[q][x];gxn,gyn=g.rows[gx][x],g.rows[gy][y]
        z=old-y;nr=carry_step(r,z)
        return None if min(qn,gxn,gyn)<0 or max(map(abs,nr))>8 else (qn,gxn,gyn,recent,x,nr,z)
    a,labels=reachable(('n','b'),(0,0,0,0,0,(0,0,0),0),graphstep,
                       lambda s:value(s[-2])-s[-1]+e[s[0]][2]==0)
    a,labels=trim_labels(a,labels)
    lines=begin('GraphTrace',['Generated.Graph','PrimitiveSemantics'])
    lines.append('open Primitive WordArithmetic')
    lines.append(table('RawGraph',a))
    include(lines,'graphToTrace','Graph',read('candidate-graph'),'RawGraph',a)
    vals=','.join('some (⟨'+carry(r)+','+str(old)+','+str(recent)+','+str(last)+'⟩,'+fin(q)+')'
                  for q,gx,gy,old,recent,r,last in labels)+',none'
    lines.append(f'def graphLabels : Array (Option (DelayState × Fin 28)) := #[{vals}]')
    leaves=['(some (⟨'+carry(r)+','+str(old)+','+str(recent)+','+str(last)+'⟩,'+fin(q)+'))'
            for q,gx,gy,old,recent,r,last in labels]+['none']
    lines.append(f'def graphLabelTree : Lookup (Option (DelayState × Fin 28)) := {lookup(leaves)}')
    lines.append(f'def graphLabel (q : Fin {len(a.rows)+1}) := graphLabelTree.get q.val')
    lines.append('theorem graphTrace : TraceCheck RawGraph (initial,0) graphStep graphGood graphLabel := by decide +kernel')
    lines.append('theorem graphValue (w) (hw : accepts Graph w) :\n    wordValue (digit 0) w = shiftValue (digit 1) w + Suffix.output (eRun 0 (w.map (bit 1))) :=\n  graph_trace_value w (trace_sound _ _ _ _ _ graphTrace w (graphToTrace w hw))')
    lines.append(f'def graphPathLabel (q : Fin {len(a.rows)+1}) := (graphLabel q).map Prod.snd')
    lines.append('theorem graphPathCheck : PathCheck RawGraph (bit 1) graphPathLabel := by decide +kernel')
    lines.append('theorem graphPath (w) (hw : accepts Graph w) : ∃ last, Suffix.Path 0 (w.map (bit 1)) last :=\n  path_sound _ _ _ graphPathCheck w (graphToTrace w hw)')
    sem=[4,0,1,2,3,5]
    for idx,coord in [(1,1),(2,0)]:
        name='graphGreedy'+str(coord)
        vals=','.join('some '+fin(sem[s[idx]]) for s in labels)+',none'
        lines.append(f'def {name}Labels : Array (Option (Fin 7)) := #[{vals}]')
        leaves=['(some '+fin(sem[s[idx]])+')' for s in labels]+['none']
        lines.append(f'def {name}LabelTree : Lookup (Option (Fin 7)) := {lookup(leaves)}')
        lines.append(f'def {name}Label (q : Fin {len(a.rows)+1}) := {name}LabelTree.get q.val')
        lines.append(f'def {name}Letter (a : Fin 4) : Fin 2 := Fin.ofNat 2 (a.val / 2^{coord})')
        lines.append(f'theorem {name}Check : ProductCheck greedyMachine RawGraph {name}Letter {name}Label := by decide +kernel')
        lines.append(f'theorem {name}Sound (w) (hw : accepts Graph w) : accepts greedyMachine (w.map {name}Letter) :=\n  product_sound _ _ _ _ (productCheck_valid _ _ _ _ {name}Check) w (graphToTrace w hw)')
    lines.append('#print axioms graphValue')
    lines.append('#print axioms graphPath')
    finish('GraphTrace',lines)
    print('graph live states',len(a.rows),flush=True)


if __name__=='__main__':
    main()
