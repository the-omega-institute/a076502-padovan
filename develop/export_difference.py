#!/usr/bin/env python3
"""Kernel-checkable trace linking the D graph to its literal output table."""

from automata_proof import reachable,greedy,author_table,difference_graph
from export_operations import begin,finish,include,fin
from export_primitives import trim_labels
from export_lean_certificates import table,lookup


def main():
    d=author_table('D_DFAO');g=greedy('_')
    lines=begin('DifferenceData',['AutomataCertificate'])
    lines.append('def dTransitionTree : Lookup Int := '+lookup(['('+str(v)+')' for row in d for v in row[:2]]))
    lines.append('def dOutputTree : Lookup Int := '+lookup([row[2] for row in d]))
    lines.append('def dTransitions (q : Fin 28) (b : Bool) : Int := dTransitionTree.get (2*q.val + if b then 1 else 0)')
    lines.append('def dOutput (q : Fin 28) : Int := dOutputTree.get q.val')
    lines.append('theorem d_binary : ∀ q : Fin 28, dOutput q = 0 ∨ dOutput q = 1 := by decide +kernel')
    finish('DifferenceData',lines)
    def step(s,l):
        q,r,last=s;x,y=l
        if last==1:return None
        qn,rn=d[q][x],g.rows[r][x]
        return None if min(qn,rn)<0 else (qn,rn,y)
    a,labels=reachable(('n','d'),(0,0,0),step,lambda s:d[s[0]][2]==s[2])
    a,labels=trim_labels(a,labels)
    lines=begin('DifferenceTrace',['DifferenceSemantics','Generated.DifferenceGraph'])
    lines.append('open Difference Primitive WordArithmetic')
    lines.append(table('RawDifference',a))
    include(lines,'differenceToTrace','DifferenceGraph',difference_graph(),'RawDifference',a)
    values=['(some ('+fin(q)+','+fin(last)+'))' for q,r,last in labels]+['none']
    lines.append('def diffLabels : Lookup (Option (Fin 28 × Fin 3)) := '+lookup(values))
    lines.append(f'def diffLabel (q : Fin {len(a.rows)+1}) := diffLabels.get q.val')
    lines.append('theorem diffTrace : TraceCheck RawDifference (0,0) diffStep diffGood diffLabel := by decide +kernel')
    lines.append('theorem differenceValue (w) (h : accepts DifferenceGraph w) : wordValue (digit 0) w = dOutput (dRun 0 (w.map (bit 1))) :=\n  diff_trace_value w (trace_sound _ _ _ _ _ diffTrace w (differenceToTrace w h))')
    lines.append('#print axioms differenceValue')
    finish('DifferenceTrace',lines)
    print('D graph semantic states:',len(a.rows))


if __name__=='__main__':
    main()
