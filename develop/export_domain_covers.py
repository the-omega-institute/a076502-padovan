#!/usr/bin/env python3
"""Bridge the certified universal domains to the semantic operation tables."""

import ast
import re
from automata_proof import DFA, prefixed_zero_domain, intersect, reachable, constant
from export_operations import OUT, begin, finish, include


def emitted(name):
    text=(OUT/(name+'.lean')).read_text()
    rows=ast.literal_eval(re.search(r'def '+name+r'Rows.*?:= (.*)',text)[1].replace('#[','['))
    finals=ast.literal_eval(re.search(r'def '+name+r'Final.*?:= (.*)',text)[1].replace('#[','[').replace('true','True').replace('false','False'))
    start=int(re.search(r'start := ⟨(\d+)',text)[1])
    sink=len(rows)-1
    return DFA(('n',),[[t if t<sink else -1 for t in row] for row in rows[:-1]],
               {q for q,b in enumerate(finals[:-1]) if b},start)


def main():
    g=prefixed_zero_domain(('n',),3)
    threshold,_=reachable(('n',),0,lambda v,b:min(2,2*v+b[0]),lambda v:v==2)
    g2=intersect(g,threshold)
    lines=begin('DomainCovers',['ConcreteCertificates','Generated.GraphDomain','Generated.Bounded',
                              'Generated.Recurrence','Generated.Zeros','Generated.Zero','Generated.Difference'])
    for label,left_name,left,right_name in [
        ('totalGraph','Concrete.graphTotalityLeft',g,'GraphDomain'),
        ('totalBound','Concrete.candidateBoundLeft',g,'Bounded'),
        ('totalRecurrence','Concrete.recurrenceLanguageLeft',g2,'Recurrence'),
        ('totalDifference','Concrete.differenceLanguageLeft',g,'Difference')]:
        include(lines,label,left_name,left,right_name,emitted(right_name))
        module=label[0].upper()+label[1:]
        standalone=begin(module,['ConcreteCertificates','Generated.'+right_name])
        include(standalone,label,left_name,left,right_name,emitted(right_name))
        finish(module,standalone)
    zeros=begin('TotalZeros',['Generated.Zeros','Generated.Zero'])
    include(zeros,'zerosOnlyAtZero','Zeros',emitted('Zeros'),'Zero',constant('n',0))
    finish('TotalZeros',zeros)
    finish('DomainCovers',begin('DomainCovers',['Generated.'+s for s in
      ['TotalGraph','TotalBound','TotalRecurrence','TotalDifference','TotalZeros']]))


if __name__=='__main__':
    main()
