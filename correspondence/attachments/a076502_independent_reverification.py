#!/usr/bin/env python3
"""Independent re-verification of the A076502 Padovan identification.

Written from the mathematical description only. It does not import the package code
nor its JSON automata. The only imported datum is the 28-state table E.

Part 1 (automata): b(n) = shift2(n) + E(greedy(n)) satisfies b(0)=0, b(1)=1 and
    b(n) = n - b(n - b(n - b(n-1)))  for all n >= 2,
with a self-certified adder (carry invariant modulo X^3-X-1, totality by inclusion).
Part 2 (discrepancy): exact rational enclosure of b(n) - c*n.

Usage: python3 a076502_independent_reverification.py [BOX]   (carry box, default 8)
"""
import sys, time
from itertools import product
BOX=int(sys.argv[1]) if len(sys.argv)>1 else 8
E=[(0,1,0),(2,-1,1),(3,-1,1),(4,-1,1),(5,6,0),(7,8,0),(-1,-1,1),(9,10,0),(11,-1,0),(5,12,0),(13,-1,1),(14,-1,2),(15,-1,1),(16,-1,1),
   (17,-1,0),(18,-1,1),(19,-1,1),(20,21,1),(22,-1,1),(23,21,1),(24,1,0),(-1,-1,0),(9,6,0),(25,10,-1),(26,1,0),(20,27,1),(23,8,1),(15,-1,0)]
# ---------- greedy language (msd first, leading zeros allowed) ----------
# state = number of zeros still required (0..4), or 'X' = the exceptional 1 at position 0 was just read (must be last)
def gstep(g,b):
    if g=='X': return None
    if b==0: return max(g-1,0)
    if g==0: return 4
    if g==1: return 'X'
    return None
# ---------- carry: remainder modulo X^3-X-1, value = L(r) - last signed digit ----------
def cstep(r,s):
    r0,r1,r2=r; t=(r2+s,r0+r2,r1)
    return t if max(map(abs,t))<=BOX else None
def L(r): return 2*r[0]+2*r[1]+3*r[2]
# ---------- partial DFAs ----------
class DFA:
    def __init__(s,k,trans,final): s.k=k; s.trans=trans; s.final=final   # trans: list of dict symbol->state ; initial state 0
def build(k,start,step,accept):
    ids={start:0}; order=[start]; trans=[]; final=set()
    syms=list(product((0,1),repeat=k))
    for st in order:
        if accept(st): final.add(ids[st])
        row={}
        for a in syms:
            t=step(st,a)
            if t is None: continue
            if t not in ids: ids[t]=len(order); order.append(t)
            row[a]=ids[t]
        trans.append(row)
    return DFA(k,trans,final)
def trim(d):
    n=len(d.trans); rev=[[] for _ in range(n)]
    for q,row in enumerate(d.trans):
        for t in row.values(): rev[t].append(q)
    live=set(d.final); todo=list(live)
    while todo:
        q=todo.pop()
        for p in rev[q]:
            if p not in live: live.add(p); todo.append(p)
    if 0 not in live: return DFA(d.k,[{}],set())
    ren={}; order=[0]; ren[0]=0
    for q in order:
        for a,t in d.trans[q].items():
            if t in live and t not in ren: ren[t]=len(order); order.append(t)
    return DFA(d.k,[{a:ren[t] for a,t in d.trans[q].items() if t in live} for q in order],{ren[q] for q in d.final if q in ren})
def minimize(d):
    d=trim(d); n=len(d.trans); syms=list(product((0,1),repeat=d.k))
    cls=[1 if q in d.final else 0 for q in range(n)]
    while True:
        sig={}; new=[]
        for q in range(n):
            key=(cls[q],tuple(cls[d.trans[q][a]] if a in d.trans[q] else -1 for a in syms))
            new.append(sig.setdefault(key,len(sig)))
        if len(sig)==len(set(cls)): cls=new; break
        cls=new
    rep={}
    for q in range(n): rep.setdefault(cls[q],q)
    ren={cls[0]:0}; order=[cls[0]]
    for c in order:
        for a,t in d.trans[rep[c]].items():
            if cls[t] not in ren: ren[cls[t]]=len(order); order.append(cls[t])
    return DFA(d.k,[{a:ren[cls[t]] for a,t in d.trans[rep[c]].items()} for c in order],{ren[cls[q]] for q in d.final})
def compose(ntracks,visible,comps):
    """comps = list of (dfa, global track indices). Returns the minimal DFA on the visible tracks of
       { visible : there exist hidden tracks such that every component accepts }."""
    hidden=[t for t in range(ntracks) if t not in visible]
    start=frozenset([tuple(0 for _ in comps)])
    def step(S,a):
        out=set()
        for tup in S:
            for hb in product((0,1),repeat=len(hidden)):
                bits=[0]*ntracks
                for i,t in enumerate(visible): bits[t]=a[i]
                for i,t in enumerate(hidden): bits[t]=hb[i]
                nt=[]
                for (dfa,idx),q in zip(comps,tup):
                    t2=dfa.trans[q].get(tuple(bits[j] for j in idx))
                    if t2 is None: break
                    nt.append(t2)
                else: out.add(tuple(nt))
        return frozenset(out) if out else None
    def accept(S): return any(all(q in dfa.final for (dfa,_),q in zip(comps,tup)) for tup in S)
    return minimize(build(len(visible),start,step,accept))
t0=time.time()
# ---------- building blocks ----------
# Add(x,y,z) : x+y=z
ADD=minimize(build(3,((0,0,0),0,0,0,0),
    lambda st,a:(lambda r,gx,gy,gz:None if None in (r,gx,gy,gz) else (r,a[0]+a[1]-a[2],gx,gy,gz))(cstep(st[0],a[0]+a[1]-a[2]),gstep(st[2],a[0]),gstep(st[3],a[1]),gstep(st[4],a[2])),
    lambda st:L(st[0])-st[1]==0))
print("adder:",len(ADD.trans),"states"); sys.stdout.flush()
# B(n,b) : b = shift2(n)+E(n).  state = (r, last signed digit, 2-digit delay line of n, E state, g_n, g_b)
def bstep(st,a):
    r,last,d1,d2,e,gn,gb=st; s=d2-a[1]           # d2 = digit of n read two steps earlier
    r2=cstep(r,s); e2=E[e][a[0]]; gn2=gstep(gn,a[0]); gb2=gstep(gb,a[1])
    if r2 is None or e2<0 or gn2 is None or gb2 is None: return None
    return (r2,s,a[0],d1,e2,gn2,gb2)
B=minimize(build(2,((0,0,0),0,0,0,0,0,0),bstep,lambda st:L(st[0])-st[1]+E[st[4]][2]==0))
print("graph (n,b(n)):",len(B.trans),"states"); sys.stdout.flush()
ONE=DFA(1,[{(0,):0,(1,):1},{}],{1})
# ---------- recurrence chain ----------
# tracks : 0=n 1=m 2=o 3=p
R1=compose(4,[0,3],[(ADD,(1,2,0)),(ONE,(2,)),(B,(1,3))]);                 print("(n, b(n-1)):",len(R1.trans),"states"); sys.stdout.flush()
# tracks : 0=n 1=p 2=h 3=v
R2=compose(4,[0,3],[(R1,(0,1)),(ADD,(2,1,0)),(B,(2,3))]);                 print("(n, b(n-b(n-1))):",len(R2.trans),"states"); sys.stdout.flush()
# tracks : 0=n 1=v 2=k 3=w
R3=compose(4,[0,3],[(R2,(0,1)),(ADD,(2,1,0)),(B,(2,3))]);                 print("(n, b(n-b(n-b(n-1)))):",len(R3.trans),"states"); sys.stdout.flush()
# tracks : 0=n 1=w 2=u
GOOD=compose(3,[0],[(R3,(0,1)),(B,(0,2)),(ADD,(2,1,0))]);                 print("Good(n):",len(GOOD.trans),"states"); sys.stdout.flush()
# ---------- universal inclusions ----------
def included(cond_start,cond_step,cond_accept,target):
    """is every word accepted by the condition automaton accepted by target? returns a counterexample word or None"""
    seen={(cond_start,0):None}; todo=[(cond_start,0)]
    while todo:
        c,q=todo.pop()
        if cond_accept(c) and (q is None or q not in target.final):
            w=[];x=(c,q)
            while seen[x] is not None: x,b=seen[x]; w.append(b)
            return w[::-1]
        for b in (0,1):
            c2=cond_step(c,b)
            if c2 is None: continue
            q2=None if q is None else target.trans[q].get((b,))
            if (c2,q2) not in seen: seen[(c2,q2)]=((c,q),b); todo.append((c2,q2))
    return None
# condition: word = 000 followed by a word of G (leading zeros allowed)
# state = (leading zeros read (max 3), g, v) where v encodes the value: 0 -> value 0 ; 1 -> value 1 ; 2 -> value >= 2
def cs(c,b):
    z,g,v=c
    if z<3: return (z+1,g,v) if b==0 else None
    g2=gstep(g,b)
    if g2 is None: return None
    if v==0: v2=1 if b==1 else 0
    else: v2=2
    return (3,g2,v2)
print("adder totality, 000(GxG) included in exists z:", end=" ")
DOM=compose(3,[0,1],[(ADD,(0,1,2))])
def cs2(c,a):
    z,g1,g2=c
    if z<3: return (z+1,g1,g2) if a==(0,0) else None
    h1,h2=gstep(g1,a[0]),gstep(g2,a[1])
    return None if h1 is None or h2 is None else (3,h1,h2)
seen={((0,0,0),0)}; todo=[((0,0,0),0)]; cex=False
while todo:
    c,q=todo.pop()
    if c[0]==3 and (q is None or q not in DOM.final): cex=True; break
    for a in product((0,1),repeat=2):
        c2=cs2(c,a)
        if c2 is None: continue
        q2=None if q is None else DOM.trans[q].get(a)
        if (c2,q2) not in seen: seen.add((c2,q2)); todo.append((c2,q2))
print("COUNTEREXAMPLE" if cex else "OK")
TOT=compose(2,[0],[(B,(0,1))])
print("graph totality on 000G:", included((0,0,0),cs,lambda c:c[0]==3,TOT) or "OK")
print("recurrence for all n>=2, (000G, value>=2) included in Good:", included((0,0,0),cs,lambda c:c[0]==3 and c[2]==2,GOOD) or "OK")
# b(n) <= n, and b(n) >= 1 for n >= 1
LE=compose(3,[0],[(B,(0,1)),(ADD,(1,2,0))])
print("b(n) <= n for all n:", included((0,0,0),cs,lambda c:c[0]==3,LE) or "OK")
ZERO=DFA(1,[{(0,):0}],{0})
BZ=compose(2,[0],[(B,(0,1)),(ZERO,(1,))])
seen={((0,0,0),0)}; todo=[((0,0,0),0)]; found=False
while todo:
    c,q=todo.pop()
    if c[0]==3 and c[2]>=1 and q in BZ.final: found=True; break
    for b in (0,1):
        c2=cs(c,b); q2=BZ.trans[q].get((b,)) if q is not None else None
        if c2 is None or q2 is None: continue
        if (c2,q2) not in seen: seen.add((c2,q2)); todo.append((c2,q2))
print("b(n) = 0 only for n = 0:", "COUNTEREXAMPLE" if found else "OK")
print("b(0) =",0+E[0][2],"; b(1) =",0+E[E[0][1]][2])
print("part 1 done in",round(time.time()-t0,1),"s ; carry box = [-%d,%d]^3"%(BOX,BOX))

# ---------- Part 2: exact rational enclosure of b(n) - c*n ----------
from fractions import Fraction as Fr
# rational bracket of c by exact bisection on P(x)=x^3-x^2+2x-1 (strictly increasing)
lo,hi=Fr(0),Fr(1)
for _ in range(80):
    mid=(lo+hi)/2
    if mid**3-mid**2+2*mid-1<0: lo=mid
    else: hi=mid
U=[1,2,3,4,5]
while len(U)<200: U.append(U[-2]+U[-3])
def delta_iv(p):   # rational interval containing delta_p
    if p==0: return (-hi,-lo)
    if p==1: return (-2*hi,-2*lo)
    return (U[p-2]-hi*U[p],U[p-2]-lo*U[p])
# pairs (E state, G state) reachable after an arbitrary prefix
start=(0,0); reach={start}; todo=[start]
while todo:
    e,g=todo.pop()
    for b in (0,1):
        e2=E[e][b]; g2=gstep(g,b)
        if e2<0 or g2 is None: continue
        if (e2,g2) not in reach: reach.add((e2,g2)); todo.append((e2,g2))
print("reachable (E,G) pairs:",len(reach))
for K in (20,40,70):
    # tail: positions >= K, gaps >= 5, |delta_p| < (5/16)(7/8)^(p-3)  (quadratic-energy lemma)
    R=Fr(5,16)*Fr(7,8)**(K-3)/(1-Fr(7,8)**5)
    cur={s:(Fr(0),Fr(0)) for s in reach}
    for pos in range(K-1,-1,-1):
        nxt={}
        for (e,g),(a,b) in cur.items():
            for bit in (0,1):
                e2=E[e][bit]; g2=gstep(g,bit)
                if e2<0 or g2 is None: continue
                d=delta_iv(pos) if bit else (Fr(0),Fr(0))
                na,nb=a+d[0],b+d[1]
                if (e2,g2) in nxt: o=nxt[(e2,g2)]; nxt[(e2,g2)]=(min(o[0],na),max(o[1],nb))
                else: nxt[(e2,g2)]=(na,nb)
        cur=nxt
    lo_=min(a+E[e][2] for (e,g),(a,b) in cur.items()); hi_=max(b+E[e][2] for (e,g),(a,b) in cur.items())
    print("K=%d: suffix in [%.9f, %.9f] ; tail R=%.3e ; final enclosure (%.6f, %.6f) ; inside (-11/10, 6/5): %s"%(K,lo_,hi_,float(R),float(lo_-R),float(hi_+R), (lo_-R>Fr(-11,10)) and (hi_+R<Fr(6,5))))
