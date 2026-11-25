import argparse
import json
import threading
import time
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

args = argparse.ArgumentParser()
args.add_argument('size', type=int)
args.add_argument('--not', dest='neg', type=int, default=1)
args.add_argument('--seconds', type=int, default=300)
args.add_argument('--prefix', type=int, default=0)
args.add_argument('--useful-not', action='store_true')
opts = args.parse_args()
n=7
pool=IDPool();cnf=CNF();sels=[];ors=[];nots=[]
for g in range(opts.size):
    w=n+g
    aa=[pool.id(('a',g,i)) for i in range(w)]
    bb=[pool.id(('b',g,i)) for i in range(w)]
    sels.append((aa,bb))
    ov=pool.id(('or',g)); nv=pool.id(('not',g))
    ors.append(ov);nots.append(nv)
    cnf.append([-ov,-nv])
    for a,b in zip(aa,bb):
        # NOT reads its first operand only; duplicate it to avoid unused choices.
        cnf.extend([[-nv,-a,b],[-nv,-b,a]])
    for sel in (aa,bb):
        cnf.extend(CardEnc.equals(sel,1,vpool=pool,encoding=EncType.seqcounter))
    for i in range(w):
        for j in range(i):cnf.append([-aa[i],-bb[j]])
cnf.extend(CardEnc.atmost(nots,opts.neg,vpool=pool,encoding=EncType.seqcounter))
if opts.neg == 1:
    # A counterexample cannot itself be monotone: it would be its own replacement.
    cnf.append(nots)
for wire in range(n+opts.size-1):
    cnf.append([s[wire] for pair in sels for s in pair if wire<len(s)])
for x in range(1<<n):
    vals=[bool(x>>i&1) for i in range(n)]
    for g in range(opts.size):
        a=pool.id(('mux',x,g,0));b=pool.id(('mux',x,g,1));out=pool.id(('v',x,g))
        for sel,dest in zip(sels[g],(a,b)):
            for s,val in zip(sel,vals):
                if isinstance(val,bool):cnf.append([-s,dest if val else -dest])
                else:cnf.extend([[-s,-val,dest],[-s,val,-dest]])
        ov,nv=ors[g],nots[g]
        cnf.extend([[-ov,-a,out],[-ov,-b,out],[-ov,a,b,-out],
                    [ov,nv,a,-out],[ov,nv,b,-out],[ov,nv,-a,-b,out],
                    [-nv,a,out],[-nv,-a,-out]])
        vals.append(out)
    cnf.append([vals[-1] if bin(x).count('1')>=2 else -vals[-1]])
if opts.useful_not:
    for g,nv in enumerate(nots):
        singleton_values=[pool.id(('mux',1<<i,g,0)) for i in range(n)]
        cnf.append([-nv,*singleton_values])
        cnf.append([-nv,*[-v for v in singleton_values]])
    cnf.append([-nots[-1]])
print(json.dumps(dict(size=opts.size,negations=opts.neg,variables=pool.top,clauses=len(cnf.clauses))),flush=True)
start=time.monotonic()
with Solver(name='g4',bootstrap_with=cnf) as solver:
    assumptions=[]
    for g in range(opts.prefix):
        assumptions.extend([sels[g][0][2*g],sels[g][1][2*g+1],-ors[g],-nots[g]])
    timer=threading.Timer(opts.seconds,solver.interrupt);timer.start()
    try:result=solver.solve_limited(assumptions=assumptions,expect_interrupt=True)
    finally:timer.cancel()
    print(json.dumps(dict(result=result,elapsed=time.monotonic()-start,stats=solver.accum_stats())),flush=True)
    if result:
        model=set(solver.get_model())
        gates=[dict(op='not' if nots[g] in model else 'or' if ors[g] in model else 'and',
                    inputs=[next(i for i,s in enumerate(sel) if s in model) for sel in sels[g]]) for g in range(opts.size)]
        for x in range(1<<n):
            vals=[bool(x>>i&1) for i in range(n)]
            for g in gates:
                a,b=[vals[j] for j in g['inputs']]
                vals.append(not a if g['op']=='not' else a or b if g['op']=='or' else a and b)
            assert vals[-1]==(bin(x).count('1')>=2)
        p=Path(f'threshold7-s{opts.size}-not{opts.neg}.json')
        p.write_text(json.dumps(dict(size=opts.size,gates=gates),indent=2))
        print(f'Independently verified all 128 inputs: {p}',flush=True)
