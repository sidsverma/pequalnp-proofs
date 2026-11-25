import argparse
import json
import threading
import time
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

base=json.loads(Path('threshold16.json').read_text())
gates=base['gates'];n=7

def attempt(start,width,seconds=3,reduction=1):
    end=start+width;size=width-reduction;initial=n+start
    boundary=sorted({w for g in gates[end:] for w in g['inputs'] if n+start<=w<n+end}
                    |({base['output']} if n+start<=base['output']<n+end else set()))
    pool=IDPool();cnf=CNF();true=pool.id('true');cnf.append([true]);sels=[];ors=[];nots=[]
    for g in range(size):
        w=initial+g
        aa=[pool.id(('a',g,i)) for i in range(w)];bb=[pool.id(('b',g,i)) for i in range(w)]
        sels.append((aa,bb));ov=pool.id(('or',g));nv=pool.id(('not',g));ors.append(ov);nots.append(nv)
        cnf.append([-ov,-nv])
        for sel in (aa,bb):cnf.extend(CardEnc.equals(sel,1,vpool=pool,encoding=EncType.seqcounter))
        for i in range(w):
            for j in range(i):cnf.append([-aa[i],-bb[j]])
    cnf.extend(CardEnc.atmost(nots,1,vpool=pool,encoding=EncType.seqcounter))
    aliases={w:[pool.id(('alias',w,i)) for i in range(initial+size)] for w in boundary}
    for sel in aliases.values():cnf.extend(CardEnc.equals(sel,1,vpool=pool,encoding=EncType.seqcounter))
    def mux(sel,values,key):
        dest=pool.id(key)
        for s,val in zip(sel,values):cnf.extend([[-s,-val,dest],[-s,val,-dest]])
        return dest
    for x in range(128):
        known=[bool(x>>i&1) for i in range(n)]
        for gate in gates[:start]:
            a,b=[known[w] for w in gate['inputs']];known.append(a or b if gate['op']=='or' else a and b)
        values=[true if v else -true for v in known]
        for g in range(size):
            a=mux(sels[g][0],values,('mux',x,g,0));b=mux(sels[g][1],values,('mux',x,g,1));out=pool.id(('v',x,g));ov,nv=ors[g],nots[g]
            cnf.extend([[-ov,-a,out],[-ov,-b,out],[-ov,a,b,-out],
                        [ov,nv,a,-out],[ov,nv,b,-out],[ov,nv,-a,-b,out],[-nv,a,out],[-nv,-a,-out]])
            values.append(out)
        wires={i:v for i,v in enumerate(values[:initial])}
        for w,sel in aliases.items():wires[w]=mux(sel,values,('aliasvalue',x,w))
        for j,gate in enumerate(gates[end:],end):
            a,b=[wires[w] for w in gate['inputs']];out=pool.id(('suffix',x,j));wires[n+j]=out
            if gate['op']=='or':cnf.extend([[-a,out],[-b,out],[a,b,-out]])
            else:cnf.extend([[a,-out],[b,-out],[-a,-b,out]])
        out=wires[base['output']]
        cnf.append([out if bin(x).count('1')>=2 else -out])
    with Solver(name='g4',bootstrap_with=cnf) as solver:
        timer=threading.Timer(seconds,solver.interrupt);timer.start()
        try:result=solver.solve_limited(expect_interrupt=True)
        finally:timer.cancel()
        print(json.dumps(dict(start=start,width=width,result=result,conflicts=solver.accum_stats()['conflicts'])),flush=True)
        if not result:return None
        model=set(solver.get_model())
        new=[dict(op='not' if nots[g] in model else 'or' if ors[g] in model else 'and',
                  inputs=[next(i for i,s in enumerate(sel) if s in model) for sel in sels[g]]) for g in range(size)]
        mapping={w:next(i for i,s in enumerate(sel) if s in model) for w,sel in aliases.items()}
        def remap(w):return w if w<initial else mapping[w] if w<n+end else w-reduction
        candidate=gates[:start]+new+[dict(op=g['op'],inputs=[remap(w) for w in g['inputs']]) for g in gates[end:]]
        output=remap(base['output'])
        for x in range(128):
            vals=[bool(x>>i&1) for i in range(n)]
            for gate in candidate:
                a,b=[vals[w] for w in gate['inputs']];vals.append(not a if gate['op']=='not' else a or b if gate['op']=='or' else a and b)
            assert vals[output]==(bin(x).count('1')>=2)
        assert sum(g['op']=='not' for g in candidate)<=1
        return dict(gates=candidate,output=output,size=len(candidate))

parser=argparse.ArgumentParser()
parser.add_argument('--min',type=int,default=3)
parser.add_argument('--max',type=int,default=8)
parser.add_argument('--seconds',type=int,default=3)
parser.add_argument('--reduction',type=int,default=1)
opts=parser.parse_args()
for width in range(opts.min,opts.max+1):
    for start in range(len(gates)-width+1):
        candidate=attempt(start,width,opts.seconds,opts.reduction)
        if candidate:
            filename='threshold-window-witness.json' if opts.reduction else 'threshold-window-validation.json'
            Path(filename).write_text(json.dumps(candidate,indent=2))
            print(f"FOUND verified {candidate['size']}-gate circuit",flush=True)
            raise SystemExit(0)
print('No witness in the bounded window search; timeouts are inconclusive.',flush=True)
