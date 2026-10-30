"""Independent weighted parity and witness checks for the four main corollaries."""
import argparse
from collections import Counter
from itertools import combinations
import json
import os
from pathlib import Path
import random
import resource
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_cnf_reference import exact_count,literal_constraints
from cnf_circuits import connected_object_cnf


def components(n,U,F):
    blocks = [{i} for i in range(n) if U>>i&1]
    for a,b in F:
        ia=next(j for j,s in enumerate(blocks) if a in s)
        ib=next(j for j,s in enumerate(blocks) if b in s)
        if ia!=ib:
            blocks[ia] |= blocks[ib]
            del blocks[ib]
    return blocks


def references(n,edges,mode,root):
    data=[]
    for U in range(1<<n):
        if mode!="fvs" and U>>root&1==0:
            continue
        us=tuple((U>>i)&1 for i in range(n))
        inside=[i for i,(a,b) in enumerate(edges) if us[a] and us[b]]
        if mode=="cover" and any(not(us[a] or us[b]) for a,b in edges):
            continue
        if mode=="dominating":
            dominated={i for i in range(n) if us[i]}
            for a,b in edges:
                if us[a]: dominated.add(b)
                if us[b]: dominated.add(a)
            if len(dominated)!=n: continue
        if mode=="steiner":
            if not(us[0] and us[-1]): continue
            for F in combinations(inside,U.bit_count()-1):
                cc=len(components(n,U,[edges[i] for i in F]))
                data.append((us+tuple(int(i in F) for i in range(len(edges))),1<<(cc-1),cc==1))
        elif mode=="fvs":
            blocks=components(n,U,[edges[i] for i in inside])
            for M in range(1<<n):
                if M&~U or len(inside)+M.bit_count()!=U.bit_count(): continue
                unmarked=sum(not any(M>>v&1 for v in block) for block in blocks)
                one_marker=all(sum((M>>v)&1 for v in block)==1 for block in blocks)
                forest=len(inside)==U.bit_count()-len(blocks)
                data.append((us+tuple((M>>i)&1 for i in range(n)),1<<unmarked,forest and one_marker))
        else:
            cc=len(components(n,U,[edges[i] for i in inside]))
            data.append((us,1<<(cc-1),cc==1))
    return data


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--mode",required=True,choices=("steiner","cover","dominating","fvs"))
    ap.add_argument("--n",type=int,default=5)
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--stop",type=int,default=4)
    ap.add_argument("--progress",required=True)
    args=ap.parse_args()
    assert os.getpriority(os.PRIO_PROCESS,0)>=19
    resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2))
    begin=time.monotonic()
    rows=[]
    for trial in range(args.start,args.stop):
        rng=random.Random(10301000+trial*13+len(args.mode))
        n=args.n
        possible=list(combinations(range(n),2))
        edges=sorted(rng.sample(possible,min(len(possible),n+trial%4)))
        root=0 if args.mode=="steiner" else trial%n
        c=connected_object_cnf(n,edges,args.mode,terminals=(0,n-1),root=root)
        names=[f"vertex_{i}" for i in range(n)]
        if args.mode=="steiner": names += [f"edge_{i}" for i in range(len(edges))]
        if args.mode=="fvs": names += [f"marker_{i}" for i in range(n)]
        bits=[c.names[s] for s in names]
        p=len(bits)
        costs=[rng.randrange(4) for _ in range(p)]
        constant=0
        if args.mode=="fvs":
            constant=sum(costs[:n])
            costs=[-x for x in costs[:n]]+[0]*n
        W=2*p
        weights=[rng.randint(1,W) for _ in range(p)]
        P=p*W+1
        coeffs=[P*a+w for a,w in zip(costs,weights)]
        shift=P*constant+sum(min(0,a) for a in coeffs)
        out=c.weighted_sum([x if a>=0 else -x for x,a in zip(bits,coeffs)],
                           [abs(a) for a in coeffs])
        objects=references(n,edges,args.mode,root)
        cuts,truth=Counter(),Counter()
        valid={}
        for values,multiplicity,real in objects:
            cost=constant+sum(a*x for a,x in zip(costs,values))
            key=P*cost+sum(w*x for w,x in zip(weights,values))-shift
            cuts[key]+=multiplicity
            if real:
                truth[key]+=1
                valid[values]=cost
        targets=set(cuts)
        targets.update((-1,0,1<<len(out)))
        for _ in range(5): targets.add(rng.randrange(max(1,sum(map(abs,coeffs))+1)))
        queries=0
        first=None
        for target in sorted(targets):
            actual=exact_count(c.nvars,c.clauses+literal_constraints(out,target))
            assert actual==cuts[target],(trial,args.mode,target,actual,cuts[target])
            assert actual%2==truth[target]%2
            if actual%2 and first is None: first=target
            queries+=1
        found_cost=None
        if first is not None:
            fixed=[]
            values=[None]*p
            order=list(range(p));rng.shuffle(order)
            targetclauses=literal_constraints(out,first)
            for i in order:
                zero=exact_count(c.nvars,c.clauses+targetclauses+fixed+[(-bits[i],)])
                value=0 if zero%2 else 1
                values[i]=value
                fixed.append((bits[i] if value else -bits[i],))
                queries+=1
            assert tuple(values) in valid
            assert exact_count(c.nvars,c.clauses+targetclauses+fixed)%2==1
            found_cost=valid[tuple(values)]
            queries+=1
        optimum=min(valid.values(),default=None)
        if truth:
            unique_min=truth[min(truth)]==1
            if unique_min: assert found_cost==optimum
        else:
            unique_min=False
            assert first is None
        row={"trial":trial,"root":root,"edges":edges,"objects":len(objects),
             "valid_objects":len(valid),"queries":queries,"weight_layers":len(targets),
             "optimal_cost":optimum,"found_cost":found_cost,"unique_minimum":unique_min,
             "N":c.nvars,"M":len(c.clauses)}
        rows.append(row)
        with open(args.progress,"a") as f:
            f.write(json.dumps({"completed_trial":trial,"elapsed_seconds":time.monotonic()-begin,
                                **row},sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","args":vars(args),"trials":rows,
                      "elapsed_seconds":time.monotonic()-begin},sort_keys=True))


if __name__=="__main__": main()
