"""Check directed Steiner terminal selection; compare exact cuts and true arborescences.

Terminal selection is imposed by explicit unit clauses.
"""
import argparse
from itertools import combinations
import json
import os
from pathlib import Path
import resource
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_cnf_reference import exact_count
from cnf_circuits import Circuit

def formula(n,arcs,root,terminals,repair=True):
    c=Circuit()
    u=[c.new_var(primary=True) for _ in range(n)]
    x=[c.new_var(primary=True) for _ in arcs]
    col=[c.new_var(primary=True) for _ in range(n)]
    c.fix(u[root],1);c.fix(col[root],0)
    if repair:
        for v in terminals:c.fix(u[v],1)
    outgoing=[[] for _ in range(n)]
    for (a,b),bit in zip(arcs,x):
        outgoing[a].append(bit)
        c.clauses.extend([(-bit,u[a]),(-bit,u[b]),(-bit,-col[a],col[b]),
                          (-bit,col[a],-col[b])])
    for v in range(n):
        c.clauses.append((u[v],-col[v]))
        word=c.popcount(outgoing[v])
        if v==root:c.equal_constant(word,0)
        else:
            c.clauses.extend([(-word[0],u[v]),(word[0],-u[v])])
            for high in word[1:]:c.fix(high,0)
    return c

def reference(n,arcs,root,terminals):
    # Independently enumerate vertex sets and edge subsets, then test both
    # functional-outdegree conditions and actual paths to the root.
    cuts=true=0
    for U in range(1<<n):
        if U>>root&1==0 or any(U>>v&1==0 for v in terminals):continue
        inside=[e for e in arcs if U>>e[0]&1 and U>>e[1]&1]
        for F in combinations(inside,U.bit_count()-1):
            succ={}
            ok=True
            for a,b in F:
                if a==root or a in succ:ok=False;break
                succ[a]=b
            if not ok or any(v!=root and U>>v&1 and v not in succ for v in range(n)):continue
            blocks=[{v} for v in range(n) if U>>v&1]
            for a,b in F:
                ia=next(i for i,s in enumerate(blocks) if a in s)
                ib=next(i for i,s in enumerate(blocks) if b in s)
                if ia!=ib:blocks[ia]|=blocks[ib];del blocks[ib]
            cuts+=1<<(len(blocks)-1)
            reaches=True
            for v in range(n):
                if not U>>v&1:continue
                seen=set()
                while v!=root:
                    if v in seen or v not in succ:reaches=False;break
                    seen.add(v);v=succ[v]
                if not reaches:break
            true+=reaches
    return cuts,true

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--stop",type=int,default=512)
    ap.add_argument("--progress",required=True)
    args=ap.parse_args()
    assert os.getpriority(os.PRIO_PROCESS,0)>=19
    resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2))
    begin=time.monotonic()
    n=4;root=0;possible=[(i,j) for i in range(n) for j in range(n) if i!=j]
    stop=min(args.stop,1<<len(possible))
    queries=graphs=bad_original=0
    totalcuts=totaltrue=0
    for mask in range(args.start,stop):
        arcs=[e for i,e in enumerate(possible) if mask>>i&1]
        for Tmask in range(1,8):
            terminals=[v for v in (1,2,3) if Tmask>>(v-1)&1]
            c=formula(n,arcs,root,terminals)
            actual=exact_count(c.nvars,c.clauses)
            cuts,true=reference(n,arcs,root,terminals)
            assert actual==cuts,(mask,terminals,actual,cuts)
            assert actual%2==true%2
            assert max(map(len,c.clauses))<=3
            queries+=1;totalcuts+=cuts;totaltrue+=true
        # The omitted-terminal construction is always feasible as an ordinary
        # CNF, even on instances with no terminal-to-root path.
        graphs+=1
        if (mask+1)%32==0:
            with open(args.progress,"a") as f:
                f.write(json.dumps({"next_mask":mask+1,"graphs":graphs,"queries":queries,
                                    "elapsed_seconds":time.monotonic()-begin})+"\n")
    print(json.dumps({"status":"PASS","args":vars(args),"graphs":graphs,"queries":queries,
                      "start":args.start,"stop":stop,"sum_cut_counts":totalcuts,
                      "sum_true_arborescences":totaltrue,"terminal_sets_per_graph":7,
                      "elapsed_seconds":time.monotonic()-begin},sort_keys=True))

if __name__=="__main__":main()
