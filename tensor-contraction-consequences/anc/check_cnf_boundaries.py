"""Low-precision truncation, v2(n), and raw support-cutoff witnesses."""
import argparse
import json
import os
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_cnf_modular import instance,inventory,matching_supports,coefficient
from check_cnf_reference import exact_count
from cnf_circuits import determinant_hc_cnf,colour_cut_cnf

assert os.getpriority(os.PRIO_PROCESS,0)>=19
ap=argparse.ArgumentParser()
ap.add_argument("--start-case",type=int,default=0)
ap.add_argument("--stop-case",type=int,default=8)
ap.add_argument("--skip-family",action="store_true")
args=ap.parse_args()
start=time.monotonic()
results=[]
queries=0
cases=(("k6",1),("k6",2),("k33",1),("k33",2),
       ("triangles_bridge",2),("three_triangles",2),("c9",1),("c8",1))
for case,b in cases[args.start_case:args.stop_case]:
    n,edges=instance(case)
    positions=[(v,v) for v in range(n)]+[a for u,v in edges for a in ((u,v),(v,u))]
    ref,hc,factors,signed=inventory(n,edges,positions)
    h=(n&-n).bit_length()-1;t=b+h;mod=1<<t
    c,_=determinant_hc_cnf(n,edges,with_sign=False)
    z=[c.names[f"position_{u}_{v}"] for u,v in positions]
    total=0;nonzero=0
    supports=matching_supports(n,positions,min(n,2*t-2))
    for S in supports:
        coef=coefficient([positions[i] for i in S])
        assert coef%(1<<((len(S)+1)//2))==0
        if coef%mod==0:continue
        bits=sum(1<<i for i in S)
        expected=sum(weight for support,weight in ref.items() if support&bits==bits)
        actual=exact_count(c.nvars,c.clauses+[(z[i],) for i in S])
        assert actual==expected
        total=(total+coef*actual)%mod
        queries+=1;nonzero+=1
    assert total==signed%mod and total%(1<<h)==0
    answer=((total>>h)*pow(n>>h,-1,1<<b))%(1<<b)
    assert answer==hc%(1<<b)
    results.append({"case":case,"n":n,"b":b,"h":h,"t":t,"cutoff":2*t-2,
                    "supports":len(supports),"queries":nonzero,"true_hc":hc,"residue":answer})

sharp=[]
for r in range(1,6):
    S=[(2*i,2*i+1) for i in range(r)]+[(2*i+1,2*i) for i in range(r)]
    coef=coefficient(S)
    assert coef==1<<r
    sharp.append({"r":r,"support_size":2*r,"coefficient":coef,
                  "nonzero_modulus":1<<(r+1)})

if args.skip_family:
    print(json.dumps({"status":"PASS","args":vars(args),"low_precision":results,
                      "queries":queries,"sharp_cutoff":sharp,
                      "elapsed_seconds":time.monotonic()-start},sort_keys=True))
    sys.exit(0)

# An explicit sparse positive instance with zero small modulus.
r=3;n=4*r
edges=[]
for block in range(r):
    edges += [(4*block+i,4*block+j) for i in range(4) for j in range(i+1,4)]
    edges.append((4*block+1,4*((block+1)%r)))
c=colour_cut_cnf(n,edges,3)
count=exact_count(c.nvars,c.clauses)
assert count==3**r*8**(r-1)+2**r and count%8==0
# Independent DFS HC count; root fixed, reverse orientation quotiented.
adj=[set() for _ in range(n)]
for u,v in edges:adj[u].add(v);adj[v].add(u)
def paths(path,seen):
    if len(path)==n:return int(0 in adj[path[-1]] and path[1]<path[-1])
    return sum(paths(path+[v],seen|{v}) for v in adj[path[-1]] if v not in seen)
hc=paths([0],{0})
assert hc==8
print(json.dumps({"status":"PASS","args":vars(args),"low_precision":results,"queries":queries,
                  "sharp_cutoff":sharp,"positive_zero_residue":{"n":n,"m":len(edges),
                   "hc":hc,"colour_cnf_count":count,"modulus":8,"residue":count%8},
                  "elapsed_seconds":time.monotonic()-start},sort_keys=True))
