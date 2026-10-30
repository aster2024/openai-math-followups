"""Literal-level unique-extension tests crossing the default radix boundary."""
import argparse
import gc
import json
import os
from pathlib import Path
import random
import resource
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_cnf_reference import exact_count,literal_constraints
from cnf_circuits import Circuit

ap=argparse.ArgumentParser()
ap.add_argument("--p",type=int,required=True)
ap.add_argument("--pattern",choices=("random","max","zero_mix"),default="random")
args=ap.parse_args()
assert os.getpriority(os.PRIO_PROCESS,0)>=19
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2))
begin=time.monotonic()
rng=random.Random(10301020+args.p)
p=args.p
weights=[rng.randrange((p+2)**4+1) for _ in range(p)]
if args.pattern=="max":weights=[(1<<((p+2)**4).bit_length())-1]*p
if args.pattern=="zero_mix":weights=[0 if i%2 else w for i,w in enumerate(weights)]
negative=[rng.randrange(2) for _ in range(p)]
c=Circuit()
xs=[c.new_var(primary=True) for _ in range(p)]
out=c.weighted_sum([-x if neg else x for x,neg in zip(xs,negative)],weights)
assert max(map(len,c.clauses))<=3
queries=0
rows=[]
for name,values in (("zeros",[0]*p),("ones",[1]*p),("alternating",[i%2 for i in range(p)]),
                    ("random",[rng.randrange(2) for _ in range(p)])):
    clauses=c.clauses+[(x if v else -x,) for x,v in zip(xs,values)]
    expected=sum(w*(v^neg) for w,v,neg in zip(weights,values,negative))
    assert exact_count(c.nvars,clauses+literal_constraints(out,expected))==1
    gc.collect()
    assert exact_count(c.nvars,clauses+literal_constraints(out,expected^1))==0
    gc.collect()
    queries+=2
    rows.append({"assignment":name,"expected_sum":expected,"extensions":1,"wrong_output_extensions":0})
print(json.dumps({"status":"PASS","args":vars(args),"N":c.nvars,"M":len(c.clauses),
                  "arithmetic":c.stats["weighted_sums"],"queries":queries,"cases":rows,
                  "elapsed_seconds":time.monotonic()-begin},sort_keys=True))
