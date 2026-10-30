"""Exact minimal counterexamples to omissions or stronger interpretations."""
import json
from itertools import combinations
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_cnf_reference import exact_count,literal_constraints,reference_graph
from cnf_circuits import Circuit,cut_count_cnf,connected_object_cnf

start=time.monotonic()
rows={}

# Instantiate exactly the written construction directed-Steiner conditions at n=2,
# root 0, terminal 1, no arcs. Nonroot outdegree=1 if selected forces u_1=0.
c=Circuit()
u=[c.new_var(primary=True) for _ in range(2)]
col=[c.new_var(primary=True) for _ in range(2)]
c.fix(u[0],1);c.fix(u[1],0);c.fix(col[0],0)
for x,y in zip(u,col):c.clauses.append((x,-y))
unrepaired=exact_count(c.nvars,c.clauses)
repaired=exact_count(c.nvars,c.clauses+[(u[1],)])
assert (unrepaired,repaired)==(1,0)
rows["directed_steiner_terminal_selection"]={"n":2,"edges":[],"root":0,"terminals":[1],
    "written_conditions_count":unrepaired,"after_terminal_unit_count":repaired,"true_feasible":False}

# Root pin is necessary: one triangle has one HC, but two unpinned cuts.
c,_=cut_count_cnf(3,[(0,1),(1,2),(0,2)])
pin=(-c.names["colour_0"],)
assert exact_count(c.nvars,c.clauses)==1
no_root=[cl for cl in c.clauses if cl!=pin]
assert exact_count(c.nvars,no_root)==2
rows["missing_root_pin"]={"pinned":1,"unpinned":2,"true_hc":1}

# Forcing same colors along unselected input edges wrongly joins components.
edges=[(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(2,3)]
c,_=cut_count_cnf(6,edges)
correct=exact_count(c.nvars,c.clauses)
bad=list(c.clauses)
for i,(a,b) in enumerate(edges):
    x,ca,cb=c.names[f"edge_{i}"],c.names[f"colour_{a}"],c.names[f"colour_{b}"]
    bad.remove((-x,-ca,cb));bad.remove((-x,ca,-cb))
    bad.extend([(-ca,cb),(ca,-cb)])
unguarded=exact_count(c.nvars,bad)
assert (correct,unguarded)==(2,1)
rows["unguarded_cut_edges"]={"correct_count":correct,"unguarded_count":unguarded,"true_hc":0}

# Isolating only U loses the two ways to mark the one-edge forest.
c=connected_object_cnf(2,[(0,1)],"fvs")
fixed=[(c.names[f"vertex_{i}"],) for i in range(2)]
assert exact_count(c.nvars,c.clauses+fixed)==2
bits=[c.names[f"vertex_{i}"] for i in range(2)]+[c.names[f"marker_{i}"] for i in range(2)]
out=c.weighted_sum(bits,[1,1,1,2])
layercounts={t:exact_count(c.nvars,c.clauses+fixed+literal_constraints(out,t)) for t in (3,4)}
assert layercounts=={3:1,4:1}
rows["fvs_marker_isolation"]={"U_only_count":2,"with_marker_weights_layers":layercounts}

# FVS must not inherit an unconditional root pin: a marker-free cycle dies
# through its two cuts, but an arbitrary extra pin turns that into one.
c=connected_object_cnf(3,[(0,1),(0,2),(1,2)],"fvs")
fixed=[(c.names[f"vertex_{i}"],) for i in range(3)]
fixed += [(-c.names[f"marker_{i}"],) for i in range(3)]
uncut=exact_count(c.nvars,c.clauses+fixed)
pinned=exact_count(c.nvars,c.clauses+fixed+[(-c.names["colour_0"],)])
assert (uncut,pinned)==(2,1)
rows["fvs_must_not_inherit_HC_root"]={"marker_free_triangle_count":uncut,
    "with_wrong_extra_root_pin_count":pinned,"true_forest":False}

# A legitimate failed-isolation run returns a valid but suboptimal TSP tour.
edges=list(combinations(range(4),2))
costs=[0 if e==(0,1) else 1 for e in edges]
W=2*len(edges);P=4*W+1
weights=[P*x+1 for x in costs]
cuts,hc,_=reference_graph(4,edges,weights)
c,out=cut_count_cnf(4,edges,weights)
counts={t:exact_count(c.nvars,c.clauses+literal_constraints(out,t)) for t in sorted(hc)}
assert counts==dict(cuts)=={3*P+4:2,4*P+4:1}
rows["optimization_can_return_suboptimal"]={"graph":"K4","edge_costs":costs,"isolation_weights":[1]*6,
    "legal_weight_range":[1,W],"P":P,"layer_counts":counts,"optimum":3,
    "first_odd_layer_cost":4,"first_odd_layer_is_a_true_tour":True}
print(json.dumps({"status":"PASS","counterexamples":rows,"elapsed_seconds":time.monotonic()-start},sort_keys=True))
