import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

"""Independent brute-force check of the small exact contraction test engine."""
import hashlib
import itertools
import json
import random
from collections import defaultdict
from pathlib import Path
from tensor_realization_check import Factor, contract

rng = random.Random(10282026)
cases = 300
assignments = 0
for case in range(cases):
    n = 1 + case % 7
    variables = [f"x{i}" for i in range(n)]
    # Unary factors make every declared bit occur, including disconnected ones.
    factors = [Factor(f"free{i}", (v,), {(0,): 1, (1,): 1})
               for i, v in enumerate(variables)]
    for j in range(1 + case % 5):
        scope = tuple(rng.sample(variables, rng.randrange(min(n, 4)+1)))
        rows = {row: rng.randrange(3) for row in itertools.product((0, 1), repeat=len(scope))}
        factors.append(Factor(f"f{j}", scope, {r: w for r, w in rows.items() if w}))
    keep = tuple(rng.sample(variables, case % (n+1)))
    expected = defaultdict(int)
    for assignment in itertools.product((0, 1), repeat=n):
        valuation = dict(zip(variables, assignment))
        weight = 1
        for factor in factors:
            weight *= factor.rows.get(tuple(valuation[v] for v in factor.scope), 0)
        if weight:
            expected[tuple(valuation[v] for v in keep)] += weight
        assignments += 1
    obtained, _ = contract(factors, keep)
    assert obtained == dict(expected), (case, obtained, dict(expected))

root = Path(__file__).resolve().parent
result = dict(status="PASS", cases=cases, brute_force_assignments=assignments,
              seed=10282026, scope="small weighted factor graphs, scalar and disconnected factors, arbitrary retained subsets",
              engine_sha256=hashlib.sha256((root/"tensor_realization_check.py").read_bytes()).hexdigest())
(root/"results/contraction_engine_check.json").write_text(json.dumps(result, indent=2)+"\n")
_detail_print(json.dumps(result))

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
