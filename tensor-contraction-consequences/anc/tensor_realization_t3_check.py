import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))

#!/usr/bin/env python3
"""A three-party, two-bit protocol instance with four-leaf equality trees (Section 3.2).

Imports only the generic sparse factor data type and contraction routine.
The party predicates are explicit tables rather than arithmetic-gate decompositions.
"""
import hashlib
import itertools
import json
import time
from collections import Counter, defaultdict, deque
from pathlib import Path

from tensor_realization_check import Factor, bits, contract, number


def main():
    started = time.monotonic()
    t, raw_bits, width, target, prime, r = 3, 2, 2, 3, 5, 3
    C = t * r + t
    transcripts = list(itertools.product((0, 1), repeat=C))

    def referee(tr):
        # Public, total computation on arbitrary transcripts, not executions.
        residues = [number(tr[i*r:(i+1)*r]) for i in range(t)]
        valid = all(x < prime for x in residues)
        high_target, low_target = divmod(target, 2)
        h = (high_target - sum(residues)) % prime
        low_branch = h < t
        next_target = low_target + 2*h if low_branch else high_target
        stopped = next_target < 0 or next_target >= t
        final = tr[t*r:]
        if stopped:
            valid = valid and all(x == 0 for x in final)
            output = int(next_target < 0)
        else:
            output = int(sum(final) > next_target)
        return valid, low_branch, stopped, output

    analyses = {tr: referee(tr) for tr in transcripts}
    factors = []
    for party in range(t):
        scope = tuple(f"in{party}_{k}" for k in range(raw_bits)) + tuple(f"tr{k}_p{party}" for k in range(C))
        rows = {}
        for raw in range(1 << raw_bits):
            high, low = divmod(raw, 2)
            for tr in transcripts:
                _, low_branch, stopped, _ = analyses[tr]
                expected_message = bits(high % prime, r)
                expected_final = 0 if stopped else (low if low_branch else high)
                if tr[party*r:(party+1)*r] == expected_message and tr[t*r+party] == expected_final:
                    rows[bits(raw, raw_bits) + tr] = 1
        factors.append(Factor(f"party{party}", scope, rows))
    factors.append(Factor("referee", tuple(f"tr{k}_ref" for k in range(C)) + ("out",), {tr+(a[3],): 1 for tr, a in analyses.items() if a[0]}))
    equality3 = {(0, 0, 0): 1, (1, 1, 1): 1}
    for k in range(C):
        # Four leaves: p0, p1, p2, referee. One genuine internal tree edge.
        factors.append(Factor(f"copy{k}_left", (f"tr{k}_p0", f"tr{k}_p1", f"tr{k}_middle"), equality3))
        factors.append(Factor(f"copy{k}_right", (f"tr{k}_middle", f"tr{k}_p2", f"tr{k}_ref"), equality3))
    external = [f"in{i}_{k}" for i in range(t) for k in range(raw_bits)] + ["out"]
    for v in external:
        factors.append(Factor(f"terminal_{v}", (v,), {(0,): 1, (1,): 1}))
    incidence = defaultdict(list)
    for f in factors:
        assert len(set(f.scope)) == len(f.scope)
        assert all(value == 1 for value in f.rows.values())
        for v in f.scope:
            incidence[v].append(f.name)
    assert all(len(endpoints) == 2 for endpoints in incidence.values())
    original_M, original_V = len(incidence), len(factors)
    subdivided = [Factor(f.name, tuple(f"{v}@{f.name}" for v in f.scope), f.rows) for f in factors]
    for v, (a, b) in incidence.items():
        subdivided.append(Factor(f"sub_{v}", (f"{v}@{a}", f"{v}@{b}"), {(0, 0): 1, (1, 1): 1}))
    edges = defaultdict(list)
    for f in subdivided:
        for v in f.scope:
            edges[v].append(f.name)
    assert all(len(endpoints) == 2 for endpoints in edges.values())
    adjacency = defaultdict(list)
    for a, b in edges.values():
        adjacency[a].append(b)
        adjacency[b].append(a)
    colors = {}
    for root in adjacency:
        if root in colors:
            continue
        colors[root] = 0
        queue = deque([root])
        while queue:
            vertex = queue.popleft()
            for nxt in adjacency[vertex]:
                if nxt in colors:
                    assert colors[nxt] != colors[vertex]
                else:
                    colors[nxt] = 1 - colors[vertex]
                    queue.append(nxt)
    keep = tuple(f"{v}@terminal_{v}" for v in external)
    joint, elimination = contract(subdivided, keep)
    histogram, traces, accepts = Counter(), Counter(), 0
    for raw in itertools.product(range(4), repeat=t):
        # Independent direct protocol execution, never used for tensor generation.
        high = [x // 2 for x in raw]
        low = [x % 2 for x in raw]
        h = (target // 2 - sum(x % prime for x in high)) % prime
        if h < t:
            xs, next_target, trace = low, target % 2 + 2*h, "LOW"
        else:
            xs, next_target, trace = high, target // 2, "HIGH"
        if next_target < 0 or next_target >= t:
            expected, trace = int(next_target < 0), trace+"/STOP"
        else:
            expected = int(sum(xs) > next_target)
        assert expected == int(sum(raw) > target)
        traces[trace] += 1
        prefix = sum((bits(x, raw_bits) for x in raw), ())
        masses = [joint.get(prefix+(y,), 0) for y in (0, 1)]
        assert masses[expected] == 1 and masses[1-expected] == 0
        histogram[sum(masses)] += 1
        accepts += expected
    assert len(joint) == 64
    pinned = sum(weight for row, weight in joint.items() if row[-1] == 1)
    assert pinned == accepts
    assert original_M == 5*C+t*raw_bits+1
    result = {
        "status": "PASS", "scope": "one finite three-party protocol realization; transcript tables, without arithmetic decomposition",
        "parameters": {"t": t, "S": t, "raw_bits_per_party": raw_bits, "B_prime": width, "target": target, "prime_seed": [prime], "transcript_bits": C},
        "graph": {"original_vertices": original_V, "original_edges": original_M, "vertices": len(subdivided), "edges": len(edges), "max_degree": max(len(f.scope) for f in subdivided), "every_edge_has_exactly_two_ports": True, "bipartite": True, "entries_0_or_1": True, "copy_tree_leaves_per_transcript_bit": 4, "copy_tree_internal_edges_per_transcript_bit": 1},
        "input_assignments": 64, "internal_extension_counts_histogram": dict(histogram), "joint_marginal_matches_direct_protocol": True,
        "output_one_pin_contraction": pinned, "direct_protocol_accepting_inputs": accepts, "trace_histogram": dict(traces),
        "contraction": elimination, "seconds": round(time.monotonic()-started, 4),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "generic_engine_sha256": hashlib.sha256(Path(__file__).with_name("tensor_realization_check.py").read_bytes()).hexdigest(),
    }
    path = Path(__file__).resolve().parent / "results" / "tensor_realization_check_t3.json"
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    _detail_print(json.dumps(result, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
