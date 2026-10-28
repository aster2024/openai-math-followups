#!/usr/bin/env python3
"""Finite protocol tensor-network check (Section 3.2); generic exact sparse elimination, no NumPy.

This is not an asymptotic proof or an implementation of H_TC. Every original
tensor is 0/1. The eliminated factors have nonnegative integer entries.
The network is built from locally checked relation tables, never from a list
of the complete protocol executions. Direct executions are a separate oracle.
The arithmetic-gate realization is deliberately not implemented here.
"""
from __future__ import annotations
import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))


import hashlib
import itertools
import json
import time
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


def bits(n, width):
    return tuple((n >> i) & 1 for i in range(width))


def number(xs):
    return sum(x << i for i, x in enumerate(xs))


@dataclass
class Factor:
    name: str
    scope: tuple[str, ...]
    rows: dict[tuple[int, ...], int]


def multiply(a, b):
    """Generic natural join of sparse factor tables, multiplying weights."""
    common = tuple(v for v in a.scope if v in b.scope)
    ai = tuple(a.scope.index(v) for v in common)
    bi = tuple(b.scope.index(v) for v in common)
    extra = tuple(i for i, v in enumerate(b.scope) if v not in a.scope)
    index = defaultdict(list)
    for row, weight in b.rows.items():
        index[tuple(row[i] for i in bi)].append((row, weight))
    out = {}
    for ar, av in a.rows.items():
        for br, bv in index.get(tuple(ar[i] for i in ai), ()):
            row = ar + tuple(br[i] for i in extra)
            out[row] = out.get(row, 0) + av * bv
    return Factor("product", a.scope + tuple(b.scope[i] for i in extra), out)


def sum_out(factor, variable):
    i = factor.scope.index(variable)
    out = defaultdict(int)
    for row, weight in factor.rows.items():
        out[row[:i] + row[i + 1:]] += weight
    return Factor("sum", factor.scope[:i] + factor.scope[i + 1:], dict(out))


def contract(factors, keep):
    """Exact variable elimination, preserving the requested joint marginal."""
    factors = list(factors)
    eliminate = set().union(*(set(f.scope) for f in factors)) - set(keep)
    peak = max(len(f.rows) for f in factors)
    steps = 0
    while eliminate:
        choices = []
        for v in eliminate:
            neighbors = [f for f in factors if v in f.scope]
            union = set().union(*(set(f.scope) for f in neighbors))
            choices.append((len(union), sum(len(f.rows) for f in neighbors), v, neighbors))
        _, _, variable, neighbors = min(choices, key=lambda z: z[:3])
        remove = {id(f) for f in neighbors}
        factors = [f for f in factors if id(f) not in remove]
        product = neighbors[0]
        for f in neighbors[1:]:
            product = multiply(product, f)
            peak = max(peak, len(product.rows))
        factors.append(sum_out(product, variable))
        eliminate.remove(variable)
        steps += 1
    result = factors[0]
    for f in factors[1:]:
        result = multiply(result, f)
        peak = max(peak, len(result.rows))
    indices = [result.scope.index(v) for v in keep]
    rows = {tuple(row[i] for i in indices): w for row, w in result.rows.items()}
    return rows, {"elimination_steps": steps, "peak_nonzero_table_rows": peak}


class Protocol:
    def __init__(self, raw_bits, width, target, primes, dropped_padding_bit=None):
        self.raw_bits = raw_bits
        self.width = width
        self.target = target
        self.primes = tuple(primes)
        self.r = max(p.bit_length() for p in primes)
        self.J = width.bit_length() - 1
        self.C = 2 * self.J * self.r + 2
        self.drop = dropped_padding_bit
        assert width in (2, 4) and raw_bits in (2, 4)
        assert raw_bits <= width and len(primes) == self.J
        assert all(p in (3, 5) for p in primes)  # S=t=2; p>S.

    def value(self, raw):
        # Explicit polynomial-time private-input map. No latent input bits.
        return raw

    def public_analysis(self, tr):
        """Referee computation using only transcript, target and fixed seed."""
        target, width = self.target, self.width
        frames, valid = [], True
        stopped, answer = False, None
        for j, p in enumerate(self.primes):
            if not stopped and (target < 0 or target >= 2 * ((1 << width) - 1)):
                stopped, answer = True, int(target < 0)
            start = 2 * j * self.r
            sent = [number(tr[start + i * self.r:start + (i + 1) * self.r]) for i in range(2)]
            if stopped:
                for k in range(start, start + 2 * self.r):
                    if k != self.drop and tr[k]:
                        valid = False
                frames.append((width, None, True))
                continue
            if any(x >= p for x in sent):
                valid = False
            half = width // 2
            high_target, low_target = divmod(target, 1 << half)
            h = (high_target - sum(sent)) % p
            branch = h if h < 2 else None
            frames.append((width, branch, False))
            target = low_target + branch * (1 << half) if branch is not None else high_target
            width = half
        # Range check applies at the final one-bit stage as well.
        if not stopped and (target < 0 or target >= 2 * ((1 << width) - 1)):
            stopped, answer = True, int(target < 0)
        final_start = 2 * self.J * self.r
        if stopped:
            for k in range(final_start, self.C):
                if k != self.drop and tr[k]:
                    valid = False
        else:
            answer = int(sum(tr[final_start:]) > target)
        return valid, tuple(frames), stopped, answer

    def party_ok(self, party, raw, tr, analysis):
        _, frames, final_stopped, _ = analysis
        x = self.value(raw)
        for j, (width, branch, stopped) in enumerate(frames):
            start = 2 * j * self.r + party * self.r
            if stopped:
                expected = (0,) * self.r
            else:
                high, low = divmod(x, 1 << (width // 2))
                expected = bits(high % self.primes[j], self.r)
                x = low if branch is not None else high
            for offset, wanted in enumerate(expected):
                k = start + offset
                if not (stopped and k == self.drop) and tr[k] != wanted:
                    return False
        k = 2 * self.J * self.r + party
        wanted = 0 if final_stopped else x
        return (final_stopped and k == self.drop) or tr[k] == wanted

    def direct(self, x0, x1):
        """Separate execution oracle; not used to build any tensor entry."""
        xs, target, width = [self.value(x0), self.value(x1)], self.target, self.width
        tr, trace, stopped, answer = [], [], False, None
        for p in self.primes:
            if target < 0 or target >= 2 * ((1 << width) - 1):
                stopped, answer = True, int(target < 0)
            if stopped:
                tr.extend([0] * (2 * self.r))
                trace.append("STOP")
                continue
            half = width // 2
            hi = [x >> half for x in xs]
            lo = [x % (1 << half) for x in xs]
            target_hi, target_lo = divmod(target, 1 << half)
            residue = [x % p for x in hi]
            for x in residue:
                tr.extend(bits(x, self.r))
            h = (target_hi - sum(residue)) % p
            false_h = h < 2 and sum(hi) != target_hi - h
            if h < 2:
                trace.append("FALSE-h" if false_h else "LOW")
                xs, target = lo, target_lo + h * (1 << half)
            else:
                trace.append("HIGH")
                xs, target = hi, target_hi
            width = half
        if target < 0 or target >= 2 * ((1 << width) - 1):
            stopped, answer = True, int(target < 0)
        if stopped:
            tr.extend([0, 0])
        else:
            tr.extend(xs)
            answer = int(sum(xs) > target)
        return tuple(tr), answer, tuple(trace)


def network(protocol):
    """Protocol parties/referee + transcript equality trees + unary terminals.

    t=2 gives exactly three copies of every transcript bit, so its equality
    tree is one degree-three vertex. All original edges are subdivided once.
    """
    b, C = protocol.raw_bits, protocol.C
    transcripts = list(itertools.product((0, 1), repeat=C))
    analyses = {tr: protocol.public_analysis(tr) for tr in transcripts}
    factors = []
    for party in range(2):
        scope = tuple(f"in{party}_{k}" for k in range(b)) + tuple(f"tr{k}_p{party}" for k in range(C))
        rows = {}
        for raw in range(1 << b):
            for tr in transcripts:
                if protocol.party_ok(party, raw, tr, analyses[tr]):
                    rows[bits(raw, b) + tr] = 1
        factors.append(Factor(f"party{party}", scope, rows))
    referee_rows = {tr + (info[3],): 1 for tr, info in analyses.items() if info[0]}
    factors.append(Factor("referee", tuple(f"tr{k}_ref" for k in range(C)) + ("out",), referee_rows))
    for k in range(C):
        factors.append(Factor(f"copy{k}", (f"tr{k}_p0", f"tr{k}_p1", f"tr{k}_ref"), {(0, 0, 0): 1, (1, 1, 1): 1}))
    external = [f"in{party}_{k}" for party in range(2) for k in range(b)] + ["out"]
    for variable in external:
        factors.append(Factor(f"terminal_{variable}", (variable,), {(0,): 1, (1,): 1}))
    # Validate that the original objects are an edge network, not a hypergraph.
    incidence = defaultdict(list)
    for f in factors:
        assert len(f.scope) == len(set(f.scope))
        assert all(w in (0, 1) for w in f.rows.values())
        for v in f.scope:
            incidence[v].append(f.name)
    assert all(len(ports) == 2 for ports in incidence.values())
    original_M = len(incidence)
    original_V = len(factors)
    subdivided = []
    for f in factors:
        subdivided.append(Factor(f.name, tuple(f"{v}@{f.name}" for v in f.scope), f.rows))
    for v, (a, bname) in incidence.items():
        subdivided.append(Factor(f"sub_{v}", (f"{v}@{a}", f"{v}@{bname}"), {(0, 0): 1, (1, 1): 1}))
    keep = tuple(f"{v}@terminal_{v}" for v in external)
    subdiv_incidence = defaultdict(list)
    for f in subdivided:
        for v in f.scope:
            subdiv_incidence[v].append(f.name)
    assert all(len(ports) == 2 for ports in subdiv_incidence.values())
    adjacency = defaultdict(list)
    for a, bname in subdiv_incidence.values():
        adjacency[a].append(bname)
        adjacency[bname].append(a)
    coloring = {}
    for root in adjacency:
        if root in coloring:
            continue
        coloring[root] = 0
        queue = deque([root])
        while queue:
            a = queue.popleft()
            for nxt in adjacency[a]:
                if nxt in coloring:
                    assert coloring[nxt] != coloring[a]
                else:
                    coloring[nxt] = 1 - coloring[a]
                    queue.append(nxt)
    metrics = {
        "original_vertices": original_V,
        "original_edges": original_M,
        "vertices": len(subdivided),
        "edges": len(subdiv_incidence),
        "max_degree": max(len(f.scope) for f in subdivided),
        "every_edge_has_exactly_two_ports": True,
        "bipartite": True,
        "entries_0_or_1": True,
        "transcript_bits": C,
        "party_nonzero_rows": [len(f.rows) for f in factors[:2]],
        "referee_nonzero_rows": len(factors[2].rows),
    }
    assert metrics["edges"] == 2 * original_M
    assert metrics["vertices"] == original_V + original_M
    assert metrics["max_degree"] == max(protocol.raw_bits + C, C + 1, 3)
    return subdivided, keep, metrics


def check_case(label, raw_bits, width, target, primes, drop=None):
    start = time.monotonic()
    p = Protocol(raw_bits, width, target, primes, drop)
    factors, keep, metrics = network(p)
    joint, contraction = contract(factors, keep)
    traces, witness, wrong, accepted = Counter(), None, 0, 0
    per_input_counts = Counter()
    for x0, x1 in itertools.product(range(1 << raw_bits), repeat=2):
        _, y, trace = p.direct(x0, x1)
        accepted += y
        traces["/".join(trace)] += 1
        prefix = bits(x0, raw_bits) + bits(x1, raw_bits)
        masses = [joint.get(prefix + (z,), 0) for z in (0, 1)]
        per_input_counts[sum(masses)] += 1
        expected_mass = 2 if drop is not None else 1
        assert masses[y] == expected_mass and masses[1 - y] == 0, (label, x0, x1, masses, y)
        if y != int(p.value(x0) + p.value(x1) > target):
            wrong += 1
            if witness is None:
                witness = {"inputs": [x0, x1], "protocol_output": y, "true_comparison": 1-y, "trace": trace}
    assert len(joint) == (1 << (2 * raw_bits))
    pinned_count = sum(w for row, w in joint.items() if row[-1] == 1)
    assert pinned_count == accepted * (2 if drop is not None else 1)
    return {
        "label": label, "raw_bits_per_party": raw_bits, "B_prime": width,
        "target": target, "prime_seed": primes, "dropped_padding_bit": drop,
        "graph": metrics, "contraction": contraction,
        "input_assignments": 1 << (2 * raw_bits),
        "internal_extension_counts_histogram": dict(per_input_counts),
        "joint_marginal_matches_direct_protocol": True,
        "output_one_pin_contraction": pinned_count,
        "direct_protocol_accepting_inputs": accepted,
        "trace_histogram": dict(traces),
        "protocol_comparison_errors_for_fixed_seed": wrong,
        "comparison_error_witness": witness,
        "seconds": round(time.monotonic() - start, 4),
    }


def main():
    started = time.time()
    # Fixed before running. The suite is deliberately tiny, not a random search.
    cases = [
        ("b2_negative_early_stop", 2, 2, -1, [3]),
        ("b2_above_max_early_stop", 2, 2, 6, [3]),
        ("b2_interior", 2, 2, 2, [3]),
        ("b4_bad_seed", 4, 4, 0, [3, 3]),
        ("b4_two_layers", 4, 4, 9, [3, 3]),
        ("b4_mixed_primes", 4, 4, 15, [3, 5]),
        ("b4_restricted_private_domain", 2, 4, 3, [3, 3]),
        ("b2_one_padding_constraint_deleted", 2, 2, -1, [3], 0),
    ]
    results = []
    for args in cases:
        result = check_case(*args)
        results.append(result)
        _detail_print(json.dumps({"case": result["label"], "status": "PASS", "seconds": result["seconds"]}), flush=True)
    summary = {
        "status": "PASS", "method": "explicit Boolean tensors; every edge subdivided; generic sparse factor variable elimination",
        "scope": "finite protocol tensor realization (Section 3.2); transcript tables, without arithmetic decomposition",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "run_start_unix": started, "total_seconds": round(time.time() - started, 4),
        "case_count": len(results), "results": results,
    }
    out = Path(__file__).resolve().parent / "results" / "tensor_realization_check.json"
    out.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")
    _detail_print(json.dumps({"summary": out.name, "status": "PASS", "total_seconds": summary["total_seconds"]}), flush=True)


if __name__ == "__main__":
    main()

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
