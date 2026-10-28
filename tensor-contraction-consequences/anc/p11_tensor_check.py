"""Explicit small arithmetic-gate protocol networks (Section 3.2), including fan-in-two modular arithmetic.

The factors are generated locally from arbitrary public histories. The final
joint marginal is obtained by generic exact factor elimination, not by direct
execution of the protocol. The computation checks finite instances of the reduction.
"""
from __future__ import annotations
import sys as _local_sys
from pathlib import Path as _local_Path
_local_sys.path.insert(0, str(_local_Path(__file__).resolve().parent))
import builtins as _builtins
_detail_lines=[]
def _detail_print(*a, **kw):
    _detail_lines.append(' '.join(map(str,a)))


import argparse
import hashlib
import itertools
import json
import time
from collections import Counter, defaultdict, deque
from pathlib import Path

from tensor_realization_check import Factor, bits, contract, number


class Gates:
    def __init__(self):
        self.factors = [Factor("zero", ("zero",), {(0,): 1}),
                        Factor("one", ("one",), {(1,): 1})]
        self.serial = 0
        self.gate_count = 0
        self.input_ports = 0

    def fresh(self, label):
        self.serial += 1
        return f"{label}_{self.serial}"

    def gate(self, kind, *parents):
        assert len(parents) in (1, 2)
        output = self.fresh(kind)
        # Repeated parents are one logical signal. Preserve separate inputs
        # in the gate function, but do not put duplicate variables in a scope.
        unique = tuple(dict.fromkeys(parents))
        rows = {}
        for values in itertools.product((0, 1), repeat=len(unique)):
            mapping = dict(zip(unique, values))
            xs = [mapping[x] for x in parents]
            value = {"xor": lambda: xs[0] ^ xs[1],
                     "and": lambda: xs[0] & xs[1],
                     "or": lambda: xs[0] | xs[1],
                     "not": lambda: 1-xs[0]}[kind]()
            rows[values + (value,)] = 1
        self.factors.append(Factor(output, unique + (output,), rows))
        self.gate_count += 1
        self.input_ports += len(parents)
        return output

    def constant(self, value, width):
        return ["one" if x else "zero" for x in bits(value, width)]

    def add(self, a, b, carry="zero"):
        assert len(a) == len(b)
        result = []
        for x, y in zip(a, b):
            xy = self.gate("xor", x, y)
            result.append(self.gate("xor", xy, carry))
            carry = self.gate("or", self.gate("and", x, y),
                              self.gate("and", xy, carry))
        return result, carry

    def mux(self, selector, yes, no):
        inv = self.gate("not", selector)
        return [self.gate("or", self.gate("and", selector, a),
                          self.gate("and", inv, b)) for a, b in zip(yes, no)]

    def sum_mod(self, a, b, p):
        r = len(a)
        low, carry = self.add(a, b)
        full = low + [carry]
        diff, ge = self.add(full, self.constant((1 << (r+1))-1-p, r+1), "one")
        return self.mux(ge, diff[:r], full[:r])

    def difference_mod(self, a, b, p):
        r = len(a)
        neg_b = [self.gate("not", x) for x in b]
        diff, ge = self.add(a, neg_b, "one")
        corrected, _ = self.add(diff, self.constant(p, r))
        return self.mux(ge, diff, corrected)

    def branch(self, d, t, stop, ell):
        r = len(d)
        _, ge = self.add(d, self.constant((1 << r)-1-t, r), "one")
        chosen = self.mux(ge, self.constant(t, ell), d[:ell])
        return self.mux(stop, self.constant(0, ell), chosen)


def state(t, B, T, history):
    """Public state after a prescribed prefix, including canonical stops."""
    width, target, stopped, answer = B, T, False, None
    for h in history:
        if h > t:
            return None
        if not stopped and (target < 0 or target >= t*((1 << width)-1)):
            stopped, answer = True, int(target < 0)
        if stopped:
            if h != 0:
                return None
            continue
        half = width//2
        th, tl = divmod(target, 1 << half)
        target = tl + h*(1 << half) if h < t else th
        width = half
    if not stopped and (target < 0 or target >= t*((1 << width)-1)):
        stopped, answer = True, int(target < 0)
    return width, target, stopped, answer


def equality_tree(names, label):
    """One external edge per occurrence, arity at most three."""
    if len(names) == 1:
        return [Factor(f"free_{label}", tuple(names), {(0,): 1, (1,): 1})]
    if len(names) == 2:
        return [Factor(f"eq_{label}", tuple(names), {(0, 0): 1, (1, 1): 1})]
    rows = {(0, 0, 0): 1, (1, 1, 1): 1}
    out, pending = [], list(names)
    i = 0
    while len(pending) > 3:
        a, b, *remaining = pending
        middle = f"copy_internal_{label}_{i}"
        out.append(Factor(f"copy_{label}_{i}", (a, b, middle), rows))
        pending, i = [middle] + remaining, i+1
    out.append(Factor(f"copy_{label}_{i}", tuple(pending), rows))
    return out


def to_bipartite(factors, exposed):
    factors = list(factors)
    for v in exposed:
        factors.append(Factor(f"terminal_{v}", (v,), {(0,): 1, (1,): 1}))
    occurrences, local, terminals = defaultdict(list), [], {}
    for i, f in enumerate(factors):
        assert len(f.scope) == len(set(f.scope))
        ports = tuple(f"port_{i}_{k}" for k in range(len(f.scope)))
        local.append(Factor(f.name, ports, f.rows))
        for v, port in zip(f.scope, ports):
            occurrences[v].append(port)
            if f.name == f"terminal_{v}":
                terminals[v] = (port, f.name)
    for v, names in occurrences.items():
        local.extend(equality_tree(names, v))
    incidence = defaultdict(list)
    for f in local:
        for edge in f.scope:
            incidence[edge].append(f.name)
    assert all(len(v) == 2 for v in incidence.values())
    subdivided = [Factor(f.name, tuple(f"{v}@{f.name}" for v in f.scope), f.rows) for f in local]
    for v, (a, b) in incidence.items():
        subdivided.append(Factor(f"sub_{v}", (f"{v}@{a}", f"{v}@{b}"), {(0, 0): 1, (1, 1): 1}))
    adjacency, final_edges = defaultdict(list), defaultdict(list)
    for f in subdivided:
        assert all(w == 1 for w in f.rows.values())
        for edge in f.scope:
            final_edges[edge].append(f.name)
    for ends in final_edges.values():
        assert len(ends) == 2
        a, b = ends
        adjacency[a].append(b)
        adjacency[b].append(a)
    color = {}
    for start in adjacency:
        if start in color:
            continue
        color[start] = 0
        todo = deque([start])
        while todo:
            v = todo.popleft()
            for u in adjacency[v]:
                if u in color:
                    assert color[v] != color[u]
                else:
                    color[u] = 1-color[v]
                    todo.append(u)
    keep = tuple(f"{terminals[v][0]}@{terminals[v][1]}" for v in exposed)
    return subdivided, keep, dict(vertices=len(subdivided), edges=len(final_edges),
        max_degree=max(len(f.scope) for f in subdivided), bipartite=True,
        every_edge_has_two_ports=True, all_original_entries_zero_one=True,
        max_copy_fanout=max(map(len, occurrences.values())))


def build(t, B, T, primes):
    J, r, ell = B.bit_length()-1, max(p.bit_length() for p in primes), t.bit_length()
    assert len(primes) == J and all(p > t for p in primes)
    gates = Gates()
    raw = [[f"x{i}_{k}" for k in range(B)] for i in range(t)]
    messages = [[[f"msg{i}_{j}_{k}" for k in range(r)] for j in range(J)] for i in range(t)]
    tails = [f"tail{i}" for i in range(t)]
    history_bits = []
    for j, p in enumerate(primes):
        targets = [f"target{j}_{k}" for k in range(r)]
        stop = f"stop{j}"
        control = {}
        flat_prefix = tuple(v for block in history_bits for v in block)
        for hb in itertools.product((0, 1), repeat=j*ell):
            hs = [number(hb[k*ell:(k+1)*ell]) for k in range(j)]
            st = state(t, B, T, hs)
            if st is None:
                continue
            width, target, stopped, _ = st
            tr = 0 if stopped else (target >> (width//2)) % p
            control[hb + bits(tr, r) + (int(stopped),)] = 1
        gates.factors.append(Factor(f"control{j}", flat_prefix+tuple(targets)+(stop,), control))
        total = messages[0][j]
        for i in range(1, t):
            total = gates.sum_mod(total, messages[i][j], p)
        diff = gates.difference_mod(targets, total, p)
        history_bits.append(gates.branch(diff, t, stop, ell))
    history = tuple(v for block in history_bits for v in block)
    for i in range(t):
        scope = tuple(raw[i]) + history + tuple(v for frame in messages[i] for v in frame) + (tails[i],)
        table = {}
        for x in range(1 << B):
            for hb in itertools.product((0, 1), repeat=J*ell):
                hs = [number(hb[j*ell:(j+1)*ell]) for j in range(J)]
                xi, transmitted, valid = x, [], True
                for j, p in enumerate(primes):
                    st = state(t, B, T, hs[:j])
                    if st is None or hs[j] > t:
                        valid = False
                        break
                    width, _, stopped, _ = st
                    if stopped:
                        if hs[j] != 0:
                            valid = False
                            break
                        transmitted.extend(bits(0, r))
                    else:
                        hi, lo = divmod(xi, 1 << (width//2))
                        transmitted.extend(bits(hi % p, r))
                        xi = lo if hs[j] < t else hi
                final = state(t, B, T, hs) if valid else None
                if final is not None:
                    tail = 0 if final[2] else xi
                    assert tail in (0, 1)
                    table[bits(x, B)+hb+tuple(transmitted)+(tail,)] = 1
        gates.factors.append(Factor(f"party{i}", scope, table))
    final_table = {}
    for hb in itertools.product((0, 1), repeat=J*ell):
        hs = [number(hb[j*ell:(j+1)*ell]) for j in range(J)]
        st = state(t, B, T, hs)
        if st is None:
            continue
        width, target, stopped, answer = st
        for ts in itertools.product((0, 1), repeat=t):
            if stopped and any(ts):
                continue
            value = answer if stopped else int(sum(ts) > target)
            final_table[hb+ts+(value,)] = 1
    gates.factors.append(Factor("final", history+tuple(tails)+("output",), final_table))
    native = dict(boolean_gates=gates.gate_count, boolean_input_ports=gates.input_ports,
                  max_party_degree=max(len(f.scope) for f in gates.factors if f.name.startswith("party")),
                  max_control_degree=max(len(f.scope) for f in gates.factors if f.name.startswith("control")),
                  final_degree=len(history)+t+1, J=J, r=r, ell=ell)
    exposed = tuple(v for group in raw for v in group) + ("output",)
    return (*to_bipartite(gates.factors, exposed), native)


def direct(t, B, T, primes, xs):
    width, target, xs = B, T, list(xs)
    trace = []
    for p in primes:
        if target < 0 or target >= t*((1 << width)-1):
            return int(target < 0), trace+["STOP"]
        half = width//2
        hi, lo = [x >> half for x in xs], [x % (1 << half) for x in xs]
        th, tl = divmod(target, 1 << half)
        h = (th-sum(x % p for x in hi)) % p
        if h < t:
            trace.append("LOW" if sum(hi) == th-h else "FALSE-h")
            xs, target = lo, tl+h*(1 << half)
        else:
            trace.append("HIGH")
            xs, target = hi, th
        width = half
    return int(sum(xs) > target), trace


CASES = {
    "one_round_bad_seed": (2, 2, 0, (3,)),
    "initial_stop": (2, 2, -1, (3,)),
    "two_rounds": (2, 4, 5, (3, 5)),
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("case", choices=CASES)
    args = parser.parse_args()
    started = time.monotonic()
    t, B, T, primes = CASES[args.case]
    factors, keep, graph, native = build(t, B, T, primes)
    _detail_print(json.dumps(dict(stage="built", case=args.case, graph=graph, native=native)), flush=True)
    joint, stats = contract(factors, keep)
    histogram, traces, wrong = Counter(), Counter(), []
    for xs in itertools.product(range(1 << B), repeat=t):
        expected, trace = direct(t, B, T, primes, xs)
        prefix = sum((bits(x, B) for x in xs), ())
        masses = [joint.get(prefix+(y,), 0) for y in (0, 1)]
        assert masses[expected] == 1 and masses[1-expected] == 0, (xs, masses, expected)
        histogram[sum(masses)] += 1
        traces["/".join(trace)] += 1
        if expected != int(sum(xs) > T) and len(wrong) < 4:
            wrong.append(dict(inputs=xs, protocol=expected, exact_comparison=int(sum(xs) > T)))
    result = dict(status="PASS", case=args.case, parameters=dict(t=t, B_prime=B, target=T, primes=primes),
        graph=graph, native=native, input_assignments=(1 << B)**t,
        extension_count_histogram=dict(histogram), output_one_count=sum(v for k, v in joint.items() if k[-1]),
        trace_histogram=dict(traces), allowed_bad_seed_examples=wrong,
        contraction=stats, seconds=time.monotonic()-started,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    dest = Path(__file__).resolve().parent/"results"/f"p11_tensor_{args.case}.json"
    dest.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    _detail_print(json.dumps(result, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()

if __name__ == "__main__":
    _out=_local_Path(__file__).resolve().parent/"results"/(_local_Path(__file__).stem+".details.txt")
    _out.write_text("\n".join(_detail_lines)+"\n")
    _builtins.print(_local_Path(__file__).name+": PASS; details="+_out.name)
