"""Functional fan-in-two circuits and parsimonious Tseitin 3-CNF.

No solver dependency.  All arithmetic is expanded into Boolean gates.
Run experiments with nice -n 19 and an external <=300 second timeout.
"""
from collections import defaultdict
from itertools import product


class Circuit:
    def __init__(self):
        self.nvars = 0
        self.primary = []
        self.gates = []
        self.clauses = []
        self.names = {}
        self.zero = self.new_var("constant_zero")
        self.clauses.append((-self.zero,))
        self.one = -self.zero
        self.stats = {}

    def new_var(self, name=None, primary=False):
        self.nvars += 1
        if name is not None:
            self.names[name] = self.nvars
        if primary:
            self.primary.append(self.nvars)
        return self.nvars

    def fix(self, bit, value):
        self.clauses.append((bit if value else -bit,))

    def gate(self, op, a, b):
        # Constant simplifications preserve a unique functional extension.
        if op == "and":
            if a == self.zero or b == self.zero:
                return self.zero
            if a == self.one:
                return b
            if b == self.one or a == b:
                return a
            if a == -b:
                return self.zero
        if op == "or":
            if a == self.one or b == self.one:
                return self.one
            if a == self.zero:
                return b
            if b == self.zero or a == b:
                return a
            if a == -b:
                return self.one
        if op == "xor":
            if a == self.zero:
                return b
            if b == self.zero:
                return a
            if a == self.one:
                return -b
            if b == self.one:
                return -a
            if a == b:
                return self.zero
            if a == -b:
                return self.one
        out = self.new_var()
        self.gates.append((op, a, b, out))
        if op == "and":
            self.clauses.extend([(-a, -b, out), (a, -out), (b, -out)])
        elif op == "or":
            self.clauses.extend([(a, b, -out), (-a, out), (-b, out)])
        elif op == "xor":
            self.clauses.extend([
                (a, b, -out), (a, -b, out),
                (-a, b, out), (-a, -b, -out)])
        else:
            raise ValueError(op)
        return out

    def full_adder(self, a, b, c):
        t = self.gate("xor", a, b)
        s = self.gate("xor", t, c)
        carry = self.gate("or", self.gate("and", a, b),
                          self.gate("and", t, c))
        return s, carry

    def add(self, left, right, width):
        carry = self.zero
        out = []
        for i in range(width):
            a = left[i] if i < len(left) else self.zero
            b = right[i] if i < len(right) else self.zero
            s, carry = self.full_adder(a, b, carry)
            out.append(s)
        # All callers prove integer bounds that make this carry zero.
        # It remains a functional gate output even if it is not constrained.
        return out

    def popcount(self, bits):
        if not bits:
            return [self.zero]
        columns = defaultdict(list)
        columns[0] = list(bits)
        i = 0
        while i <= max(columns):
            while len(columns[i]) >= 3:
                a, b, c = (columns[i].pop() for _ in range(3))
                s, carry = self.full_adder(a, b, c)
                columns[i].append(s)
                columns[i + 1].append(carry)
            i += 1
        width = max(1, len(bits).bit_length())
        row1 = [columns[j][0] if columns[j] else self.zero
                for j in range(width)]
        row2 = [columns[j][1] if len(columns[j]) > 1 else self.zero
                for j in range(width)]
        return self.add(row1, row2, width)

    def multiply_constant(self, bits, coefficient):
        width = max(1, (coefficient * ((1 << len(bits)) - 1)).bit_length())
        accum = [self.zero] * width
        for shift in range(coefficient.bit_length()):
            if coefficient >> shift & 1:
                accum = self.add(accum, [self.zero] * shift + list(bits), width)
        return accum

    def weighted_sum(self, bits, weights, digit_bits=None):
        if len(bits) != len(weights) or any(w < 0 for w in weights):
            raise ValueError("invalid weighted sum")
        scale = len(bits) + 2
        if digit_bits is None:
            digit_bits = max(1, (scale.bit_length() - 1) // 4)
        if digit_bits < 1:
            raise ValueError("digit_bits must be positive")
        base = 1 << digit_bits
        weight_bits = max(weights, default=0).bit_length()
        digits = (weight_bits + digit_bits - 1) // digit_bits
        width = max(1, sum(weights).bit_length())
        terms_by_digit = []
        bucket_count = 0
        start = len(self.gates)
        for j in range(digits):
            buckets = defaultdict(list)
            for bit, weight in zip(bits, weights):
                digit = (weight >> (j * digit_bits)) & (base - 1)
                if digit:
                    buckets[digit].append(bit)
            bucket_count += len(buckets)
            terms = []
            for digit, bucket in sorted(buckets.items()):
                count = self.popcount(bucket)
                term = self.multiply_constant(count, digit)
                terms.append(term)
            terms_by_digit.append(terms)
        # Short digit subtotals followed by a carry scan.  In particular,
        # long coefficients do not trigger a full-width adder per bucket.
        q = max(1, len(bits).bit_length())
        digit_width = q + digit_bits + 1
        carry = [self.zero]
        accum = []
        for terms in terms_by_digit:
            subtotal = [self.zero] * digit_width
            for term in terms:
                subtotal = self.add(subtotal, term, digit_width)
            total = self.add(subtotal, carry, digit_width)
            accum.extend(total[:digit_bits])
            carry = total[digit_bits:]
        accum.extend(carry)
        accum = (accum + [self.zero] * width)[:width]
        self.stats.setdefault("weighted_sums", []).append({
            "inputs": len(bits), "weight_bits": weight_bits,
            "digit_bits": digit_bits, "digits": digits,
            "buckets": bucket_count, "gates": len(self.gates) - start,
            "width": width})
        return accum

    def weighted_sum_whole_word(self, bits, weights, digit_bits=None):
        """Full-word addition implementation for comparison with the digit-carry circuit."""
        if len(bits) != len(weights) or any(w < 0 for w in weights):
            raise ValueError("invalid weighted sum")
        scale = len(bits) + 2
        if digit_bits is None:
            digit_bits = max(1, (scale.bit_length() - 1) // 4)
        base = 1 << digit_bits
        weight_bits = max(weights, default=0).bit_length()
        digits = (weight_bits + digit_bits - 1) // digit_bits
        width = max(1, sum(weights).bit_length())
        terms = []
        bucket_count = 0
        start = len(self.gates)
        for j in range(digits):
            buckets = defaultdict(list)
            for bit, weight in zip(bits, weights):
                digit = (weight >> (j * digit_bits)) & (base - 1)
                if digit:
                    buckets[digit].append(bit)
            bucket_count += len(buckets)
            for digit, bucket in sorted(buckets.items()):
                count = self.popcount(bucket)
                term = self.multiply_constant(count, digit)
                terms.append([self.zero] * (j * digit_bits) + term)
        accum = [self.zero] * width
        for term in terms:
            accum = self.add(accum, term, width)
        self.stats.setdefault("weighted_sums", []).append({
            "inputs": len(bits), "weight_bits": weight_bits,
            "digit_bits": digit_bits, "digits": digits,
            "buckets": bucket_count, "gates": len(self.gates) - start,
            "width": width})
        return accum

    def equal_constant(self, bits, target):
        if target < 0 or target >= (1 << len(bits)):
            self.clauses.append(())
            return
        for i, bit in enumerate(bits):
            self.fix(bit, target >> i & 1)

    def less_equal_constant(self, bits, target):
        if target < 0:
            self.clauses.append(())
            return
        if target >= (1 << len(bits)) - 1:
            return
        equal, less = self.one, self.zero
        for i in reversed(range(len(bits))):
            bit = bits[i]
            if target >> i & 1:
                less = self.gate("or", less, self.gate("and", equal, -bit))
                equal = self.gate("and", equal, bit)
            else:
                equal = self.gate("and", equal, -bit)
        self.fix(self.gate("or", equal, less), 1)

    def evaluate(self, primary_values):
        values = [False] * (self.nvars + 1)
        if len(primary_values) != len(self.primary):
            raise ValueError("one bit per primary input is required")
        for var, val in zip(self.primary, primary_values):
            values[var] = bool(val)
        def val(lit):
            return values[abs(lit)] if lit > 0 else not values[-lit]
        for op, a, b, out in self.gates:
            av, bv = val(a), val(b)
            values[out] = (av and bv) if op == "and" else (
                (av or bv) if op == "or" else (av != bv))
        return values

    def satisfies(self, values):
        return all(any(values[abs(l)] == (l > 0) for l in clause)
                   for clause in self.clauses)

    def value_of(self, bits, values):
        return sum((values[abs(b)] == (b > 0)) << i for i, b in enumerate(bits))

    def count_primary(self):
        # Counts all primary assignments, then checks the actual CNF clauses
        # on their unique circuit extension.  No graph-specific inference.
        return sum(self.satisfies(self.evaluate(v))
                   for v in product((False, True), repeat=len(self.primary)))

    def dimacs(self, path):
        with open(path, "w") as f:
            f.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")


def cut_count_cnf(n, edges, weights=None, target=None, endpoints=None,
                  costs=None, cost_limit=None, required=(), forbidden=(),
                  digit_bits=None, directed=False):
    c = Circuit()
    selected = [c.new_var(f"edge_{i}", primary=True) for i in range(len(edges))]
    colours = [c.new_var(f"colour_{v}", primary=True) for v in range(n)]
    c.fix(colours[0], 0)
    incident = [[] for _ in range(n)]
    for (u, v), x in zip(edges, selected):
        incident[u].append(x)
        incident[v].append(x)
        c.clauses.extend([(-x, -colours[u], colours[v]),
                          (-x, colours[u], -colours[v])])
    if directed:
        incoming = [[] for _ in range(n)]
        outgoing = [[] for _ in range(n)]
        for (u, v), x in zip(edges, selected):
            incoming[v].append(x)
            outgoing[u].append(x)
        for v in range(n):
            c.equal_constant(c.popcount(incoming[v]),
                             0 if endpoints is not None and v == endpoints[0] else 1)
            c.equal_constant(c.popcount(outgoing[v]),
                             0 if endpoints is not None and v == endpoints[1] else 1)
    else:
        for v in range(n):
            degree = c.popcount(incident[v])
            wanted = 1 if endpoints is not None and v in endpoints else 2
            c.equal_constant(degree, wanted)
    for e in required:
        c.fix(selected[e], 1)
    for e in forbidden:
        c.fix(selected[e], 0)
    outputs = None
    if weights is not None:
        outputs = c.weighted_sum(selected, weights, digit_bits)
        if target is not None:
            c.equal_constant(outputs, target)
    if costs is not None:
        out_cost = c.weighted_sum(selected, costs, digit_bits)
        c.less_equal_constant(out_cost, cost_limit)
    c.stats.update({"n": n, "m": len(edges), "N": c.nvars,
                    "M": len(c.clauses), "k": max(map(len, c.clauses), default=0)})
    return c, outputs


def xor_all(c, bits):
    value = c.zero
    for bit in bits:
        value = c.gate("xor", value, bit)
    return value


def inversion_parity(c, nrows, positions, selected):
    """O(M log n) gates; endpoint orders are fixed construction data.

    Computes the XOR of z_ij*z_i'j' over i<i' and j>j', even on
    non-permutation subsets. Sorting of known column constants is not
    a run-time Boolean operation.
    """
    entries = [(i, j, z) for (i, j), z in zip(positions, selected)]
    def recurse(lo, hi, es):
        if hi - lo <= 1 or not es:
            return c.zero
        mid = (lo + hi) // 2
        left = [e for e in es if e[0] < mid]
        right = [e for e in es if e[0] >= mid]
        by_col = defaultdict(lambda: [[], []])
        for i, j, z in es:
            by_col[j][int(i >= mid)].append(z)
        prefix_right = c.zero
        cross = []
        for j, (ls, rs) in sorted(by_col.items()):
            # Update right prefix after this column: inversions are strict.
            cross.append(c.gate("and", xor_all(c, ls), prefix_right))
            prefix_right = c.gate("xor", prefix_right, xor_all(c, rs))
        return xor_all(c, [xor_all(c, cross), recurse(lo, mid, left),
                           recurse(mid, hi, right)])
    return recurse(0, nrows, entries)


def determinant_hc_cnf(n, edges, sign_target=None, with_sign=True):
    """Signed #3CNF difference = det-filtered count = n * #HC.

    Primary multiplicity bits realize diagonal entries 2 (or 3 at root).
    Off-diagonal entries are -x_e.  No arithmetic determinant primitive.
    """
    c = Circuit()
    x = [c.new_var(f"edge_{i}", primary=True) for i in range(len(edges))]
    incident = [[] for _ in range(n)]
    for (u, v), bit in zip(edges, x):
        incident[u].append(bit)
        incident[v].append(bit)
    for bits in incident:
        c.equal_constant(c.popcount(bits), 2)
    positions = [(v, v) for v in range(n)]
    supported_by = [None] * n
    for e, (u, v) in enumerate(edges):
        positions.extend([(u, v), (v, u)])
        supported_by.extend([e, e])
    z = [c.new_var(f"position_{i}_{j}", primary=True) for i, j in positions]
    row = [[] for _ in range(n)]
    col = [[] for _ in range(n)]
    off_diagonal = []
    for (i, j), bit, edge in zip(positions, z, supported_by):
        row[i].append(bit)
        col[j].append(bit)
        if i != j:
            c.clauses.append((-bit, x[edge]))
            off_diagonal.append(bit)
    for bits in row + col:
        c.equal_constant(c.popcount(bits), 1)
    for v in range(n):
        a = c.new_var(f"multiplicity_{v}_a", primary=True)
        c.clauses.append((-a, z[v]))
        if v == 0:
            b = c.new_var(f"multiplicity_{v}_b", primary=True)
            c.clauses.extend([(-b, z[v]), (-a, -b)])
    parity = None
    c.stats["inversion_gates"] = 0
    if with_sign:
        before_sign = len(c.gates)
        parity = inversion_parity(c, n, positions, z)
        c.stats["inversion_gates"] = len(c.gates) - before_sign
        parity = c.gate("xor", parity, xor_all(c, off_diagonal))
        if sign_target is not None:
            c.fix(parity, sign_target)
    elif sign_target is not None:
        raise ValueError("unsigned circuit has no sign output")
    c.stats.update({"n": n, "m": len(edges), "N": c.nvars,
                    "M": len(c.clauses), "k": max(map(len, c.clauses), default=0)})
    return c, parity


def colour_cut_cnf(n, edges, bits_per_colour, colour_count=None):
    c = Circuit()
    x = [c.new_var(f"edge_{i}", primary=True) for i in range(len(edges))]
    colours = [[c.new_var(f"colour_{v}_{j}", primary=True)
                for j in range(bits_per_colour)] for v in range(n)]
    if colour_count is not None:
        assert 1 <= colour_count <= 1 << bits_per_colour
        for word in colours:
            c.less_equal_constant(word, colour_count - 1)
    for bit in colours[0]:
        c.fix(bit, 0)
    incident = [[] for _ in range(n)]
    for (u, v), bit in zip(edges, x):
        incident[u].append(bit)
        incident[v].append(bit)
        for a, b in zip(colours[u], colours[v]):
            c.clauses.extend([(-bit, -a, b), (-bit, a, -b)])
    for es in incident:
        c.equal_constant(c.popcount(es), 2)
    return c


def rank_hc_cnf(n, edges, directed=False):
    """Exact rank/position #3CNF; one assignment per Hamilton cycle.

    Undirected cycles choose the orientation whose outgoing root neighbor
    is smaller than its incoming root neighbor.  All labels are forced
    uniquely on a cycle; other cycles are impossible by strict increment.
    """
    c = Circuit()
    arcs = list(edges) if directed else [a for u, v in edges for a in ((u, v), (v, u))]
    x = [c.new_var(f"arc_{u}_{v}", primary=True) for u, v in arcs]
    incoming = [[] for _ in range(n)]
    outgoing = [[] for _ in range(n)]
    for (u, v), bit in zip(arcs, x):
        outgoing[u].append(bit)
        incoming[v].append(bit)
    for bits in incoming + outgoing:
        c.equal_constant(c.popcount(bits), 1)
    width = max(1, (n - 1).bit_length())
    ranks = [[c.new_var(f"rank_{v}_{i}", primary=True) for i in range(width)]
             for v in range(n)]
    c.equal_constant(ranks[0], 0)
    increments = [c.add(word + [c.zero], [c.one], width + 1) for word in ranks]
    for (u, v), bit in zip(arcs, x):
        if v == 0:
            for i, rank_bit in enumerate(ranks[u]):
                c.clauses.append((-bit, rank_bit if (n - 1) >> i & 1 else -rank_bit))
        else:
            c.clauses.append((-bit, -increments[u][-1]))
            for a, b in zip(ranks[v], increments[u]):
                c.clauses.extend([(-bit, -a, b), (-bit, a, -b)])
    if not directed:
        root_in = {u: bit for (u, v), bit in zip(arcs, x) if v == 0}
        root_out = {v: bit for (u, v), bit in zip(arcs, x) if u == 0}
        greater = c.zero
        for v in reversed(sorted(root_in)):
            c.clauses.append((-root_out[v], greater))
            greater = c.gate("or", greater, root_in[v])
    c.stats.update({"n": n, "m": len(edges), "N": c.nvars,
                    "M": len(c.clauses), "k": max(map(len, c.clauses), default=0),
                    "rank_bits_per_vertex": width})
    return c


def connected_object_cnf(n, edges, mode, terminals=None, root=0):
    """Linear parity certificates for Steiner, CVC, CDS and marked FVS."""
    c = Circuit()
    u = [c.new_var(f"vertex_{v}", primary=True) for v in range(n)]
    colours = [c.new_var(f"colour_{v}", primary=True) for v in range(n)]
    if mode == "steiner":
        x = [c.new_var(f"edge_{i}", primary=True) for i in range(len(edges))]
        for (v, w), bit in zip(edges, x):
            c.clauses.extend([(-bit, u[v]), (-bit, u[w])])
        for v in (terminals or (root,)):
            c.fix(u[v], 1)
    else:
        x = [c.gate("and", u[v], u[w]) for v, w in edges]
    for (v, w), bit in zip(edges, x):
        c.clauses.extend([(-bit, -colours[v], colours[w]),
                          (-bit, colours[v], -colours[w])])
    for v in range(n):
        c.clauses.append((u[v], -colours[v]))
    if mode == "cover":
        for v, w in edges:
            c.clauses.append((u[v], u[w]))
    elif mode == "dominating":
        neighbours = [{v} for v in range(n)]
        for v, w in edges:
            neighbours[v].add(w)
            neighbours[w].add(v)
        for ns in neighbours:
            value = c.zero
            for v in sorted(ns):
                value = c.gate("or", value, u[v])
            c.fix(value, 1)
    elif mode not in ("steiner", "fvs"):
        raise ValueError(mode)
    if mode == "fvs":
        markers = [c.new_var(f"marker_{v}", primary=True) for v in range(n)]
        for v in range(n):
            c.clauses.extend([(-markers[v], u[v]), (-markers[v], -colours[v])])
        left = c.popcount(x + markers)
        right = c.popcount(u)
    else:
        c.fix(u[root], 1)
        c.fix(colours[root], 0)
        if mode == "steiner":
            left = c.popcount(x + [c.one])
            right = c.popcount(u)
        else:
            left = right = []
    if left or right:
        for i in range(max(len(left), len(right))):
            a = left[i] if i < len(left) else c.zero
            b = right[i] if i < len(right) else c.zero
            c.clauses.extend([(-a, b), (a, -b)])
    return c


def count_dimacs_dpll(nvars, clauses):
    """Independent literal-level #DPLL, including declared unused variables.

    Unit propagation and free-variable factoring only.  Does not use a
    Circuit object, functional states, graph structure, or expected counts.
    """
    def visit(current, unassigned):
        while True:
            if any(not clause for clause in current):
                return 0
            units = {clause[0] for clause in current if len(clause) == 1}
            if any(-lit in units for lit in units):
                return 0
            if not units:
                break
            unassigned = unassigned - {abs(lit) for lit in units}
            current = [tuple(lit for lit in clause if -lit not in units)
                       for clause in current if not any(lit in units for lit in clause)]
        occurring = {abs(lit) for clause in current for lit in clause}
        free = len(unassigned - occurring)
        if not current:
            return 1 << len(unassigned)
        clause = min(current, key=len)
        var = abs(clause[0])
        rest = unassigned & occurring
        return (1 << free) * (visit(current + [(var,)], rest)
                              + visit(current + [(-var,)], rest))
    return visit([tuple(c) for c in clauses], set(range(1, nvars + 1)))
