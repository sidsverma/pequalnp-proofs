import argparse
import json
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def adjacent(a, b, k):
    return any(
        (a in (i, k + i) and b in ((i + 1) % k, 2 * k + i))
        or (b in (i, k + i) and a in ((i + 1) % k, 2 * k + i))
        for i in range(k)
    )


def synthesize(k, size, seconds, path=False, fixed=False):
    n = 3 * k + int(path)
    def target(x, y):
        if not path:
            return adjacent(x, y, k)
        return any((x in (i, k + 1 + i) and y in (i + 1, 2 * k + 1 + i))
                   or (y in (i, k + 1 + i) and x in (i + 1, 2 * k + 1 + i))
                   for i in range(k))
    pool = IDPool()
    cnf = CNF()
    selectors = []
    operations = []
    for gate in range(size):
        wires = 2 * n + gate
        a = [pool.id(("a", gate, i)) for i in range(wires)]
        b = [pool.id(("b", gate, i)) for i in range(wires)]
        selectors.append((a, b))
        operations.append(pool.id(("or", gate)))
        for sel in (a, b):
            cnf.extend(CardEnc.equals(sel, 1, vpool=pool, encoding=EncType.seqcounter))
        for i in range(wires):
            for j in range(i):
                cnf.append([-a[i], -b[j]])

    # Every input is essential for these nonconstant adjacency rows/columns.
    # Requiring every intermediate gate to be used removes padded candidates.
    for wire in range(2 * n + size - 1):
        uses = []
        for a, b in selectors:
            if wire < len(a):
                uses.extend([a[wire], b[wire]])
        cnf.append(uses)

    for x in range(n):
        for y in range(n):
            values = [i == x or i == n + y for i in range(2 * n)]
            for gate in range(size):
                ins = [pool.id(("mux", x, y, gate, j)) for j in range(2)]
                out = pool.id(("value", x, y, gate))
                for sel, dest in zip(selectors[gate], ins):
                    for s, val in zip(sel, values):
                        if isinstance(val, bool):
                            cnf.append([-s, dest if val else -dest])
                        else:
                            cnf.append([-s, -val, dest])
                            cnf.append([-s, val, -dest])
                a, b = ins
                op = operations[gate]
                # op selects OR; otherwise AND.
                cnf.extend([[-op, -a, out], [-op, -b, out], [-op, a, b, -out],
                            [op, a, -out], [op, b, -out], [op, -a, -b, out]])
                values.append(out)
            cnf.append([values[-1] if target(x, y) else -values[-1]])

    print(json.dumps(dict(k=k, size=size, variables=pool.top, clauses=len(cnf.clauses))), flush=True)
    started = time.monotonic()
    with Solver(name="g4", bootstrap_with=cnf) as solver:
        baseline = [(i, n + i, True) for i in range(n)]
        outputs = []
        for i in range(k):
            baseline.append((2*n+i, 2*n+k+int(path)+i, True))
            l = 2*n+len(baseline)-1
            baseline.append((2*n+(i+1 if path else (i+1)%k), 2*n+2*k+int(path)+i, True))
            r = 2*n+len(baseline)-1
            baseline.append((l, r, False))
            outputs.append(2*n+len(baseline)-1)
        out = outputs[0]
        for other in outputs[1:]:
            baseline.append((out, other, True))
            out = 2*n+len(baseline)-1
        if len(baseline) == size + 1:
            # Start near a valid construction with one mixed input gate removed.
            replacement = baseline[0][0]
            baseline = baseline[1:]
            baseline = [(replacement if a == 2*n else a-(a>2*n),
                         replacement if b == 2*n else b-(b>2*n), op) for a,b,op in baseline]
        if len(baseline) == size:
            phases = []
            for i, (a,b,op) in enumerate(baseline):
                a,b=sorted((a,b))
                for choices, selected in zip(selectors[i], (a,b)):
                    phases.extend(s if j==selected else -s for j,s in enumerate(choices))
                phases.append(operations[i] if op else -operations[i])
            solver.set_phases(phases)
        timer = threading.Timer(seconds, solver.interrupt)
        timer.start()
        try:
            result = solver.solve_limited(assumptions=phases if fixed else [], expect_interrupt=True)
        finally:
            timer.cancel()
        print(json.dumps(dict(result=result, elapsed=time.monotonic() - started, stats=solver.accum_stats())), flush=True)
        if result:
            model = set(solver.get_model())
            gates = [dict(op="or" if operations[i] in model else "and",
                          inputs=[next(j for j, s in enumerate(sel) if s in model) for sel in selectors[i]])
                     for i in range(size)]
            # Independently evaluate the extracted witness on every promised input.
            for x in range(n):
                for y in range(n):
                    vals = [i == x or i == n + y for i in range(2 * n)]
                    for g in gates:
                        a, b = [vals[j] for j in g["inputs"]]
                        vals.append((a or b) if g["op"] == "or" else (a and b))
                    assert vals[-1] == target(x, y)
            output_path = Path(f"{'path' if path else 'cycle'}-k{k}-s{size}.json")
            output_path.write_text(json.dumps(dict(k=k, size=size, gates=gates), indent=2))
            print(f"witness independently verified: {output_path}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("k", type=int)
    parser.add_argument("size", type=int)
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--path", action="store_true")
    parser.add_argument("--fixed", action="store_true")
    args = parser.parse_args()
    synthesize(args.k, args.size, args.seconds, args.path, args.fixed)
