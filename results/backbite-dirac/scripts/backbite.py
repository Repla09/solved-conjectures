"""Test: is the backbite reconfiguration graph R(G) connected when min degree >= n/2?

Conjecture (Kazazi, arXiv 2610.05068): delta(G) >= n/2 implies R(G) connected.
Reads graph6 lines on stdin (e.g. from `geng -c -d<d> n`), prints any counterexample.

A Hamiltonian path is unoriented (a path and its reverse are the same).
Backbite at endpoint v1 of v1..vn: pick a G-neighbour vi of v1 with i >= 3,
add v1 vi and delete v(i-1) vi, giving v(i-1) ... v1 vi ... vn.
"""
import sys


def parse_g6(line):
    data = [ord(c) - 63 for c in line.strip()]
    n = data[0]
    bits = []
    for d in data[1:]:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    adj = [0] * n
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            idx += 1
    return n, adj


def ham_paths(n, adj):
    out = []
    full = (1 << n) - 1

    def ext(path, used):
        if used == full:
            t = tuple(path)
            if t[0] < t[-1]:
                out.append(t)
            return
        last = path[-1]
        cand = adj[last] & ~used
        while cand:
            b = cand & -cand
            v = b.bit_length() - 1
            path.append(v)
            ext(path, used | b)
            path.pop()
            cand ^= b

    for s in range(n):
        ext([s], 1 << s)
    return out


def norm(p):
    return p if p[0] < p[-1] else p[::-1]


def neighbours(p, adj):
    n = len(p)
    res = []
    for q in (p, p[::-1]):
        v1 = q[0]
        for i in range(2, n):
            if adj[v1] >> q[i] & 1:
                new = q[i - 1::-1] + q[i:]
                res.append(norm(new))
    return res


def connected(n, adj):
    paths = ham_paths(n, adj)
    if not paths:
        return True, 0, 0
    seen = {paths[0]}
    stack = [paths[0]]
    while stack:
        p = stack.pop()
        for q in neighbours(p, adj):
            if q not in seen:
                seen.add(q)
                stack.append(q)
    return len(seen) == len(paths), len(paths), len(seen)


def main():
    tested = bad = 0
    for line in sys.stdin:
        if not line.strip():
            continue
        n, adj = parse_g6(line)
        ok, total, reach = connected(n, adj)
        tested += 1
        if not ok:
            bad += 1
            print(f"COUNTEREXAMPLE {line.strip()} n={n}: {reach}/{total} paths reachable", flush=True)
    print(f"tested {tested} graphs, counterexamples {bad}", flush=True)


if __name__ == "__main__":
    main()
